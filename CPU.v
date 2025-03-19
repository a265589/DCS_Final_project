//==============================================//
//           Top CPU Module Declaration         //
//==============================================//
module CPU(
	// Input Ports
    clk,
    rst_n,
    data_read,
    instruction,
    // Output Ports
    data_wen,
    data_addr,
    inst_addr,
    data_write
    );
					
	input clk;
	input rst_n;
	input [31:0] instruction;
	input [31:0] data_read;
	output  data_wen;
	output  [31:0] data_addr;
	output  [31:0] inst_addr;
	output  [31:0] data_write;

    //You can modify the below code
    wire stall;
    // IF stage 
    reg [31:0] PC_Fhl;
    wire [31:0] PC_plus_1_Fhl;
    wire [31:0] instruction_Fhl;
    wire squash_IF;
    wire stall_IF;

    wire branch_prediction_Fhl;
    wire  signed [31:0] branch_target_Fhl;

    // ID stage
    reg [31:0] PC_Dhl;
    reg [31:0] instruction_Dhl;
    reg signed [31:0] PC_plus_1_Dhl;
    reg [31:0] reg_file [0:31];
    

    wire RegDst_Dhl, jump_Dhl, Branch_Dhl, MemtoReg_Dhl, MemWrite_Dhl, MemRead_Dhl, ALUSrc_Dhl, RegWrite_Dhl;
    wire [1:0]ALUOp_Dhl;
    wire  [4:0] rs_Dhl, rt_Dhl, rd_Dhl;
    wire  [5:0] opcode_Dhl;
    wire  [5:0] funct_Dhl; 
    wire  [15:0] immediate_Dhl;
    wire  signed [31:0] immediate_sign_extended_Dhl;
    wire  signed [31:0] branch_target_Dhl;
    wire  [31:0] jump_target_Dhl;
    wire squash_ID;
    reg branch_prediction_Dhl;
   
    // EX stage 
    reg [31:0] PC_Xhl;
    reg [31:0] reg_data_1_Xhl, reg_data_2_Xhl;
    reg signed [31:0]  immediate_sign_extended_Xhl;
    wire [31:0] operand_1_Xhl, operand_2_Xhl;
    wire [1:0] forward_A, forward_B;
    reg  [4:0] rs_Xhl, rt_Xhl, rd_Xhl;
    reg [1:0]ALUOp_Xhl;
    reg RegDst_Xhl, Branch_Xhl, MemtoReg_Xhl, MemWrite_Xhl, MemRead_Xhl, ALUSrc_Xhl, RegWrite_Xhl;
    wire [31:0]ALU_result_Xhl;
    wire Zero_Xhl;
    wire branch_taken_Xhl;
    reg [31:0]  branch_mispredict_target_Xhl;
    wire branch_mispredict_Xhl;
    reg branch_prediction_Xhl;
    reg[31:0] branch_target_Xhl;

    // MEM stage

    reg  MemtoReg_Mhl, RegWrite_Mhl, MemWrite_Mhl;
    reg [31:0] reg_data_2_Mhl;
    reg [31:0] ALU_result_Mhl;
    reg  [4:0] rd_Mhl;

    
    // WB stage
    reg RegDst_Whl, MemtoReg_Whl, RegWrite_Whl;
    reg [31:0] ALU_result_Whl;
    reg [31:0] data_read_Whl;
    wire[4:0] write_reg_Whl; 
    wire [31:0] data_Whl;
    reg  [4:0] rd_Whl;

 



    //control unit

    CONTROL ctrl(.opcode(opcode_Dhl), .funct(funct_Dhl), .RegDst(RegDst_Dhl), .jump(jump_Dhl), .Branch(Branch_Dhl), .MemtoReg(MemtoReg_Dhl), .ALUOp(ALUOp_Dhl), .MemWrite(MemWrite_Dhl), .MemRead(MemRead_Dhl), .ALUSrc(ALUSrc_Dhl), .RegWrite(RegWrite_Dhl) );
    Forward_Unit forward_u (.rs_Xhl(rs_Xhl), .rt_Xhl(rt_Xhl), .rd_Mhl(rd_Mhl), .rd_Whl(rd_Whl), .RegWrite_Mhl(RegWrite_Mhl), .RegWrite_Whl(RegWrite_Whl), .forward_A(forward_A), .forward_B(forward_B) );
    Hazard_Detection hz_dectect( .MemRead_Xhl(MemRead_Xhl), .rt_Xhl(rt_Xhl), .rs_Dhl(rs_Dhl), .rt_Dhl(rt_Dhl), .stall(stall));
    Branch_Target_Buffer btb( .clk(clk), .rst_n(rst_n), .PC(PC_Fhl), .add((!branch_prediction_Xhl) && branch_mispredict_Xhl ),  .remove(branch_prediction_Xhl && branch_mispredict_Xhl ), .tag(PC_Xhl), .target(branch_target_Xhl), .hit(branch_prediction_Fhl), .hit_target(branch_target_Fhl));
    // Branch_Predictor br_predict(.clk(clk), .rst_n(rst_n), .branch_result(branch_taken_Xhl), .is_update_predictor(Branch_Xhl), .branch_prediction(branch_prediction_Dhl));

    wire [31:0] PC_Phl;
    assign PC_Phl = (branch_mispredict_Xhl)? branch_mispredict_target_Xhl : (jump_Dhl)? jump_target_Dhl : (branch_prediction_Fhl)? branch_target_Fhl : PC_plus_1_Fhl;

    // IF stage

    always @(posedge clk or negedge rst_n) begin
        if(!rst_n)
        begin
            PC_Fhl <= 32'd0;
        end
        else if (!stall_IF)
        begin
            PC_Fhl <= PC_Phl;
        end
    end

    assign  inst_addr = PC_Fhl;

    assign instruction_Fhl = instruction;
    assign PC_plus_1_Fhl = PC_Fhl + 32'd1;
    assign stall_IF = stall;


    //IF ----> ID

    always @(posedge clk or negedge rst_n) begin
        if(!rst_n)
        begin
            instruction_Dhl <= 0;
            PC_plus_1_Dhl <=  0;
            branch_prediction_Dhl <= 0;
        end
        else
        begin
            if(squash_IF)
            begin
                instruction_Dhl <= 0;
                PC_plus_1_Dhl <=  0;
                branch_prediction_Dhl <= 0;
                PC_Dhl <= 0;
            end
            else if(!stall_IF)
            begin
                instruction_Dhl <= instruction_Fhl;
                PC_plus_1_Dhl <=  PC_plus_1_Fhl;
                branch_prediction_Dhl <=  branch_prediction_Fhl ;
                PC_Dhl <= PC_Fhl;
            end
            // else
            // begin
            //     instruction_Dhl <= instruction_Dhl;
            //     PC_plus_1_Dhl <= PC_plus_1_Dhl;
            //     branch_prediction_Dhl <=  branch_prediction_Dhl;
            //     // PC_Dhl <= PC_Dhl;
            // end
        end
    end
    
    assign squash_IF =  jump_Dhl | branch_mispredict_Xhl ;
    // ID stage

    assign opcode_Dhl = instruction_Dhl[31:26];
    assign funct_Dhl =  instruction_Dhl[5:0];
    assign rs_Dhl = instruction_Dhl[25:21];
    assign rt_Dhl = instruction_Dhl[20:16];
    assign rd_Dhl = instruction_Dhl[15:11];

    assign immediate_Dhl = instruction_Dhl[15:0];
    assign immediate_sign_extended_Dhl = { {16{immediate_Dhl[15]}}, immediate_Dhl};
    assign branch_target_Dhl = immediate_sign_extended_Dhl + PC_plus_1_Dhl;
    // assign branch_prediction_taken_Dhl = branch_prediction_Dhl & Branch_Dhl;
    assign jump_target_Dhl = { PC_plus_1_Dhl[31:28], 2'b00 , instruction_Dhl[25:0] };

    //ID ----> EX
       always @(posedge clk or negedge rst_n) begin
        if(!rst_n)
        begin
            RegDst_Xhl <= 0;
            Branch_Xhl <= 0;
            MemtoReg_Xhl <= 0;
            MemWrite_Xhl <= 0;
            MemRead_Xhl <= 0;
            ALUSrc_Xhl <= 0;
            ALUOp_Xhl <= 0;
            RegWrite_Xhl <= 0;
            branch_mispredict_target_Xhl <= 0;
            branch_target_Xhl <= 0;
            branch_prediction_Xhl <= 0; 
            rs_Xhl <= 0;
            rt_Xhl <= 0;
            rd_Xhl <= 0;
            reg_data_1_Xhl <= 0;
            reg_data_2_Xhl <= 0;
            immediate_sign_extended_Xhl <= 0;
            PC_Xhl <= 0;
        end
        else
        begin
            if(squash_ID)
            begin
                RegDst_Xhl <= 0;
                Branch_Xhl <= 0;
                MemtoReg_Xhl <= 0;
                MemWrite_Xhl <= 0;
                MemRead_Xhl <= 0;
                ALUSrc_Xhl <= 0;
                ALUOp_Xhl <= 0;
                RegWrite_Xhl <= 0;
                branch_mispredict_target_Xhl  <= 0; 
                branch_target_Xhl <= 0;
                branch_prediction_Xhl <= 0;
                rs_Xhl <= 0;
                rt_Xhl <= 0;
                rd_Xhl <= 0;
                reg_data_1_Xhl <= 0;
                reg_data_2_Xhl <= 0;
                immediate_sign_extended_Xhl <= 0;
                PC_Xhl <= 0;
            end
            else 
            begin
                RegDst_Xhl <= RegDst_Dhl;
                Branch_Xhl <= Branch_Dhl;
                MemtoReg_Xhl <= MemtoReg_Dhl;
                MemWrite_Xhl <= MemWrite_Dhl;
                MemRead_Xhl <= MemRead_Dhl;
                ALUSrc_Xhl <= ALUSrc_Dhl;
                ALUOp_Xhl <= ALUOp_Dhl;
                RegWrite_Xhl <= RegWrite_Dhl;
                branch_mispredict_target_Xhl  <= (branch_prediction_Dhl)? PC_plus_1_Dhl : branch_target_Dhl; 
                branch_target_Xhl <= branch_target_Dhl;
                branch_prediction_Xhl <= branch_prediction_Dhl;
                rs_Xhl <= rs_Dhl;
                rt_Xhl <= rt_Dhl;
                rd_Xhl <= rd_Dhl;
                reg_data_1_Xhl <= reg_file[rs_Dhl];
                reg_data_2_Xhl <= reg_file[rt_Dhl];
                immediate_sign_extended_Xhl <= immediate_sign_extended_Dhl;
                PC_Xhl <= PC_Dhl;
            end

        end
      end 

    assign squash_ID =  branch_mispredict_Xhl | stall;
    // Ex stage
    assign operand_1_Xhl = (forward_A == 'b10)? ALU_result_Mhl : (forward_A == 'b01)?  data_Whl : reg_data_1_Xhl;


    assign  operand_2_Xhl = (ALUSrc_Xhl == 'b1)? immediate_sign_extended_Xhl : (forward_B == 'b10)? ALU_result_Mhl : (forward_B == 'b01)?  data_Whl : reg_data_2_Xhl; 
    ALU a (.ALUOp(ALUOp_Xhl), .operand_1(operand_1_Xhl), .operand_2(operand_2_Xhl), .ALU_result(ALU_result_Xhl), .Zero(Zero_Xhl));
    assign branch_taken_Xhl = Branch_Xhl & Zero_Xhl;
    assign branch_mispredict_Xhl =  Branch_Xhl && (branch_taken_Xhl != branch_prediction_Xhl); 

    //EX ----> MEM
       always @(posedge clk or negedge rst_n) begin
        if(!rst_n)
        begin
            ALU_result_Mhl <= 0;
            reg_data_2_Mhl <= 0;
            rd_Mhl <= 0;
            MemWrite_Mhl <= 0;
            MemtoReg_Mhl <= 0;
        end
        else
        begin
            ALU_result_Mhl <= ALU_result_Xhl;
            reg_data_2_Mhl <= reg_data_2_Xhl;
            rd_Mhl <=  (RegDst_Xhl == 'b0)? rt_Xhl : rd_Xhl;
            MemWrite_Mhl <= MemWrite_Xhl;
            MemtoReg_Mhl <= MemtoReg_Xhl;
            RegWrite_Mhl <= RegWrite_Xhl;
        end
      end 

    //  MEM stage
    assign data_addr =  ALU_result_Mhl;
    assign data_write = reg_data_2_Mhl;
    assign data_wen = (MemWrite_Mhl == 'b1)? 'b1 : 'b0;

      //MEM -----> WB
       always @(posedge clk or negedge rst_n) begin
        if(!rst_n)
        begin
            ALU_result_Whl <= 0;
            rd_Whl <= 0;
            MemtoReg_Whl <= 0;
            RegWrite_Whl <= 0;
            data_read_Whl <=  0;
            // PC_Whl <= 0;
        end
        else
        begin
            ALU_result_Whl <= ALU_result_Mhl;
            rd_Whl <= rd_Mhl;
            MemtoReg_Whl <= MemtoReg_Mhl;
            RegWrite_Whl <= RegWrite_Mhl;
            data_read_Whl <=  data_read;
            // PC_Whl <= PC_Mhl;
        end
      end   

    //  WB stage

    assign data_Whl = (MemtoReg_Whl == 'b0)? ALU_result_Whl : data_read_Whl;
    integer i = 0;
    always @(negedge clk or negedge rst_n) begin
        if(!rst_n)
        begin
            for(i = 0; i<31; i=i+1)
                reg_file[i] <= 0;
        end
        else
        begin
            if(RegWrite_Whl)
                reg_file[rd_Whl] <= data_Whl;
            else 
                reg_file[rd_Whl] <= reg_file[rd_Whl];
        end
    end




endmodule


module CONTROL(
    input [5:0] opcode,
    input [5:0] funct,
    output reg RegDst,
    output reg jump,
    output reg Branch,
    output reg MemtoReg,
    output reg [1:0]ALUOp,
    output reg MemWrite = 0,
    output reg MemRead = 0,
    output reg ALUSrc,
    output reg RegWrite
);

    always @(*)
    begin

        RegDst = 'bx;
        jump = 'b0;
        Branch = 'b0;
        MemtoReg = 'bx;
        ALUOp = 2'bxx; 
        MemWrite = 'b0; 
        MemRead = 'b0;
        ALUSrc = 'bx;
        RegWrite = 'b0;              
        case (opcode)
            'b000000:
            begin
                case(funct)   
                    'b100000: //add
                    begin
                        RegDst = 1;
                        jump = 0;
                        Branch = 0;
                        MemtoReg = 0;
                        ALUOp = 2'b00; 
                        MemWrite = 0; 
                        MemRead = 0;
                        ALUSrc = 0;
                        RegWrite = 1;     
                    end
                    'b101010: //slt
                    begin
                        RegDst = 1;
                        jump = 0;
                        Branch = 0;
                        MemtoReg = 0;
                        ALUOp = 2'b10; 
                        MemWrite = 0; 
                        MemRead = 0;
                        ALUSrc = 0;
                        RegWrite = 1;     
                    end
                endcase
            end
            'b001000: //addi
                    begin
                        RegDst = 0;
                        jump = 0;
                        Branch = 0;
                        MemtoReg = 0;
                        ALUOp = 2'b00; 
                        MemWrite = 0; 
                        MemRead = 0;
                        ALUSrc = 1;
                        RegWrite = 1;     
                    end
            'b000100: //beq
            begin
                RegDst = 'bx;
                jump = 0;
                Branch = 1;
                MemtoReg = 'bx;
                ALUOp = 2'b01; 
                MemWrite = 0; 
                MemRead = 0;
                ALUSrc = 0;
                RegWrite = 0;     
            end

            'b000010: //j
            begin
                RegDst = 'bx;
                jump = 1;
                Branch = 0;
                MemtoReg = 'bx;
                ALUOp = 2'bxx; 
                MemWrite = 0; 
                MemRead = 0;
                ALUSrc = 'bx;
                RegWrite = 0;     
            end
            'b100011: //lw
            begin
                RegDst = 0;
                jump = 0;
                Branch = 0;
                MemtoReg = 1;
                ALUOp = 2'b00; 
                MemWrite = 0; 
                MemRead = 1;
                ALUSrc = 1;
                RegWrite = 1;     
            end
            'b101011: //sw
            begin
                RegDst = 'b0;
                jump = 0;
                Branch = 0;
                MemtoReg = 'b0;
                ALUOp = 2'b00; 
                MemWrite = 1; 
                MemRead = 0;
                ALUSrc = 1;
                RegWrite = 0;     
            end
        endcase

    end

endmodule




module ALU(
    input [1:0]ALUOp,
    input signed [31:0] operand_1,
    input signed [31:0] operand_2,
    output reg signed [31:0] ALU_result,
    output Zero
);

    always @(*)
    begin

        case(ALUOp)
            2'b00:
                ALU_result = operand_1 + operand_2;
            2'b01:
                ALU_result = operand_1 - operand_2;
            2'b10:
                ALU_result = operand_1 < operand_2;
            default:
                ALU_result = 'b0;
        endcase
    end

    assign Zero = (ALU_result == 0)? 1'b1 : 1'b0;

endmodule


module Forward_Unit(
    input [4:0] rs_Xhl,
    input [4:0] rt_Xhl,
    input [4:0] rd_Mhl,
    input [4:0] rd_Whl,
    input RegWrite_Mhl,
    input RegWrite_Whl,
    output reg [1:0] forward_A,
    output reg [1:0] forward_B
);


    always @(*)
    begin

        if (RegWrite_Mhl == 1 && rd_Mhl != 0 && rd_Mhl == rs_Xhl)  // EX hazard
            forward_A = 2'b10;
        else if (RegWrite_Whl == 1 && rd_Whl != 0 && rd_Whl == rs_Xhl)  //MEM hazard
            forward_A = 2'b01;
        else
            forward_A = 2'b00;


        if (RegWrite_Mhl == 1 && rd_Mhl != 0 && rd_Mhl == rt_Xhl)  // EX hazard
            forward_B = 2'b10;
        else if (RegWrite_Whl == 1 && rd_Whl != 0 && rd_Whl == rt_Xhl)  //MEM hazard
            forward_B = 2'b01;
        else
            forward_B = 2'b00;
    end


endmodule

module Hazard_Detection(
    input MemRead_Xhl,
    input [4:0] rt_Xhl,
    input [4:0] rs_Dhl,
    input [4:0] rt_Dhl,
    output reg stall = 0
);

    always @(*)
    begin
        if(MemRead_Xhl == 1 && ((rt_Xhl == rt_Dhl) || (rt_Xhl == rs_Dhl)) )
            stall = 1;
        else
            stall = 0;
    end


endmodule



module Branch_Target_Buffer(
  input  clk,
  input rst_n,
  input [31:0] PC,
  input add,
  input remove,
  input [31:0]tag,
  input [31:0]target,
  output reg hit,
  output reg [31:0] hit_target
);

parameter entry_num = 5;

reg  [entry_num-1:0]entry_hit_status;

reg [31:0] target_buffer[0:entry_num-1];
reg [31:0] entry_tag[0:entry_num-1];
reg  entry_valid[0:entry_num-1];
reg [5:0] index; 


integer i; 
always @ (posedge clk or negedge rst_n) begin
    if(!rst_n) begin
        for(i = 0; i < entry_num  ; i++)
        begin
            target_buffer[i] <= 0;
            entry_tag[i] <= 0;
            entry_valid[i] <= 0;
        end    
    end
    else begin
        if(add)
        begin
            for(i = entry_num - 1  ; i >= 0;  i--)
            begin
                if(entry_valid[i] == 0)
                begin
                    target_buffer[i] <= target;
                    entry_tag[i] <= tag;
                    entry_valid[i] <= 1;  
                    break;
                end

            end
        end
        else if(remove)
        begin
            for(i = entry_num - 1  ; i >= 0;  i--)
            begin
                if(tag == entry_tag[i] )
                    entry_valid[i] <= 0;
            end
        end
  
    end
end
    always @(*)
    begin
        entry_hit_status = 0;
        for(i = 0  ; i <  entry_num; i++)
        begin
            entry_hit_status[i] = (entry_valid[i] && PC == entry_tag[i]);
        end    
    end

    // always @(*)
    // begin
    //     hit = 0;
    //     hit_target = 0;
    //     for(i = 0  ; i <  entry_num; i++)
    //     begin
    //        if(PC == entry_tag[i] && entry_valid[i] == 1)
    //        begin
    //             hit = 1;
    //             hit_target = target_buffer[i];
    //        end
    //     end    
    // end



    always @(*) begin
        index = 0;
        for (i=0; i<entry_num; i++) 
        begin
            if (entry_hit_status[i])
                index = i;
        end
    end
    assign hit = entry_hit_status > 0 ? 'b1 : 'b0;
    assign hit_target = target_buffer[index];
endmodule


module Branch_Predictor
(
  input  clk,
  input rst_n,
  input  branch_result,
  input is_update_predictor,
  output reg branch_prediction
);


parameter bit_depth = 18;

parameter SNT = 2'b00;
parameter WNT = 2'b01;
parameter WT  = 2'b10;
parameter ST  = 2'b11;

reg [bit_depth - 1 :0] BHR, BHR_next;
reg [1:0] PHT[2**bit_depth - 1:0];
reg [1:0]PHT_next;


integer  i;



always @ (posedge clk or negedge rst_n) begin
    if(!rst_n) begin
        BHR <= 'd0;
        for(i = 0; i < 2 ** bit_depth  ; i++)
            PHT[i] <= WNT;
    end
    else begin
        BHR <= BHR_next;
        PHT[BHR] <= PHT_next; 
    end
end

always @(*)
begin
    if( is_update_predictor)
    begin
        BHR_next = (BHR << 1'b1)  +  branch_result ;
    end
    else
    begin
        BHR_next = BHR;
    end
end

always@(*)
begin
    if( is_update_predictor)
    begin
        case(PHT[BHR])
            ST:begin
                if(branch_result == 1)
                    PHT_next = ST;
                else
                    PHT_next = WT;
            end
            WT:begin
                if(branch_result == 1)
                    PHT_next = ST;
                else
                    PHT_next = WNT;
            end
            SNT:begin
                if(branch_result == 1)
                    PHT_next = WNT;
                else
                    PHT_next = SNT;
            end
            WNT:begin
                if(branch_result == 1)
                    PHT_next = WT;
                else
                    PHT_next = SNT;
            end
            default:
                PHT_next = PHT[BHR];
        endcase
    end
    else
        PHT_next = PHT[BHR];
end

always @(*)
begin
    case(PHT[BHR])
        ST:begin
            branch_prediction = 1'd1;
        end
        WT:begin
            branch_prediction = 1'd1;
        end
        SNT:begin
            branch_prediction = 1'd0;
        end
        WNT:begin
            branch_prediction = 1'd0;
        end
    endcase
end

  
endmodule

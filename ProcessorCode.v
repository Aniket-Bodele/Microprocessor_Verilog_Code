// Program Counter Plus 4
module PCplus4(fromPC, NexttoPC);
    input [31:0] fromPC;
    output [31:0] NexttoPC;
    assign NexttoPC = fromPC + 32'd4;
endmodule

// Program Counter
module Program_counter(clk, reset, Pc_in, Pc_out);
    input clk, reset;
    input [31:0] Pc_in;
    output reg [31:0] Pc_out;
    always @(posedge clk or posedge reset)
    begin
        if (reset)
            Pc_out <= 32'b0;
        else
            Pc_out <= Pc_in;
    end
endmodule

// Instruction Memory
module Instruction_mem(clk, reset, read_address, instruction_out);
    input clk, reset;
    input [31:0] read_address;
    output [31:0] instruction_out;
    reg [31:0] I_Memory [1024:0];
    assign instruction_out = I_Memory[read_address];  

    integer k;
    always @(posedge clk or posedge reset)
    begin
        if (reset)
        begin
            // Initialize memory with instructions at reset
            I_Memory[0] = 32'b0;
            I_Memory[4] = 32'b0000000_11001_10000_000_01101_0110011;  // add 13, 16, 25
            I_Memory[8] = 32'b0100000_00011_01000_000_00101_0110011;  // sub 5, 8, 3
            I_Memory[12] = 32'b0000000_00011_00010_111_00001_0110011;  // and 1, 2, 3
            I_Memory[16] = 32'b0000000_00101_00011_110_00100_0110011;  // or 4, 3, 5

            //I-Type
            I_Memory[20] = 32'b000000000011_10101_000_10110_0010011;                 //addi 22, 21, 3(imm)
            I_Memory[24] = 32'b000000000011_10101_011_10110_0010011;                 //subi 22, 21, 3(imm)
            I_Memory[28] = 32'b000000000011_10101_111_10110_0010011;                 //ANDi 22, 21, 3(imm)
            I_Memory[32] = 32'b000000000011_10101_110_10110_0010011;                 //ORi 22, 21, 3(imm)
            I_Memory[36] = 32'b000000000011_10101_001_10110_0010011;                 //XORi 22, 21, 3(imm)
            I_Memory[40] = 32'b000000000001_01000_110_01001_0010011;                 //ori 9, 8, 1(imm)
            //L-Type
            I_Memory[44] = 32'b000000001111_00101_010_01000_0000011;                 // lw 8, 15(*5)
            I_Memory[48] = 32'b000000000011_00011_010_01001_0000011;                 // lw 9, 3(*3)
            //S- Type
            I_Memory[52] = 32'b0000000_01111_00101_010_01100_0100011;                // sw 15, 12(*5)
            I_Memory[56] = 32'b0000000_01110_00110_010_01010_0100011;                // sw 14, 10(*6)
            //SB-Type
            I_Memory[60]= 32'h00948663;                                              //beq 9,9,12     (0000000_01001_01001_000_01100_1100011)
end     
            // Add more instructions as required
        end

endmodule

// Immediate Generator
module ImmGen(Opcode, instruction, ImmExt);
    input [6:0] Opcode;
    input [31:0] instruction;
    output reg [31:0] ImmExt;
    always @(*)
    begin
        case (Opcode)
            7'b0010011: ImmExt <= {{20{instruction[31]}}, instruction[31:20]};  // I-type load
            7'b0000011: ImmExt <= {{20{instruction[31]}}, instruction[31:20]};  // L-type load
            7'b0100011: ImmExt <= {{20{instruction[31]}}, instruction[31:25], instruction[11:7]};  // S-type store
            7'b1100011: ImmExt <= {{19{instruction[31]}}, instruction[31], instruction[30:25], instruction[11:8], 1'b0};  // B-type branch
            default: ImmExt <= 32'b0;
        endcase
    end
endmodule

// Control Unit
module Control_unit(instruction, Branch, MemRead, MemtoReg, ALUOp, MemWrite, ALUSrc, RegWrite);
    input [6:0] instruction;
    output reg Branch, MemRead, MemtoReg, MemWrite, ALUSrc, RegWrite;
    output reg [1:0] ALUOp;
    always @(*)
    begin
        case (instruction)
            7'b0110011: {ALUSrc, MemtoReg, RegWrite, MemRead, MemWrite, Branch, ALUOp} <= 8'b001000_10;  // R-type
            7'b0010011: {ALUSrc, MemtoReg, RegWrite, MemRead, MemWrite, Branch, ALUOp} <= 8'b101000_11;  // I-type
            7'b0000011: {ALUSrc, MemtoReg, RegWrite, MemRead, MemWrite, Branch, ALUOp} <= 8'b111100_00;  // Lw-type
            7'b0100011: {ALUSrc, MemtoReg, RegWrite, MemRead, MemWrite, Branch, ALUOp} <= 8'b100010_00;  // Store-type
            7'b1100011: {ALUSrc, MemtoReg, RegWrite, MemRead, MemWrite, Branch, ALUOp} <= 8'b000001_01;  // Branch-type
            default: {ALUSrc, MemtoReg, RegWrite, MemRead, MemWrite, Branch, ALUOp} <= 8'b000000_00;
        endcase
    end
endmodule

// Register File
module Reg_File (clk, reset, Rs1, Rs2, Rd, Write_Data, read_data1, read_data2, RegWrite);
    input clk, reset, RegWrite;
    input [4:0] Rs1, Rs2, Rd;
    input [31:0] Write_Data;
    output [31:0] read_data1, read_data2;
    reg [31:0] registers [31:0];
    reg initialized;  // Flag to check if registers have been initialized

    // Initializing registers with some initial values
    initial begin
        initialized = 1'b1; 
        registers[0] = 32'd5;
        registers[1] = 32'd4;
        registers[2] = 32'd2;
        registers[3] = 32'd24;
        registers[4] = 32'd4;
        registers[5] = 32'd1;
        registers[6] = 32'd44;
        registers[7] = 32'd4;
        registers[8] = 32'd2;
        registers[9] = 32'd1;
        registers[10] = 32'd23;
        registers[11] = 32'd4;
        registers[12] = 32'd90;
        registers[13] = 32'd10;
        registers[14] = 32'd20;
        registers[15] = 32'd30;
        registers[16] = 32'd40;
        registers[17] = 32'd50;
        registers[18] = 32'd60;
        registers[19] = 32'd70;
        registers[20] = 32'd80;
        registers[21] = 32'd80;
        registers[22] = 32'd90;
        registers[23] = 32'd70;
        registers[24] = 32'd60;
        registers[25] = 32'd65;
        registers[26] = 32'd4;
        registers[27] = 32'd32;
        registers[28] = 32'd12;
        registers[29] = 32'd34;
        registers[30] = 32'd5;
        registers[31] = 32'd10;
        
         // Set the flag to initialized
    end

    integer i;
    always @(posedge clk or posedge reset) begin
        if (reset) begin
            if (initialized) begin
                // Preserve initial register values
                registers[0] <= 32'b0;
                for (i = 1; i < 32; i = i + 1) begin
                    registers[i] <= registers[i];  // Keep the values unchanged
                end
            end else begin
                // Clear all registers if they were not initialized yet
                for (i = 0; i < 32; i = i + 1) begin
                    registers[i] <= 32'b0;
                end
            end
        end 
        else if (RegWrite) begin
            // Write data to the register
            registers[Rd] <= Write_Data;
        end
    end

    assign read_data1 = registers[Rs1];
    assign read_data2 = registers[Rs2];
endmodule

// ALU Control
module ALU_Control(ALUOp, fun7, fun3, Control_out);
    input fun7;
    input [2:0] fun3;
    input [1:0] ALUOp;
    output reg [3:0] Control_out;
    always @(*)
    begin
        casex ({ALUOp, fun7, fun3})
            6'b00_x_xxx: Control_out <= 4'b0010;//add(load and store)
            6'b01_x_xxx: Control_out <= 4'b0110;//sub(branch)
            6'b10_0_000: Control_out <= 4'b0010;//add
            6'b11_x_000: Control_out <= 4'b0010;//addi
            6'b10_1_000: Control_out <= 4'b0110;//sub
            6'b11_x_011: Control_out <= 4'b0110;//subi
            6'b10_0_111: Control_out <= 4'b0000;//AND
            6'b11_x_111: Control_out <= 4'b0000;//ANDi
            6'b10_0_110: Control_out <= 4'b0001;//OR
            6'b11_x_110: Control_out <= 4'b0001;//ORi
            6'b10_0_001: Control_out <= 4'b1000;//XOR
            6'b11_x_001: Control_out <= 4'b1000;//XORi
            6'b10_0_010: Control_out <= 4'b1001;//INC

            default: Control_out <= 4'b1111;
        endcase
    end
endmodule

// ALU
module ALU_unit(A, B, Control_in, ALU_Result, zero);
    input [31:0] A, B;
    input [3:0] Control_in;
    output reg [31:0] ALU_Result;
    output reg zero;
    always @(Control_in or A or B)
    begin
        case (Control_in)
            4'b0000: begin zero <= 1'b0; ALU_Result <= A & B; end
            4'b0001: begin zero <= 1'b0; ALU_Result <= A | B; end
            4'b0010: begin zero <= 1'b0; ALU_Result <= A + B; end
            4'b0110: begin if(A==B) zero<=1'b1; else begin zero<=1'b0; ALU_Result<=A - B;end  end
            4'b1000: begin  zero <= 1'b0; ALU_Result <= A ^ B;  end
            4'b1001: begin zero <= 1'b0; ALU_Result <= A + 1; end
            default: begin zero <= 1'b0; ALU_Result <= 32'b0; end
        endcase
    end
endmodule
//Data memory
module Data_Memory (clk, reset, MemWrite, MemRead, read_address, Write_data, MemData_out);
input clk,reset, MemWrite, MemRead;
input [31:0] read_address, Write_data;
output [31:0] MemData_out;
reg [31:0] D_Memory [63:0];
assign MemData_out = (MemRead) ? D_Memory[read_address] : 32'b00;
integer k;
always @(posedge clk) begin
    D_Memory[16]=56;
    D_Memory[27]=65;
end
always @(posedge clk or posedge reset)
begin 
if(reset)
begin
    for(k=0;k<64;k=k+1)begin
        D_Memory[k]<=32'b00;
    end
end
else if(MemWrite) begin
    D_Memory[read_address]<=Write_data;
end
end

endmodule
//MUX
module Mux(sel1, A1, B1, Mux1_out);
input sel1;
input [31:0] A1,B1;
output [31:0] Mux1_out;
assign Mux1_out = (sel1==1'b0)? A1: B1;
endmodule
//Adder
module Adder(in_1,in_2,Sum_out);
input [31:0] in_1,in_2;
output [31:0]Sum_out;
assign Sum_out = in_1 + in_2;
endmodule
//And_Logic
module AND_logic (branch, zero, and_out);
input branch,zero;
output and_out;
assign and_out = branch & zero;
endmodule
//Processor Code
module top(clk, reset);
wire [31:0] PC_top, instruction_top, Rd1_top, Rd2_top, ImmExt_top, mux1_top, Sum_out_top, NextoPC_top, PCin_top, address_top, Memdata_top, WriteBack_top;
wire RegWrite_top, ALUSrc_top, zero_top, branch_top, sel2_top, MemtoReg_top, MemWrite_top, MemRead_top;
wire [1:0] ALUOp_top;
wire [3:0] control_top;
input clk, reset;
Program_counter PC (.clk(clk), .reset(reset), .Pc_in(PCin_top), .Pc_out(PC_top));
PCplus4 PCplus4 (.fromPC(PC_top), .NexttoPC(NextoPC_top));
Instruction_mem Inst_Memory (.clk(clk), .reset(reset), .read_address(PC_top), .instruction_out(instruction_top));
Reg_File Reg_File (.clk(clk), .reset(reset),.Rs1(instruction_top[19:15]), .Rs2(instruction_top[24:20]), .Rd(instruction_top[11:7]), .Write_Data(WriteBack_top), .read_data1(Rd1_top), .read_data2(Rd2_top), .RegWrite(RegWrite_top));
ImmGen  ImmGen(.Opcode(instruction_top[6:0]),.instruction(instruction_top),.ImmExt(ImmExt_top));
Control_unit Control_unit(.instruction(instruction_top[6:0]), .Branch(branch_top), .MemRead(MemRead_top), .MemtoReg(MemtoReg_top), .ALUOp(ALUOp_top), .MemWrite(MemWrite_top), .ALUSrc(ALUSrc_top), .RegWrite(RegWrite_top));
ALU_Control ALU_Control(.ALUOp(ALUOp_top), .fun7(instruction_top[30]), .fun3(instruction_top[14:12]), .Control_out(control_top));
ALU_unit ALU(.A(Rd1_top),.B(mux1_top),.Control_in(control_top), .ALU_Result(address_top), .zero(zero_top));
Mux ALU_mux(.sel1(ALUSrc_top), .A1(Rd2_top), .B1(ImmExt_top), .Mux1_out(mux1_top));
Adder Adder(.in_1(PC_top),.in_2(ImmExt_top),.Sum_out(Sum_out_top));
AND_logic  AND_logic (.branch(branch_top), .zero(zero_top), .and_out(sel2_top));
Mux  Adder_mux(.sel1(sel2_top), .A1(NextoPC_top), .B1(Sum_out_top), .Mux1_out(PCin_top));
Data_Memory Data_Memory (.clk(clk), .reset(reset), .MemWrite(MemWrite_top), .MemRead(MemRead_top), .read_address(address_top), .Write_data(Rd2_top), .MemData_out(Memdata_top));
Mux Memory_mux(.sel1(MemtoReg_top), .A1(address_top), .B1(Memdata_top), .Mux1_out(WriteBack_top));
endmodule


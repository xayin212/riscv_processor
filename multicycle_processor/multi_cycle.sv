// functional functions are lw, sw, add, sub, slt, or, and, 


module testbench();

  logic        clk;
  logic        reset;

  logic [31:0] WriteData, DataAdr;
  logic        MemWrite;

  // instantiate device to be tested
  top dut(clk, reset, WriteData, DataAdr, MemWrite);
  
  // initialize test
  initial
    begin
      reset <= 1; # 22; reset <= 0;
    end

  // generate clock to sequence tests
  always
    begin
      clk <= 1; # 5; clk <= 0; # 5;
    end

  // check results
   always @(negedge clk)
    begin
      if(MemWrite) begin
        if(DataAdr === 32 & WriteData === 67727382) begin
          $display("Simulation succeeded");
          $stop;
        end else if (DataAdr !== 96 & DataAdr != 100) begin
          $display("Simulation failed");
          $stop;
        end
      end
    end
endmodule

module top(input logic clk, reset,
			 output logic [31:0] WriteDataM, DataAdrM,
			 output logic MemWriteM);

	logic [31:0] PCF, InstrF, ReadDataM;

 // instantiate processor and memories
 	riscv riscv(clk, reset, PCF, InstrF, MemWriteM, DataAdrM,
 	WriteDataM, ReadDataM);
 	imem imem(PCF, InstrF);
 	dmem dmem(clk, MemWriteM, DataAdrM, WriteDataM, ReadDataM);
endmodule

module imem(input logic [31:0] PCF,
			output logic [31:0] InstrF);

	logic [31:0] RAM [63:0];

	initial
		$readmemh("riscvtest.txt",RAM);
	
	assign InstrF = RAM[PCF[31:2]];
endmodule

module dmem(input logic clk, MemWriteM,
			input logic [31:0] DataAdrM, WriteDataM,
			output logic [31:0] ReadDataM);
	
	logic [31:0] RAM [63:0];

	assign ReadDataM = RAM[DataAdrM[31:2]];

	always_ff @ (posedge clk)
		if (MemWriteM)
			RAM[DataAdrM[31:2]] = WriteDataM;
endmodule

module riscv(input logic clk, reset,
			output logic [31:0] PCF, 
			input logic [31:0] InstrF,
			output logic MemWriteM,
			output logic [31:0] DataAdrM, WriteDataM, 
			input logic [31:0] ReadDataM);

	logic PCSrcE, StallF, StallD, FlushD, FlushE, RegWriteD, MemWriteD, JumpD, BranchD, ALUSrcD, RegWriteW, RegWriteE, MemWriteE, JumpE, BranchE, ALUSrcE, ZeroE, RegWriteM;
	logic [1:0] ResultSrcD, ImmSrcD, ResultSrcE, ForwardAE, ForwardBE, ResultSrcM, ResultSrcW;
	logic [2:0] ALUControlD, ALUControlE;
	logic [4:0] RDW, RS1D, RS2D, RDD, RS1E, RS2E, RDE, RDM;
	logic [31:0] PCPlus4F, PCTargetE, notPCF, InstrD, PCD, PCPlus4D, ResultW, RD1D, RD2D, ImmExtD, RD1E, RD2E, PCE, ImmExtE, PCPlus4E, ALUResultM, SrcAE, SrcBE, WriteDataE, PCPlus4M, ALUResultW, ReadDataW, PCPlus4W, ALUResultE, LuiImmD, LuiImmE, LuiImmM, LuiImmW;

	assign DataAdrM = ALUResultM;
	
	mux2 #(32) pcsrcmux(PCPlus4F, PCTargetE, PCSrcE, notPCF);
	pcreg PCReg(clk, reset, StallF, notPCF, PCF);
	adder PCPlus4immediate(PCF, 32'd4, PCPlus4F);
	ifidreg IfIdReg(clk, reset, StallD, FlushD, PCF, InstrF, PCPlus4F, InstrD, PCD, PCPlus4D);
	controller ControlUnit(InstrD[6:0], InstrD[14:12], InstrD[30], RegWriteD, MemWriteD, JumpD, BranchD, ALUSrcD, ResultSrcD, ImmSrcD, ALUControlD);
	regfile RegisterFile(clk, RegWriteW, InstrD[19:15], InstrD[24:20], RDW, ResultW, RD1D, RD2D);
	extend extender(InstrD[31:7], ImmSrcD, ImmExtD);
	luibitshifter LUIBitShifter(InstrD[31:12], LuiImmD);
	idexreg IdExReg(clk, reset, FlushE, RegWriteD, MemWriteD, JumpD, BranchD, ALUSrcD,
			   ResultSrcD,
			   ALUControlD,
			   RD1D, RD2D, PCD, ImmExtD, PCPlus4D, InstrD, LuiImmD,
			   RegWriteE, MemWriteE, JumpE, BranchE, ALUSrcE,
			   ResultSrcE,
			   ALUControlE,
			   RS1E, RS2E, RDE,
			   RD1E, RD2E, PCE, ImmExtE, PCPlus4E, LuiImmE);
	mux4 #(32) ALUSrcA(RD1E, ResultW, ALUResultM, LuiImmM, ForwardAE, SrcAE);
	mux4 #(32) ALUSrcB(RD2E, ResultW, ALUResultM, LuiImmM, ForwardBE, WriteDataE);
	mux2 #(32) ImmvsRD2(WriteDataE, ImmExtE, ALUSrcE, SrcBE);
	adder PCTargetadd(PCE, ImmExtE, PCTargetE);
	alu ALU(SrcAE, SrcBE, ALUControlE, ALUResultE, ZeroE);
	exmemreg ExMemReg(clk, reset, RegWriteE, MemWriteE,
				ResultSrcE, 
				RDE,
				ALUResultE, WriteDataE, PCPlus4E, LuiImmE,
				RegWriteM, MemWriteM,
				ResultSrcM,
				RDM,
				ALUResultM, WriteDataM, PCPlus4M, LuiImmM);
	memwbreg MemWbReg(clk, reset, RegWriteM,
				ResultSrcM,
				RDM,
				ALUResultM, ReadDataM, PCPlus4M, LuiImmM,
				RegWriteW,
				ResultSrcW,
				RDW,
				ALUResultW, ReadDataW, PCPlus4W, LuiImmW);
	mux4 #(32) ResultMux(ALUResultW, ReadDataW, PCPlus4W, LuiImmW, ResultSrcW, ResultW);
	hazardunit HazardUnit(PCSrcE, RegWriteM, RegWriteW, ResultSrcE,
				  		  InstrD[19:15], InstrD[24:20], RS1E, RS2E, RDE, RDM, RDW,
				  		  StallF, StallD, FlushD, FlushE,
				  		  ForwardAE, ForwardBE);

	assign PCSrcE = ((BranchE & ZeroE) | JumpE);

endmodule

// registers

module pcreg(input logic clk, reset, StallF,
			 input logic [31:0] notPCF,
			 output logic [31:0] PCF);
	
	always_ff @ (posedge clk)
		begin
			if (reset)
				PCF <= 32'b0;
			else if (~StallF)
				PCF <= notPCF;
		end
endmodule

module ifidreg(input logic clk, reset, StallD, FlushD,
			   input logic [31:0] PCF, InstrF, PCPlus4F,
			   output logic [31:0] InstrD, PCD, PCPlus4D);
	
	always_ff @ (posedge clk)
		begin
			if (reset | FlushD)
				begin
					InstrD <= 32'b0;
					PCD <= 32'b0;
					PCPlus4D <= 32'b0;
				end
			else if (~StallD)
				begin
					InstrD <= InstrF;
					PCD <= PCF;
					PCPlus4D <= PCPlus4F;
				end
		end
endmodule

module idexreg(input logic clk, reset, FlushE, RegWriteD, MemWriteD, JumpD, BranchD, ALUSrcD,
			   input logic [1:0] ResultSrcD,
			   input logic [2:0] ALUControlD,
			   input logic [31:0] RD1D, RD2D, PCD, ImmExtD, PCPlus4D, InstrD, LuiImmD,
			   output logic RegWriteE, MemWriteE, JumpE, BranchE, ALUSrcE,
			   output logic [1:0] ResultSrcE,
			   output logic [2:0] ALUControlE,
			   output logic [4:0] RS1E, RS2E, RDE,
			   output logic [31:0] RD1E, RD2E, PCE, ImmExtE, PCPlus4E, LuiImmE);
		
	always_ff @ (posedge clk)
		begin
			if (reset | FlushE)
				begin
					RegWriteE <= 1'b0;
					MemWriteE <= 1'b0;
					JumpE <= 1'b0;
					BranchE <= 1'b0;
					ALUSrcE <= 1'b0;
					ResultSrcE <= 2'b0;
					ALUControlE <= 3'b0;
					RS1E <= 5'b0;
					RS2E <= 5'b0;
					RDE <= 5'b0;
					RD1E <= 32'b0;
					RD2E <= 32'b0;
					PCE <= 32'b0;
					ImmExtE <= 32'b0;
					PCPlus4E <= 32'b0;
					LuiImmE <= 32'b0;
				end
			else
				begin
					RegWriteE <= RegWriteD;
					MemWriteE <= MemWriteD;
					JumpE <= JumpD;
					BranchE <= BranchD;
					ALUSrcE <= ALUSrcD;
					ResultSrcE <= ResultSrcD;
					ALUControlE <= ALUControlD;
					RS1E <= InstrD[19:15];
					RS2E <= InstrD[24:20];
					RDE <= InstrD[11:7];
					RD1E <= RD1D;
					RD2E <= RD2D;
					PCE <= PCD;
					ImmExtE <= ImmExtD;
					PCPlus4E <= PCPlus4D;
					LuiImmE <= LuiImmD;
				end
		end
endmodule

module exmemreg(input logic clk, reset, RegWriteE, MemWriteE,
				input logic [1:0] ResultSrcE, 
				input logic [4:0] RDE,
				input logic [31:0] ALUResultE, WriteDataE, PCPlus4E, LuiImmE, 
				output logic RegWriteM, MemWriteM,
				output logic [1:0] ResultSrcM,
				output logic [4:0] RDM,
				output logic [31:0] ALUResultM, WriteDataM, PCPlus4M, LuiImmM);

	always_ff @ (posedge clk)
		begin
			if (reset)
				begin
					RegWriteM <= 1'b0;
					MemWriteM <= 1'b0;
					ResultSrcM <= 2'b0;
					RDM <= 5'b0;
					ALUResultM <= 32'b0;
					WriteDataM <= 32'b0;
					PCPlus4M <= 32'b0;
					LuiImmM <= 32'b0;
				end
			else
				begin
					RegWriteM <= RegWriteE;
					MemWriteM <= MemWriteE;
					ResultSrcM <= ResultSrcE;
					RDM <= RDE;
					ALUResultM <= ALUResultE;
					WriteDataM <= WriteDataE;
					PCPlus4M <= PCPlus4E;
					LuiImmM <= LuiImmE;
				end
		end
endmodule

module memwbreg(input logic clk, reset, RegWriteM,
				input logic [1:0] ResultSrcM,
				input logic [4:0] RDM,
				input logic [31:0] ALUResultM, ReadDataM, PCPlus4M, LuiImmM,
				output logic RegWriteW,
				output logic [1:0] ResultSrcW,
				output logic [4:0] RDW,
				output logic [31:0] ALUResultW, ReadDataW, PCPlus4W, LuiImmW);

	always_ff @ (posedge clk)
		begin
			if (reset)
				begin
					RegWriteW <= 1'b0;
					ResultSrcW <= 2'b0;
					ALUResultW <= 32'b0;
					ReadDataW <= 32'b0;
					RDW <= 32'b0;
					PCPlus4W <= 32'b0;
					LuiImmW <= 32'b0;
				end
			else
				begin
					RegWriteW <= RegWriteM;
					ResultSrcW <= ResultSrcM;
					ALUResultW <= ALUResultM;
					ReadDataW <= ReadDataM;
					RDW <= RDM;
					PCPlus4W <= PCPlus4M;
					LuiImmW <= LuiImmM;
				end
		end
endmodule

module controller(input logic [6:0] op,
				  input logic [2:0] funct3,
				  input logic funct7b5,
				  output logic RegWriteD, MemWriteD, JumpD, BranchD, ALUSrcD,
				  output logic [1:0] ResultSrcD, ImmSrcD, 
				  output logic [2:0] ALUControlD);
	
	logic [1:0] ALUOp;
	logic [10:0] controls;

	logic  RtypeSub;
  	assign RtypeSub = funct7b5 & op[5];  // TRUE for R-type subtract instruction

	assign {RegWriteD, ImmSrcD, ALUSrcD, MemWriteD,
          ResultSrcD, BranchD, ALUOp, JumpD} = controls;

	always_comb
		case (op)
			7'b0000011: controls = 11'b1_00_1_0_01_0_00_0; // lw
			7'b0100011: controls = 11'b0_01_1_1_00_0_00_0; // sw
			7'b0110011: controls = 11'b1_00_0_0_00_0_10_0; // R-type 
			7'b1100011: controls = 11'b0_10_0_0_00_1_01_0; // beq
			7'b0010011: controls = 11'b1_00_1_0_00_0_10_0; // I-type ALU
			7'b1101111: controls = 11'b1_11_0_0_10_0_00_1; // JAL
			7'b0110111: controls = 11'b1_00_0_0_11_0_00_0; // lui
			default:    controls = 11'b0_00_0_0_00_0_00_0; // non-implemented instruction
		endcase

	always_comb
    case(ALUOp)
      2'b00:                ALUControlD = 3'b000; // addition
      2'b01:                ALUControlD = 3'b001; // subtraction
      default: case(funct3) // R-type or I-type ALU
                 3'b000:  if (RtypeSub) 
                            ALUControlD = 3'b001; // sub
                          else          
                            ALUControlD = 3'b000; // add, addi
					  3'b001:    ALUControlD = 3'b110; // sll
                 3'b010:    ALUControlD = 3'b101; // slt, slti
					  3'b100:	 ALUControlD = 3'b000; // lbu
                 3'b110:    ALUControlD = 3'b011; // or, ori
                 3'b111:    ALUControlD = 3'b010; // and, andi
                 default:   ALUControlD = 3'bxxx; // ???
               endcase
    endcase

endmodule

module hazardunit(input logic PCSrcE, RegWriteM, RegWriteW,
				  input logic [1:0] ResultSrcE,
				  input logic [4:0] RS1D, RS2D, RS1E, RS2E, RDE, RDM, RDW,
				  output logic StallF, StallD, FlushD, FlushE,
				  output logic [1:0] ForwardAE, ForwardBE);

	logic lwStall;

	always_comb
		begin
			//ForwardAE
			if ((ResultSrcE === 2'b11) & (RS1E === RDM) & (RS1E !== 1'b0))
				ForwardAE = 2'b11;
			if (((RS1E === RDM) & RegWriteM) & RS1E !== 1'b0)
				ForwardAE <= 2'b10;
			else if (((RS1E === RDW) & RegWriteW) & RS1E !== 1'b0)
				ForwardAE <= 2'b01;
			else
				ForwardAE <= 2'b00;

			//ForwardBE
			if ((ResultSrcE === 2'b11) & (RS2E === RDM) & (RS1E !== 1'b0))
				ForwardAE = 2'b11;
			if (((RS2E === RDM) & RegWriteM) & RS2E !== 1'b0)
				ForwardBE <= 2'b10;
			else if (((RS2E === RDW) & RegWriteW) & RS2E !== 1'b0)
				ForwardBE <= 2'b01;
			else
				ForwardBE <= 2'b00;

			lwStall <= (((RS1D === RDE) | (RS2D === RDE)) & ResultSrcE[0] === 1'b1);

			assign StallF = lwStall;
			assign StallD = lwStall;
			assign FlushD = PCSrcE;
			assign FlushE = lwStall | PCSrcE;
		end
endmodule

module regfile(input  logic        clk, 
               input  logic        we3, 
               input  logic [ 4:0] a1, a2, a3, 
               input  logic [31:0] wd3, 
               output logic [31:0] rd1, rd2);

  logic [31:0] rf[31:0];

  always_ff @(negedge clk)
    if (we3) rf[a3] <= wd3;	

  assign rd1 = (a1 != 0) ? rf[a1] : 0;
  assign rd2 = (a2 != 0) ? rf[a2] : 0;
endmodule

module extend(input  logic [31:7] instr,
              input  logic [1:0]  immsrc,
              output logic [31:0] immext);
 
  always_comb
    case(immsrc) 
               // I-type 
      2'b00:   immext = {{20{instr[31]}}, instr[31:20]};  
               // S-type (stores)
      2'b01:   immext = {{20{instr[31]}}, instr[31:25], instr[11:7]};
               // B-type (branches)
      2'b10:   immext = {{20{instr[31]}}, instr[7], instr[30:25], instr[11:8], 1'b0};
               // J-type (jal)
      2'b11:   immext = {{12{instr[31]}}, instr[19:12], instr[20], instr[30:21], 1'b0};
      default: immext = 32'bx; // undefined
    endcase             
endmodule

module adder(input  [31:0] a, b,
             output [31:0] y);

  assign y = a + b;
endmodule

module alu(input  logic [31:0] a, b,
           input  logic [2:0]  alucontrol,
           output logic [31:0] result,
           output logic        zero);

  logic [31:0] condinvb, sum;
  logic        v;              // overflow
  logic        isAddSub;       // true when is add or subtract operation

  assign condinvb = alucontrol[0] ? ~b : b;
  assign sum = a + condinvb + alucontrol[0];
  assign isAddSub = ~alucontrol[2] & ~alucontrol[1] |
                    ~alucontrol[1] & alucontrol[0];

  always_comb
    case (alucontrol)
      3'b000:  result = sum;                 // add
      3'b001:  result = sum;                 // subtract
      3'b010:  result = a & b;               // and
      3'b011:  result = a | b;       			// or
      3'b100:  result = a ^ b;		         // xor
      3'b101:  result = (a < b) ? 1 : 0;     // slt
      3'b110:  result = a * (2 ** b);       	// sll
      default: result = 32'bx;
    endcase

  assign zero = (result == 32'b0);
  assign v = ~(alucontrol[0] ^ a[31] ^ b[31]) & (a[31] ^ sum[31]) & isAddSub;
  
endmodule

module mux2 #(parameter WIDTH = 8)
             (input  logic [WIDTH-1:0] d0, d1, 
              input  logic             s, 
              output logic [WIDTH-1:0] y);

  assign y = s ? d1 : d0; 
endmodule

module mux3 #(parameter WIDTH = 8)
             (input  logic [WIDTH-1:0] d0, d1, d2,
              input  logic [1:0]       s,
              output logic [WIDTH-1:0] y);

  assign y = s[1] ? d2 : (s[0] ? d1 : d0); 
endmodule

module mux4 #(parameter WIDTH = 8)
             (input  logic [WIDTH-1:0] d0, d1, d2, d3,
              input  logic [1:0]       s,
              output logic [WIDTH-1:0] y);

  assign y = s[1] ? (s[0] ? d3 : d2) : (s[0] ? d1 : d0); 
endmodule

 module luibitshifter(input logic [31:12] Instr,
                      output logic [31:0] imm);
    
	always_comb
		begin
    		imm = {Instr[31:12], 12'b0};
		end

endmodule

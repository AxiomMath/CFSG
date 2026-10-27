module

public import CFSG.Sporadic.GLQ.RegisterProgram
public meta import CFSG.Sporadic.GLQ.RegisterProgram
public import CFSG.LocalAnalysis.SectionRank.Sporadic.OpsF2
public meta import Certificates.Data.CFSGNative.SectionRank.F2
import CFSG.Blueprint.NativeSporadic
public meta import CFSG.LocalAnalysis.SectionRank.Sporadic.LocalWitness
public import CFSG.LocalAnalysis.SectionRank.Sporadic.LocalWitness
public meta import CFSG.Open.Defs
public import CFSG.Open.Defs

public noncomputable section

namespace CFSG.RankThree.PartOne.N143

open CFSG.SectionRank CFSG.SectionRank.Native CFSG.Sporadic.GLQ CFSG.Blueprint
open scoped Matrix

namespace Co1TwoRank

@[expose] def co1TwoProg : List Instr := [
    .iv 2 3, .mu 2 1 4, .mu 4 1 5, .mu 5 3 6, .mu 6 1 7, .mu 7 1 8, .mu 8 1 9, .mu 9 2 10,
    .mu 10 2 11, .mu 11 2 12, .mu 12 3 13, .mu 13 3 14, .pwr 20 14 15, .mu 2 2 16, .mu 16 3 17,
    .mu 17 1 18, .mu 18 2 19, .mu 19 1 20, .mu 20 1 21, .mu 21 2 22, .mu 22 3 23, .mu 23 1 24,
    .mu 24 2 25, .mu 25 1 26, .iv 26 27, .mu 27 15 28, .mu 28 26 29, .mu 15 29 30, .pwr 3 30 31,
    .mu 2 1 32, .mu 32 1 33, .mu 33 2 34, .mu 34 1 35, .mu 35 3 36, .mu 36 3 37, .mu 37 2 38,
    .mu 38 2 39, .mu 39 3 40, .mu 40 1 41, .mu 41 3 42, .iv 42 43, .mu 43 15 44, .mu 44 42 45,
    .mu 15 45 46, .pwr 2 46 47, .mu 42 47 48, .iv 48 49, .mu 49 31 50, .mu 50 48 51,
    .mu 31 51 52, .pwr 1 52 53, .mu 1 2 54, .mu 54 1 55, .mu 55 3 56, .mu 56 3 57, .mu 57 2 58,
    .mu 58 1 59, .mu 59 1 60, .mu 60 2 61, .mu 61 3 62, .mu 62 3 63, .mu 63 2 64, .iv 64 65,
    .mu 65 15 66, .mu 66 64 67, .mu 15 67 68, .pwr 2 68 69, .mu 64 69 70, .iv 70 71,
    .mu 71 31 72, .mu 72 70 73, .mu 31 73 74, .pwr 2 74 75, .iv 75 76, .mu 76 53 77,
    .mu 77 75 78, .mu 53 78 79, .pwr 1 79 80, .mu 3 1 81, .mu 81 2 82, .mu 82 3 83, .mu 83 2 84,
    .mu 84 3 85, .mu 85 3 86, .mu 86 2 87, .mu 87 3 88, .mu 88 1 89, .mu 89 3 90, .mu 90 3 91,
    .iv 91 92, .mu 92 15 93, .mu 93 91 94, .mu 15 94 95, .pwr 2 95 96, .mu 91 96 97, .iv 97 98,
    .mu 98 31 99, .mu 99 97 100, .mu 31 100 101, .pwr 1 101 102, .mu 97 102 103, .iv 103 104,
    .mu 104 53 105, .mu 105 103 106, .mu 53 106 107, .pwr 1 107 108, .mu 103 108 109,
    .iv 109 110, .mu 110 80 111, .mu 111 109 112, .mu 80 112 113, .pwr 1 113 114]

@[expose] def co1TwoOuts : Fin 5 → ℕ := ![15, 31, 53, 80, 114]

@[expose] def co1TwoRegs : Array (Array ℕ × Array ℕ) :=
  runProgN (ops2 24) (initRegsN (ops2 24) 115
    ((ops2 24).decode NativeSporadic.Co1Seed1, (ops2 24).decode NativeSporadic.Co1Seed1)
    ((ops2 24).decode NativeSporadic.Co1Seed2,
      (ops2 24).pow ((ops2 24).decode NativeSporadic.Co1Seed2) 2)) co1TwoProg

@[expose] def co1TwoCheck : Bool :=
  co1TwoProg.all (Instr.lt 115) &&
    elem2OK (ops2 24) (List.ofFn fun i => co1TwoRegs[co1TwoOuts i]!.1) (List.range 24)

end Co1TwoRank

end CFSG.RankThree.PartOne.N143

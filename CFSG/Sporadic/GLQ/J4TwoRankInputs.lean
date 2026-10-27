module

public import CFSG.Sporadic.GLQ.RegisterProgram
public meta import CFSG.Sporadic.GLQ.RegisterProgram
public import CFSG.LocalAnalysis.SectionRank.Sporadic.OpsF2
public meta import Certificates.Data.CFSGNative.SectionRank.F2
public import CFSG.LocalAnalysis.SectionRank.Sporadic.J4Action
import CFSG.Blueprint.NativeSporadic
public meta import CFSG.LocalAnalysis.SectionRank.Sporadic.LocalWitness
public meta import CFSG.Open.Defs

public noncomputable section

namespace CFSG.Sporadic.GLQ

open CFSG.SectionRank CFSG.SectionRank.Native CFSG.SectionRank.LocalWitness CFSG.Blueprint
open scoped Matrix

namespace J4TwoRank

@[expose] def j4Prog : List Instr := [
    .mu 1 2 3, .mu 3 2 4, .mu 3 4 5, .mu 3 3 6, .mu 2 1 3, .mu 5 2 7, .pwr 18 3 2, .mu 6 2 3,
    .pwr 3 5 8, .mu 7 8 2, .mu 1 2 7, .iv 2 8, .pwr 5 5 2, .mu 8 7 5, .mu 6 6 7, .iv 7 8,
    .mu 2 7 6, .mu 8 6 1, .pwr 4 4 2, .iv 3 7, .mu 2 3 8, .mu 7 8 2, .mu 1 2 3, .mu 3 2 4,
    .mu 4 4 6, .mu 3 3 4, .mu 4 6 7, .mu 3 4 8, .mu 7 8 4, .mu 5 4 6, .pwr 15 6 3, .mu 2 1 9,
    .pwr 4 9 10, .iv 2 11, .mu 10 11 12, .mu 12 1 13, .iv 13 14, .mu 2 14 15, .mu 15 3 16,
    .mu 16 13 17, .pwr 3 17 18, .iv 1 19, .pwr 1 19 20, .iv 20 21, .mu 21 18 22, .mu 22 20 22,
    .pwr 1 19 23, .mu 23 11 23, .iv 23 24, .mu 24 18 25, .mu 25 23 25, .pwr 1 19 26, .mu 26 2 26,
    .iv 26 27, .mu 27 18 28, .mu 28 26 28, .pwr 1 19 29, .mu 29 11 29, .mu 29 19 29, .iv 29 30,
    .mu 30 18 31, .mu 31 29 31, .pwr 1 19 32, .mu 32 2 32, .mu 32 19 32, .iv 32 33, .mu 33 18 34,
    .mu 34 32 34, .pwr 1 19 35, .mu 35 11 35, .mu 35 19 35, .mu 35 11 35, .iv 35 36,
    .mu 36 18 37, .mu 37 35 37, .pwr 1 19 38, .mu 38 11 38, .mu 38 19 38, .mu 38 2 38, .iv 38 39,
    .mu 39 18 40, .mu 40 38 40, .pwr 1 19 41, .mu 41 11 41, .mu 41 19 41, .mu 41 11 41,
    .mu 41 19 41, .iv 41 42, .mu 42 18 43, .mu 43 41 43, .pwr 1 19 44, .mu 44 11 44,
    .mu 44 19 44, .mu 44 2 44, .mu 44 19 44, .iv 44 45, .mu 45 18 46, .mu 46 44 46, .pwr 1 19 47,
    .mu 47 11 47, .mu 47 19 47, .mu 47 11 47, .mu 47 19 47, .mu 47 11 47, .iv 47 48,
    .mu 48 18 49, .mu 49 47 49]

@[expose] def j4Outs : Fin 11 → ℕ := ![18, 22, 25, 28, 31, 34, 37, 40, 43, 46, 49]

@[expose] def j4Regs : Array (Array ℕ × Array ℕ) :=
  runProgN (ops2 112) (initRegsN (ops2 112) 50
    ((ops2 112).decode NativeSporadic.J4Seed1, (ops2 112).decode NativeSporadic.J4Seed1)
    ((ops2 112).decode NativeSporadic.J4Seed2,
      (ops2 112).pow ((ops2 112).decode NativeSporadic.J4Seed2) 3)) j4Prog

@[expose] def j4Check : Bool :=
  j4Prog.all (Instr.lt 50) && elem2OK (ops2 112) (List.ofFn fun i => j4Regs[j4Outs i]!.1) [0]

end J4TwoRank

end CFSG.Sporadic.GLQ

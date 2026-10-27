module

public import CFSG.Sporadic.GLQ.RegisterProgram
public meta import CFSG.Sporadic.GLQ.RegisterProgram
public import CFSG.LocalAnalysis.SectionRank.Sporadic.OpsF2
public meta import Certificates.Data.CFSGNative.SectionRank.F2
import CFSG.Blueprint.NativeSporadic
public import CFSG.RankThree.PartOne.KS.ScalFiveDefs
public meta import CFSG.RankThree.PartOne.KS.ScalFiveDefs

public section

namespace CFSG.RankThree.PartOne.KS.Co1Scal

open CFSG.SectionRank CFSG.SectionRank.Native CFSG.Blueprint CFSG.Sporadic.GLQ
  CFSG.RankThree.PartOne.KS.ScalFive

@[expose] def co1Prog : List Instr := [
  .iv 2 3, .pwr 1 1 4, .mu 4 2 4, .mu 4 1 4, .mu 4 3 4, .mu 4 1 4, .mu 4 3 4, .mu 4 1 4, .mu 4 2 4,
  .mu 4 1 4, .mu 4 3 4, .mu 4 1 4, .mu 4 3 4, .mu 4 1 4, .mu 4 3 4, .mu 4 1 4, .mu 4 3 4,
  .mu 4 1 4, .mu 4 2 4, .mu 4 1 4, .mu 4 3 4, .mu 4 1 4, .mu 4 2 4, .mu 4 1 4, .mu 4 2 4,
  .mu 4 1 4, .mu 4 2 4, .mu 4 1 4, .mu 4 2 4, .mu 4 1 4, .mu 4 3 4, .mu 4 1 4, .mu 4 3 4,
  .mu 4 1 4, .mu 4 2 4, .mu 4 1 4, .mu 4 2 4, .mu 4 1 4, .mu 4 2 4, .mu 4 1 4, .mu 4 2 4,
  .mu 4 1 4, .mu 4 3 4, .mu 4 1 4, .mu 4 3 4, .mu 4 1 4, .mu 4 2 4, .mu 4 1 4, .mu 4 3 4,
  .mu 4 1 4, .mu 4 2 4, .mu 4 1 4, .mu 4 2 4, .mu 4 1 4, .mu 4 2 4, .mu 4 1 4, .mu 4 3 4,
  .mu 4 1 4, .mu 4 2 4, .mu 4 1 4, .mu 4 3 4, .mu 4 1 4, .mu 4 3 4, .mu 4 1 4, .mu 4 2 4,
  .mu 4 1 4, .mu 4 3 4, .mu 4 1 4, .mu 4 2 4, .mu 4 1 4, .mu 4 3 4, .mu 4 1 4, .mu 4 2 4,
  .mu 4 1 4, .mu 4 2 4, .mu 4 1 4, .mu 4 2 4, .mu 4 1 4, .mu 4 3 4, .mu 4 1 4, .mu 4 2 4,
  .mu 4 1 4, .mu 4 3 4, .mu 4 1 4, .mu 4 2 4, .mu 4 1 4, .mu 4 2 4, .mu 4 1 4, .mu 4 3 4,
  .mu 4 1 4, .mu 4 2 4, .mu 4 1 4, .mu 4 3 4, .mu 4 1 4, .mu 4 2 4, .mu 4 1 4, .mu 4 2 4,
  .mu 4 1 4, .mu 4 3 4, .mu 4 1 4, .mu 4 3 4, .mu 4 1 4, .mu 4 3 4, .mu 4 1 4, .mu 4 3 4,
  .mu 4 1 4, .mu 4 3 4, .mu 4 1 4, .mu 4 3 4, .mu 4 1 4, .mu 4 2 4, .mu 4 1 4, .mu 4 2 4,
  .mu 4 1 4, .mu 4 2 4, .mu 4 1 4, .mu 4 2 4, .mu 4 1 4, .mu 4 3 4, .mu 4 1 4, .mu 4 3 4,
  .pwr 1 3 5, .mu 5 1 5, .mu 5 2 5, .mu 5 1 5, .mu 5 2 5, .mu 5 1 5, .mu 5 3 5, .mu 5 1 5,
  .mu 5 3 5, .mu 5 1 5, .mu 5 3 5, .mu 5 1 5, .mu 5 3 5, .mu 5 1 5, .mu 5 3 5, .mu 5 1 5,
  .mu 5 2 5, .mu 5 1 5, .mu 5 3 5, .mu 5 1 5, .mu 5 2 5, .mu 5 1 5, .mu 5 3 5, .mu 5 1 5,
  .mu 5 3 5, .mu 5 1 5, .mu 5 3 5, .mu 5 1 5, .mu 5 2 5, .mu 5 1 5, .mu 5 3 5, .mu 5 1 5,
  .mu 5 2 5, .mu 5 1 5, .mu 5 3 5, .mu 5 1 5, .mu 5 2 5, .mu 5 1 5, .mu 5 3 5, .mu 5 1 5,
  .mu 5 3 5, .mu 5 1 5, .mu 5 2 5, .mu 5 1 5, .mu 5 3 5, .mu 5 1 5, .mu 5 3 5, .mu 5 1 5,
  .mu 5 2 5, .mu 5 1 5, .mu 5 3 5, .mu 5 1 5, .mu 5 2 5, .mu 5 1 5, .mu 5 3 5, .mu 5 1 5,
  .mu 5 3 5, .mu 5 1 5, .mu 5 2 5, .mu 5 1 5, .mu 5 3 5, .mu 5 1 5, .mu 5 3 5, .mu 5 1 5,
  .mu 5 3 5, .mu 5 1 5, .mu 5 2 5, .mu 5 1 5, .mu 5 3 5, .mu 5 1 5, .mu 5 2 5, .mu 5 1 5,
  .mu 5 3 5, .mu 5 1 5, .mu 5 2 5, .mu 5 1 5, .mu 5 3 5, .mu 5 1 5, .mu 5 2 5, .mu 5 1 5,
  .mu 5 3 5, .mu 5 1 5, .mu 5 2 5, .mu 5 1 5, .mu 5 3 5, .mu 5 1 5, .mu 5 3 5, .mu 5 1 5,
  .mu 5 2 5, .mu 5 1 5, .mu 5 2 5, .mu 5 1 5, .mu 5 3 5, .mu 5 1 5, .mu 5 3 5, .mu 5 1 5,
  .mu 5 3 5, .mu 5 1 5, .mu 5 2 5, .mu 5 1 5, .mu 5 2 5, .mu 5 1 5, .mu 5 3 5, .mu 5 1 5,
  .mu 5 2 5, .mu 5 1 5, .mu 5 2 5, .mu 5 1 5, .mu 5 2 5, .mu 5 1 5, .mu 5 2 5, .mu 5 1 5,
  .mu 5 2 5, .mu 5 1 5, .mu 5 3 5, .mu 5 1 5, .mu 5 2 5, .mu 5 1 5, .mu 5 2 5, .mu 5 1 5,
  .pwr 1 3 6, .mu 6 1 6, .mu 6 3 6, .mu 6 1 6, .mu 6 2 6, .mu 6 1 6, .mu 6 3 6, .mu 6 1 6,
  .mu 6 2 6, .mu 6 1 6, .mu 6 2 6, .mu 6 1 6, .mu 6 2 6, .mu 6 1 6, .mu 6 2 6, .mu 6 1 6,
  .mu 6 2 6, .mu 6 1 6, .mu 6 2 6, .mu 6 1 6, .mu 6 2 6, .mu 6 1 6, .mu 6 3 6, .mu 6 1 6,
  .mu 6 3 6, .mu 6 1 6, .mu 6 3 6, .mu 6 1 6, .mu 6 2 6, .mu 6 1 6, .mu 6 3 6, .mu 6 1 6,
  .mu 6 2 6, .mu 6 1 6, .mu 6 2 6, .mu 6 1 6, .mu 6 3 6, .mu 6 1 6, .mu 6 2 6, .mu 6 1 6,
  .mu 6 2 6, .mu 6 1 6, .mu 6 2 6, .mu 6 1 6, .mu 6 3 6, .mu 6 1 6, .mu 6 2 6, .mu 6 1 6,
  .mu 6 2 6, .mu 6 1 6, .mu 6 2 6, .mu 6 1 6, .mu 6 3 6, .mu 6 1 6, .mu 6 3 6, .mu 6 1 6,
  .mu 6 2 6, .mu 6 1 6, .mu 6 2 6, .mu 6 1 6, .mu 6 2 6, .mu 6 1 6, .mu 6 2 6, .mu 6 1 6,
  .mu 6 2 6, .mu 6 1 6, .mu 6 2 6, .mu 6 1 6, .mu 6 3 6, .mu 6 1 6, .mu 6 2 6, .mu 6 1 6,
  .mu 6 3 6, .mu 6 1 6, .mu 6 3 6, .mu 6 1 6, .mu 6 2 6, .mu 6 1 6, .mu 6 2 6, .mu 6 1 6,
  .mu 6 3 6, .mu 6 1 6, .mu 6 3 6, .mu 6 1 6, .mu 6 2 6, .mu 6 1 6, .mu 6 2 6, .mu 6 1 6,
  .mu 6 2 6, .mu 6 1 6, .mu 6 2 6, .mu 6 1 6, .mu 6 2 6, .mu 6 1 6, .mu 6 2 6, .mu 6 1 6,
  .mu 6 2 6, .mu 6 1 6, .mu 6 3 6, .mu 6 1 6, .mu 6 2 6, .mu 6 1 6, .mu 6 3 6, .mu 6 1 6,
  .mu 6 2 6, .mu 6 1 6, .mu 6 2 6, .mu 6 1 6, .mu 6 3 6, .mu 6 1 6, .mu 6 3 6, .mu 6 1 6,
  .mu 6 3 6, .mu 6 1 6, .mu 6 3 6, .mu 6 1 6, .mu 6 2 6, .mu 6 1 6, .mu 6 2 6, .mu 6 1 6,
  .mu 4 4 7, .mu 6 5 8, .mu 7 8 9, .mu 9 9 10, .iv 10 11, .iv 4 12, .mu 11 12 13, .mu 13 10 14,
  .mu 14 4 15, .iv 5 16, .mu 11 16 17, .mu 17 10 18, .mu 18 5 19, .iv 15 20, .iv 19 21,
  .mu 20 21 22, .mu 22 15 23, .mu 23 19 24, .mu 4 6 25]

@[expose] def co1Data : Data 2 where
  prog := co1Prog
  nreg := 26
  iQ := ![15, 19]
  iZ := 24
  iS := 25
  iT := 10
  zWit := 0
  exM := ![![0, 1], ![4, 0]]
  exS := ![![1, 4], ![0, 1]]
  cs := ![0, 3]
  rT := 2
  ct := ![1, 3]
  e5 := ![0, 0]
  c5 := 0
  eTS := ![3, 4]
  cTS := 0

@[expose] def co1Regs : Array (Array ℕ × Array ℕ) :=
  runProgN (ops2 24) (initRegsN (ops2 24) co1Data.nreg
    ((ops2 24).decode NativeSporadic.Co1Seed1, (ops2 24).decode NativeSporadic.Co1Seed1)
    ((ops2 24).decode NativeSporadic.Co1Seed2,
      (ops2 24).pow ((ops2 24).decode NativeSporadic.Co1Seed2) 2)) co1Data.prog

@[expose] def co1ScalCheck : Bool :=
  co1Data.prog.all (Instr.lt co1Data.nreg) &&
    powOK (ops2 24) ((ops2 24).decode NativeSporadic.Co1Seed1) 2 &&
    powOK (ops2 24) ((ops2 24).decode NativeSporadic.Co1Seed2) 3 &&
    relsOK (ops2 24) co1Data co1Regs

end CFSG.RankThree.PartOne.KS.Co1Scal

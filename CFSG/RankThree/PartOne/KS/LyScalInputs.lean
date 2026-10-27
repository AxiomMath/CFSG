module

public import CFSG.Sporadic.GLQ.RegisterProgram
public meta import CFSG.Sporadic.GLQ.RegisterProgram
public import CFSG.LocalAnalysis.SectionRank.Sporadic.OpsFp
public meta import Certificates.Data.CFSGNative.SectionRank.Fp
public import CFSG.Blueprint.MatrixSeedIdentification
import CFSG.Blueprint.NativeSporadic
public import CFSG.RankThree.PartOne.KS.ScalFiveDefs
public meta import CFSG.RankThree.PartOne.KS.ScalFiveDefs

public section

namespace CFSG.RankThree.PartOne.KS.LyScal

open CFSG.SectionRank CFSG.SectionRank.Native CFSG.Blueprint CFSG.Sporadic.GLQ
  CFSG.RankThree.PartOne.KS.ScalFive

@[expose] def lyProg : List Instr := [
  .mu 1 2 3, .mu 3 2 4, .mu 3 4 5, .mu 3 5 6, .mu 6 5 8, .mu 3 8 9, .mu 9 4 10, .pwr 7 3 4,
  .mu 4 10 5, .mu 10 4 6, .iv 6 7, .mu 7 5 6, .pwr 10 6 7, .mu 10 7 12, .mu 1 1 4, .mu 4 3 11,
  .mu 11 12 3, .mu 3 12 4, .pwr 5 3 5, .mu 5 5 6, .iv 4 3, .mu 4 6 7, .mu 7 3 6, .iv 6 7,
  .mu 7 5 8, .mu 8 6 5, .iv 2 3, .pwr 4 5 6, .mu 3 6 7, .mu 7 2 6, .mu 4 5 7, .mu 7 5 8, .mu 7 8 9,
  .mu 7 9 10, .mu 10 9 8, .mu 8 8 7, .mu 6 7 8, .pwr 11 8 10, .mu 2 10 9, .iv 9 8, .mu 8 11 10,
  .mu 10 9 11, .mu 8 12 10, .mu 10 9 12, .mu 11 12 3, .pwr 8 3 6, .mu 3 12 7, .mu 3 7 8, .mu 3 8 7,
  .pwr 5 7 8, .mu 8 6 7, .iv 7 8, .mu 8 6 9, .mu 9 7 10, .mu 4 10 1, .mu 7 5 6, .mu 8 6 2,
  .mu 2 2 13, .iv 13 14, .iv 1 15, .mu 1 1 16, .mu 15 2 17, .iv 17 18, .iv 16 19, .mu 14 15 20,
  .mu 20 13 21, .mu 21 1 22, .mu 14 18 23, .mu 23 13 24, .mu 24 17 25, .mu 14 1 26, .mu 26 13 27,
  .mu 27 15 28, .mu 14 19 29, .mu 29 13 30, .mu 30 16 31, .iv 22 32, .iv 25 33, .mu 32 33 34,
  .mu 34 22 35, .mu 35 25 36]

@[expose] def lyData : Data 4 where
  prog := lyProg
  nreg := 37
  iQ := ![22, 25, 28, 31]
  iZ := 36
  iS := 1
  iT := 13
  zWit := 0
  exM := ![![0, 1, 0, 0], ![4, 0, 2, 1], ![0, 3, 0, 1], ![0, 4, 4, 0]]
  exS := ![![4, 0, 0, 1], ![1, 2, 0, 4], ![4, 0, 0, 0], ![4, 4, 2, 3]]
  cs := ![0, 0, 0, 1]
  rT := 2
  ct := ![4, 3, 1, 3]
  e5 := ![0, 0, 0, 0]
  c5 := 3
  eTS := ![1, 0, 0, 0]
  cTS := 0

@[expose] def lyRegs : Array (Array (Array ℕ) × Array (Array ℕ)) :=
  runProgN (opsP 5 111) (initRegsN (opsP 5 111) lyData.nreg
    ((opsP 5 111).decode NativeSporadic.LySeed1, (opsP 5 111).decode NativeSporadic.LySeed1)
    ((opsP 5 111).decode NativeSporadic.LySeed2,
      (opsP 5 111).pow ((opsP 5 111).decode NativeSporadic.LySeed2) 4)) lyData.prog

@[expose] def lyScalCheck : Bool :=
  lyData.prog.all (Instr.lt lyData.nreg) && relsOK (opsP 5 111) lyData lyRegs

end CFSG.RankThree.PartOne.KS.LyScal

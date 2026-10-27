module

public import Certificates.Data.CFSGNative.SectionRank.Local
public import Certificates.Data.CFSGNative.SectionRank.F2

public section

namespace CFSG.RankThree.PartTwo.Sec4.Census.DoubleCoverRanks.Native

open CFSG.SectionRank.Native

set_option compiler.extract_closed false

structure E8Data where
  seedA : String
  seedB : String
  nregs : Nat
  prog : List Op
  rx : Nat
  rh : Nat
  oh : Nat
  t : Nat

@[expose] def e8Check {M V : Type} (O : Ops M V) [Inhabited M] [Inhabited V] (D : E8Data) :
    Bool :=
  let R := O.regsOf D.seedA D.seedB D.nregs D.prog
  let X := R[D.rx]!
  let H := R[D.rh]!
  let H' := O.pow H (D.oh - 1)
  let X₂ := O.mul (O.mul H X) H'
  let X₃ := O.mul (O.mul H X₂) H'
  decide (2 ≤ D.nregs) && D.prog.all (Op.lt D.nregs) && decide (D.rx < D.nregs) &&
    decide (D.rh < D.nregs) && decide (0 < D.oh) && O.eq (O.pow X 2) O.one &&
    O.eq (O.pow H D.oh) O.one && O.vne (O.vmul (O.unit D.t) X) (O.unit D.t) &&
    O.eq (O.mul X X₂) (O.mul X₂ X) && O.eq (O.mul X X₃) (O.mul X₃ X) &&
    O.conjOK H X₃ (O.mul X X₂)

@[expose] def hsE8Data : E8Data where
  seedA := include_str "../../CFSG/Blueprint/Data/HSG1-f2r20B0.m1"
  seedB := include_str "../../CFSG/Blueprint/Data/HSG1-f2r20B0.m2"
  nregs := 24
  prog := [
      .pow 2 1 2, .pow 3 1 3, .pow 4 1 4, .mul 0 4 5, .mul 5 0 6, .mul 6 3 7, .mul 7 0 8,
      .mul 8 1 9, .mul 9 0 10, .mul 10 4 11, .mul 11 0 12, .mul 12 1 13, .mul 13 0 14,
      .mul 14 2 15, .mul 0 4 16, .mul 16 0 17, .mul 17 3 18, .mul 18 0 19, .mul 19 2 20,
      .mul 20 0 21, .mul 21 1 22, .pow 2 22 23]
  rx := 23
  rh := 15
  oh := 7
  t := 0

@[expose] def ruE8Data : E8Data where
  seedA := include_str "../../CFSG/Blueprint/Data/RuG1-f2r28B0.m1"
  seedB := include_str "../../CFSG/Blueprint/Data/RuG1-f2r28B0.m2"
  nregs := 34
  prog := [
      .pow 2 1 2, .pow 3 1 3, .mul 0 3 4, .mul 4 0 5, .mul 5 1 6, .mul 6 0 7, .mul 7 2 8,
      .mul 8 0 9, .mul 9 1 10, .mul 10 0 11, .mul 11 2 12, .pow 2 12 13, .mul 0 2 14,
      .mul 14 0 15, .mul 15 1 16, .mul 16 0 17, .mul 17 3 18, .mul 18 0 19, .mul 19 1 20,
      .mul 20 0 21, .mul 21 1 22, .mul 22 0 23, .mul 23 2 24, .mul 24 0 25, .mul 25 2 26,
      .mul 26 0 27, .mul 27 2 28, .mul 28 0 29, .mul 29 2 30, .mul 30 0 31, .mul 31 3 32,
      .pow 5 32 33]
  rx := 33
  rh := 13
  oh := 7
  t := 0

end CFSG.RankThree.PartTwo.Sec4.Census.DoubleCoverRanks.Native

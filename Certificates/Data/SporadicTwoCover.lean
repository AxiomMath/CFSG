module

public import Certificates.Data.DoubleCoverRanks
public import Certificates.Data.CFSGNative.SectionRank.F3

public section

namespace CFSG.RankThree.PartTwo.Sec4.Census.SporadicTwoCover.Native

open CFSG.SectionRank.Native CFSG.RankThree.PartTwo.Sec4.Census.DoubleCoverRanks.Native

set_option compiler.extract_closed false

@[expose] def e16Check {M V : Type} (O : Ops M V) [Inhabited M] [Inhabited V] (D : E8Data) :
    Bool :=
  let R := O.regsOf D.seedA D.seedB D.nregs D.prog
  let X := R[D.rx]!
  let H := R[D.rh]!
  let H' := O.pow H (D.oh - 1)
  let X₂ := O.mul (O.mul H X) H'
  let X₃ := O.mul (O.mul H X₂) H'
  let X₄ := O.mul (O.mul H X₃) H'
  decide (2 ≤ D.nregs) && D.prog.all (Op.lt D.nregs) && decide (D.rx < D.nregs) &&
    decide (D.rh < D.nregs) && decide (0 < D.oh) && O.eq (O.pow X 2) O.one &&
    O.eq (O.pow H D.oh) O.one && O.vne (O.vmul (O.unit D.t) X) (O.unit D.t) &&
    O.eq (O.mul X X₂) (O.mul X₂ X) && O.eq (O.mul X X₃) (O.mul X₃ X) &&
    O.eq (O.mul X X₄) (O.mul X₄ X) && O.conjOK H X₄ (O.mul X X₂)

@[expose] def onE8Data : E8Data where
  seedA := include_str "../../CFSG/Blueprint/Data/ONG1-f3r154B0.m1"
  seedB := include_str "../../CFSG/Blueprint/Data/ONG1-f3r154B0.m2"
  nregs := 79
  prog := [
      .pow 3 1 2, .mul 1 0 3, .mul 3 2 4, .mul 4 0 5, .mul 5 1 6, .mul 6 0 7, .mul 7 1 8,
      .mul 8 0 9, .mul 9 2 10, .mul 10 0 11, .mul 11 1 12, .mul 12 0 13, .mul 13 2 14,
      .mul 14 0 15, .mul 15 1 16, .mul 16 0 17, .mul 17 2 18, .mul 18 0 19, .mul 19 1 20,
      .mul 20 0 21, .mul 21 2 22, .mul 22 0 23, .mul 23 2 24, .mul 24 0 25, .mul 25 2 26,
      .mul 26 0 27, .mul 27 2 28, .pow 3 28 29, .mul 0 1 30, .mul 30 0 31, .mul 31 1 32,
      .mul 32 0 33, .mul 33 1 34, .mul 34 1 35, .mul 35 1 36, .mul 36 0 37, .mul 37 1 38,
      .mul 38 1 39, .mul 39 1 40, .mul 40 0 41, .mul 41 1 42, .mul 42 1 43, .mul 43 0 44,
      .mul 44 1 45, .mul 45 0 46, .mul 46 1 47, .mul 47 0 48, .mul 48 1 49, .mul 49 1 50,
      .mul 50 1 51, .mul 51 0 52, .mul 52 1 53, .mul 53 1 54, .mul 54 1 55, .pow 2 55 56,
      .mul 28 56 57, .mul 57 29 58, .pow 2 58 59, .mul 0 59 60, .mul 60 0 61, .mul 61 58 62,
      .mul 62 0 63, .mul 63 59 64, .mul 64 0 65, .mul 65 59 66, .mul 0 58 67, .mul 67 0 68,
      .mul 68 59 69, .mul 69 0 70, .mul 70 58 71, .mul 71 0 72, .mul 72 59 73, .mul 73 0 74,
      .mul 74 59 75, .mul 75 0 76, .mul 76 58 77, .pow 5 77 78]
  rx := 78
  rh := 66
  oh := 7
  t := 0

@[expose] def j3E16Data : E8Data where
  seedA := include_str "../../CFSG/Blueprint/Data/J3G1-f2r80B0.m1"
  seedB := include_str "../../CFSG/Blueprint/Data/J3G1-f2r80B0.m2"
  nregs := 41
  prog := [
      .mul 0 1 2, .mul 2 1 3, .mul 3 0 4, .mul 4 1 5, .mul 5 0 6, .mul 6 1 7, .mul 7 1 8,
      .mul 8 0 9, .mul 9 1 10, .mul 10 1 11, .mul 11 0 12, .mul 12 1 13, .mul 13 0 14,
      .mul 14 1 15, .pow 14 15 16, .mul 0 1 17, .mul 17 0 18, .mul 18 1 19, .mul 19 1 20,
      .mul 20 0 21, .mul 21 1 22, .mul 22 1 23, .mul 23 0 24, .mul 24 1 25, .mul 25 0 26,
      .mul 26 1 27, .mul 27 0 28, .mul 28 1 29, .mul 29 1 30, .mul 30 0 31, .mul 31 1 32,
      .mul 32 0 33, .mul 33 1 34, .mul 34 0 35, .mul 35 1 36, .mul 36 0 37, .mul 37 1 38,
      .mul 38 1 39, .pow 5 39 40]
  rx := 40
  rh := 16
  oh := 15
  t := 0

end CFSG.RankThree.PartTwo.Sec4.Census.SporadicTwoCover.Native

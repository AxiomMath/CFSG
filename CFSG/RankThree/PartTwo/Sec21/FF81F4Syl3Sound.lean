module

public import CFSG.RankThree.PartTwo.Sec21.FF81F4Syl3Check
public import CFSG.LieType.Chevalley.EvenF4ExceptionalRootLayers
public import CFSG.LieType.Simplicity.TitsElements
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434F42Enum

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF81.F4

open CFSG.LieType.Simplicity.TitsBits CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Ree
open CFSG.RankThree.PartTwo.Sec4.Item434F42
open CFSG.RankThree.PartOne.SEITZX (codeBits wordOfCodes letterOfCode)

section Phi

variable
  {K : Type} [Field K] [Finite K] [CharP K ReeTag.F4.prime]
  {D : Syl3Data}

theorem exceptionalAut_evalG (w : List Letter) :
    ReeTag.F4.finiteExceptionalAut K (evalG K w) = evalG K (w.map Letter.flip) := by
  haveI : CharP K 2 := ‹CharP K ReeTag.F4.prime›
  have h := reeAut_evalG (K := K) w
  have h1 := DFunLike.congr_fun
    (ReeTag.finiteReeAut_eq_reeAut (t := ReeTag.F4) (K := K) (a := 0)) (evalG K w)
  have h2 : ReeTag.F4.finiteReeAut K 0 = ReeTag.F4.finiteExceptionalAut K :=
    finiteReeAut_zero_F4
  exact (DFunLike.congr_fun h2 (evalG K w)).symm.trans (h1.trans h)

end Phi

end CFSG.RankThree.PartTwo.Sec21.FF81.F4

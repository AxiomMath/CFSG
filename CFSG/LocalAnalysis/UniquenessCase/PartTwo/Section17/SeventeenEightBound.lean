module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.ACandidateU33
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma53
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma54
public import CFSG.Quasithin.Vol2.Ch10SecKGA318

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17

open Subgroup CFSG.Open CFSG.Quasithin CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

@[expose] def B17_8BoundTwo (D : Data G) (V₀ V : Subgroup G) (hV : Hyp125 D V₀ V) : Prop :=
  ∀ L : Subgroup G, L ∈ calC D.M → IsL3Odd (Bar2 L) 3 →
    bBar (UC22.conjClosure D.M L) D.M V₀ V hV.isElemAbelian ≤ 2

theorem b17_8BoundTwo_holds (h77 : Inputs1719.W4Lem7_7) (hK : Inputs1719.K_L33AutE8)
    (D : Data G) (V₀ V : Subgroup G) (hV : Hyp125 D V₀ V) : B17_8BoundTwo D V₀ V hV := by
  intro L hL hL3
  exact bBar_conjClosure_le_of_aCandLe hV h77 hL
    (aCandLe_two_of_L33 hK (lieModel_barInf_of_L33 hL hL3))

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17

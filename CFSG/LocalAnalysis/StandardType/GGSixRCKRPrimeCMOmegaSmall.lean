module

public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeCMBlockCore
public import CFSG.HardMathSupport.Dickson.Sec6.I1431Fam.OrtHFixed
public import CFSG.RankThree.PartOne.S11d.LieCentralizerPOmega
public import CFSG.LocalAnalysis.StandardType.GGNbrFieldOtherClassicalResU3ThreeSolv
public import CFSG.HardMathSupport.Dickson.Sec6.I1431Fam.KeyAbstract
public import CFSG.HardMathSupport.Dickson.Sec6.I1431Fam.OrtHShell

public section

namespace CFSG.StandardType.RCKRP

open CFSG.Assembly CFSG.StandardType
open CFSG.Open (StatedOmega)

theorem not_isComponentOf_statedOmega_of_card_le_two {K : Type} [Field K] [Finite K] [CharP K 2]
    {ι₁ : Type} [Fintype ι₁] [DecidableEq ι₁] (Φ₁ : QuadraticForm K (ι₁ → K))
    (hΦ₁ : (QuadraticMap.polarBilin Φ₁).Nondegenerate) (h2 : Fintype.card ι₁ ≤ 2)
    (C : Subgroup ↥(StatedOmega ⇑Φ₁)) : ¬ CFSG.Open.IsComponentOf C ⊤ := by
  have hfr : Module.finrank K (ι₁ → K) ≤ 2 := by
    rw [Module.finrank_fintype_fun_eq_card]
    exact h2
  have hcomm : ∀ a b : CFSG.RankThree.Classical2.orthDerived Φ₁, a * b = b * a :=
    fun a b => Subtype.ext
      (CFSG.HardMathSupport.Dickson.Sec6.I1431.t6orth_commute_orthDerived_of_finrank_le_two
        hΦ₁ hfr a.2 b.2)
  have hcommG : ∀ a b : ↥(StatedOmega ⇑Φ₁), a * b = b * a := by
    intro a b
    apply (CFSG.RankThree.PartOne.statedOmegaOrthEquiv (Q := Φ₁) rfl).injective
    rw [map_mul, map_mul]
    exact hcomm _ _
  have hS : Group.IsSolvable ↥(StatedOmega ⇑Φ₁) :=
    Group.isSolvable_of_comm hcommG
  have hS' : Group.IsSolvable (↥(⊤ : Subgroup ↥(StatedOmega ⇑Φ₁))) :=
    Group.isSolvable_of_comm fun a b => Subtype.ext (hcommG a.1 b.1)
  intro hC
  exact CFSG.StandardType.ResU3Three.not_isComponentOf_of_isSolvable (S := ⊤) hS'
    ((CFSG.Assembly.isComponentOf_iff_open).2 hC)

end CFSG.StandardType.RCKRP

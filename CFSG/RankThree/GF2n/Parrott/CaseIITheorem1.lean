module

public import CFSG.RankThree.GF2n.Parrott.CaseIIDouble

public section

namespace CFSG.RankThree.GF2n.Parrott

open CFSG CFSG.Open Subgroup
open CFSG.ComponentClassification.CatFactsSmall.PSp43

variable {G : Type} [Group G] [Finite G] {z : G}

theorem parrott_theorem1_caseII
    (hThm1 : ∀ (G : Type) [Group G] [Finite G] (z : G) (h : Tim79a.ParrottHyp z)
      (hN : ((J z).subgroupOf (H z)).Normal) (D : QuotientData (z := z) hN),
      ParrottEqualityBranch (z := z) (D := D) h → H z ⊔ pPrimeCore 2 G = ⊤)
    (h : Tim79a.ParrottHypA z) (D : QuotientData (z := z) (J_subgroupOf_normal z))
    (heq : ∃ σ₂ : ↥(H z), orderOf σ₂ = 3 ∧
      qH D σ₂ = (⟨sigma2, sigma2_mem_A⟩ : QA45.originalSubgroup) ∧
      centralizerJ (sigma1Nine D) = centralizerJ σ₂) :
    H z ⊔ pPrimeCore 2 G = ⊤ :=
  (CaseIIDouble.H_zz_sup_pPrimeCore_eq_top_iff z).mp
    (hThm1 (CaseIIDouble.D2 G) (CaseIIDouble.zz z) (CaseIIDouble.parrottHyp_zz h)
      (J_subgroupOf_normal (CaseIIDouble.zz z)) (CaseIIDouble.quotientDataZZ D)
      ((CaseIIDouble.parrottEqualityBranch_zz_iff (CaseIIDouble.parrottHyp_zz h) D).mpr heq))

end CFSG.RankThree.GF2n.Parrott

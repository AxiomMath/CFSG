module

public import CFSG.RankThree.GF2n.Parrott.Section2J0NormalJ
public import CFSG.RankThree.GF2n.Parrott.CentralizerJoinH

public section

namespace CFSG.RankThree.GF2n.Parrott

open CFSG CFSG.Open CFSG.ComponentClassification.CatFactsSmall.PSp43

variable {G : Type} [Group G] [Finite G] {z : G}
variable [hN : ((J z).subgroupOf (H z)).Normal]
variable (D : QuotientData (z := z) hN)

theorem J0sub_normal (h : Tim79a.ParrottHyp z) {σ₂ : ↥(H z)}
    (hEq : centralizerJ (sigma1Nine (z := z) D) = centralizerJ σ₂)
    (hs₂ : orderOf σ₂ = 3)
    (hq₂ : qH D σ₂ = (⟨sigma2, sigma2_mem_A⟩ : QA45.originalSubgroup)) :
    (J0sub (z := z) (D := D)).Normal := by
  have hgen := sup_J_normalizer_centralizer_eq_top (z := z) (D := D)
    (sigma1Nine_order (z := z) D) (qH_sigma1Nine (z := z) D) hs₂ hq₂
  have hgen' : (Subgroup.normalizer
        (Subgroup.zpowers (sigma1Nine (z := z) D) : Set ↥(H z)) ⊔
      Subgroup.centralizer ({σ₂} : Set ↥(H z))) ⊔ ((J z).subgroupOf (H z)) = ⊤ := by
    rw [← hgen]
    ac_rfl
  exact J0sub_normal_of_generation' (z := z) (D := D) h σ₂ hEq hgen'

end CFSG.RankThree.GF2n.Parrott

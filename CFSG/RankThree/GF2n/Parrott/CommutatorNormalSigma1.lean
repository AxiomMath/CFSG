module

public import CFSG.RankThree.GF2n.Parrott.CentralizerJoinH
public import CFSG.RankThree.GF2n.Parrott.Section3Lift
public import CFSG.RankThree.GF2n.Parrott.CommutatorCentralizer

public section

namespace CFSG.RankThree.GF2n.Parrott

open CFSG CFSG.Open CFSG.ComponentClassification.CatFactsSmall.PSp43

variable {G : Type} [Group G] [Finite G] {z : G}
variable [hN : ((J z).subgroupOf (H z)).Normal]
variable (D : QuotientData (z := z) hN)

theorem conjZ_eq_one_of_qH_eq_sigma2 (h : Tim79a.ParrottHyp z) {σ₂ : ↥(H z)}
    (hq₂ : qH D σ₂ = (⟨sigma2, sigma2_mem_A⟩ : QA45.originalSubgroup)) :
    conjZ z σ₂ = 1 := by
  have hker : σ₂ * (sigma2Nine (z := z) D)⁻¹ ∈ (J z).subgroupOf (H z) := by
    rw [← ker_qH D, MonoidHom.mem_ker, map_mul, map_inv, hq₂, qH_sigma2Nine, mul_inv_cancel]
  have h1 : conjZ z (σ₂ * (sigma2Nine (z := z) D)⁻¹) = 1 :=
    MonoidHom.mem_ker.mp (J_le_ker_conjZ z hker)
  have h2 : σ₂ = (σ₂ * (sigma2Nine (z := z) D)⁻¹) * sigma2Nine (z := z) D := by group
  rw [h2, map_mul, h1, conjZ_sigma2Nine h D, one_mul]

theorem commutator_sigma1Nine_conj_mem (h : Tim79a.ParrottHyp z) {σ₂ : ↥(H z)}
    (hEq : centralizerJ (sigma1Nine (z := z) D) = centralizerJ σ₂)
    (hs₂ : orderOf σ₂ = 3)
    (hq₂ : qH D σ₂ = (⟨sigma2, sigma2_mem_A⟩ : QA45.originalSubgroup))
    (hc₂ : σ₂ * sigma1Nine (z := z) D = sigma1Nine (z := z) D * σ₂)
    (g : ↥(H z)) (p : G)
    (hp : p ∈ ⁅(Subgroup.zpowers (sigma1Nine (z := z) D)).map (H z).subtype, J z⁆) :
    (g : G) * p * (g : G)⁻¹ ∈
      ⁅(Subgroup.zpowers (sigma1Nine (z := z) D)).map (H z).subtype, J z⁆ := by
  have hZ₂ := conjZ_eq_one_of_qH_eq_sigma2 (z := z) D h hq₂
  exact commutator_normal_of_generation h (sigma1Nine_order (z := z) D) hs₂
    (conjZ_sigma1Nine h D) hZ₂
    (conjV_ne_one_of_order_three h (sigma1Nine_order (z := z) D) (conjZ_sigma1Nine h D))
    (conjV_ne_one_of_order_three h hs₂ hZ₂) hc₂ hEq
    (sup_J_normalizer_centralizer_eq_top (z := z) (D := D) (sigma1Nine_order (z := z) D)
      (qH_sigma1Nine (z := z) D) hs₂ hq₂) g p hp

end CFSG.RankThree.GF2n.Parrott

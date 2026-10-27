module

public import CFSG.RankThree.PartTwo.Sec21.FF81S58Base
public import CFSG.RankThree.PartTwo.Sec21.FF81S58Gen
import CFSG.RankThree.PartTwo.Sec21.FF81Step0
import CFSG.RankThree.PartTwo.Sec21.FF81Sec32A
public import CFSG.RankThree.PartTwo.Sec21.FF81S59

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF81.S58

open CFSG CFSG.RankThree.PartTwo.Sec21 CFSG.RankThree.PartTwo.Sec21.FF79
open CFSG.Assembly.LowTwoRank (StatedClassicalModel)

variable {G : Type} [Group G] [Finite G] {b : G} {L B : Subgroup G} {b₁ b₂ b₃ t₀ s₀ : G}
  {M : Subgroup G}

theorem nonempty_mulEquiv_cen_b (hB : FF81Basis b L B b₁ b₂ b₃) (h0 : Opp 3 (Cen b) = ⊥) :
    Nonempty (↥(Cen b) ≃* (↥(Subgroup.zpowers b) × ↥L)) := by
  refine nonempty_mulEquiv_prod (Subgroup.zpowers_le.mpr (b_mem_cen b)) hB.hyp.hLC
    (fun p hp q hq => ?_) hB.hyp.zpowers_inf_L (fun x hx => ?_)
  · obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hp
    exact (comm_zpow_of_mem_cen (hB.hyp.hLC hq) k).symm
  · obtain ⟨l, hl, hd⟩ := hB.hyp.exists_decomp hx
    have hdb : l⁻¹ * x ∈ Subgroup.zpowers b := by
      rw [← hB.cen_inf_cenS_eq h0]; exact hd
    refine ⟨l⁻¹ * x, hdb, l, hl, ?_⟩
    have hc : (l⁻¹ * x) * l = l * (l⁻¹ * x) := by
      have := Subgroup.mem_centralizer_iff.mp hd.2 l hl
      exact this.symm
    calc x = l * (l⁻¹ * x) := by group
      _ = (l⁻¹ * x) * l := hc.symm

theorem card_cen_b (hB : FF81Basis b L B b₁ b₂ b₃) (h0 : Opp 3 (Cen b) = ⊥) :
    Nat.card ↥(Cen b) = 3 * 1451520 := by
  obtain ⟨e⟩ := nonempty_mulEquiv_cen_b hB h0
  rw [Nat.card_congr e.toEquiv, Nat.card_prod, hB.hyp.card_zpowers, hB.hyp.card_L]

theorem zpowers_β_le_nor_M (hM7 : FF81Conc5_7 b b₁ b₂ b₃ s₀ M) :
    Subgroup.zpowers (β' b₂ b₃) ≤ Nor M := fun y hy => by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
  refine Subgroup.mem_normalizer_fintype fun m hm => ?_
  have hc : m * β' b₂ b₃ = β' b₂ b₃ * m :=
    Subgroup.mem_centralizer_singleton_iff.mp (M_le_cen_β hM7 hm)
  rw [(Commute.zpow_left (show Commute (β' b₂ b₃) m from hc.symm) k).eq, mul_inv_cancel_right]
  exact hm

theorem cen_β_le_nor_M (hM7 : FF81Conc5_7 b b₁ b₂ b₃ s₀ M) : Cen (β' b₂ b₃) ≤ Nor M := by
  rw [← hM7.2.2.2.1]
  exact sup_le (zpowers_β_le_nor_M hM7) Subgroup.le_normalizer

theorem nonempty_mulEquiv_cen_β (hM7 : FF81Conc5_7 b b₁ b₂ b₃ s₀ M) :
    Nonempty (↥(Cen (β' b₂ b₃)) ≃* (↥(Subgroup.zpowers (β' b₂ b₃)) × ↥M)) := by
  have hMC : M ≤ Cen (β' b₂ b₃) := M_le_cen_β hM7
  refine nonempty_mulEquiv_prod (Subgroup.zpowers_le.mpr (b_mem_cen (β' b₂ b₃))) hMC
    (fun p hp q hq => ?_) hM7.2.2.2.2.1 (fun x hx => ?_)
  · obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hp
    exact (comm_zpow_of_mem_cen (hMC hq) k).symm
  · have hx' : x ∈ (↑(Subgroup.zpowers (β' b₂ b₃) ⊔ M) : Set G) := by
      rw [hM7.2.2.2.1]; exact hx
    rw [Subgroup.coe_mul_of_left_le_normalizer_right _ _ (zpowers_β_le_nor_M hM7)] at hx'
    obtain ⟨p, hp, q, hq, rfl⟩ := hx'
    exact ⟨p, hp, q, hq, rfl⟩

theorem nonempty_mulEquiv_cen_cen (hB : FF81Basis b L B b₁ b₂ b₃) (h0 : Opp 3 (Cen b) = ⊥)
    (hM7 : FF81Conc5_7 b b₁ b₂ b₃ s₀ M) :
    Nonempty (↥(Cen b) ≃* ↥(Cen (β' b₂ b₃))) := by
  obtain ⟨e1⟩ := nonempty_mulEquiv_cen_b hB h0
  obtain ⟨e2⟩ := nonempty_mulEquiv_cen_β hM7
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hz1 : Nat.card (Subgroup.zpowers b) = 3 := hB.hyp.card_zpowers
  have hz2 : Nat.card (Subgroup.zpowers (β' b₂ b₃)) = 3 := by
    rw [Nat.card_zpowers, S59.orderOf_β hB]
  let ez := mulEquivOfPrimeCardEq hz1 hz2
  obtain ⟨eL⟩ := nonempty_mulEquiv_H6_of_stated hB.hyp.model
  obtain ⟨eM⟩ := nonempty_mulEquiv_H6_of_stated hM7.2.1
  exact ⟨e1.trans ((ez.prodCongr (eL.trans eM.symm)).trans e2.symm)⟩

end CFSG.RankThree.PartTwo.Sec21.FF81.S58

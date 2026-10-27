module

public import CFSG.RankThree.PartTwo.Sec21.FF79Lemma13a
public import CFSG.RankThree.PartTwo.Sec21.FF79KFacts13
public import CFSG.RankThree.PartTwo.Sec21.FF79Lemma13bFus

import CFSG.Foundations.QuasisimpleMulEquiv

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF79.L13b

open CFSG CFSG.RankThree.PartTwo.Sec21

variable {G : Type} [Group G]

structure Data (b : G) (J B : Subgroup G) : Prop where
  ord : orderOf b = 3
  hB : IsSylowOf 3 B (Cen b)
  hJC : J ≤ Cen b
  hE : IsElemAb 3 3 B
  hB0 : IsElemAb 3 2 (B ⊓ J)
  hsup : Subgroup.zpowers b ⊔ (B ⊓ J) = B
  hbJ : b ∉ J
  hab : ∀ x ∈ B, ∀ y ∈ B, x * y = y * x
  hbB : b ∈ B
  hnormJ : ∀ k : G, (k * b * k⁻¹ = b ∨ k * b * k⁻¹ = b⁻¹) → ∀ j ∈ J, k * j * k⁻¹ ∈ J
  hB0syl : IsSylowOf 3 (B ⊓ J) J
  hτ : ∃ τ ∈ J, τ ∈ Nor (B ⊓ J) ∧ ∀ x ∈ B ⊓ J, τ * x * τ⁻¹ = x⁻¹
  hcard : {f : ↥(B ⊓ J) → G | ∃ j ∈ J, j ∈ Nor (B ⊓ J) ∧
    ∀ x : ↥(B ⊓ J), f x = j * x * j⁻¹}.ncard = 8
  hnab : ∃ j₁ ∈ J, ∃ j₂ ∈ J, j₁ ∈ Nor (B ⊓ J) ∧ j₂ ∈ Nor (B ⊓ J) ∧
    ∃ x ∈ B ⊓ J, j₁ * (j₂ * x * j₂⁻¹) * j₁⁻¹ ≠ j₂ * (j₁ * x * j₁⁻¹) * j₂⁻¹
  hlast : ∀ g ∈ Nor J, g ∈ Nor (B ⊓ J) →
    ∃ j ∈ J, j ∈ Nor (B ⊓ J) ∧ ∀ x ∈ B ⊓ J, g * x * g⁻¹ = j * x * j⁻¹
  hnsc : FFNotStronglyClosed b

theorem Data.of_hyp [Finite G] (hK : FF79KTypeLn) (hN : FF79KTypeLnNorm) {n : ℕ}
    (hn : n = 4 ∨ n = 5) {b : G} {J : Subgroup G} (h : FF79Hyp n b J) {B : Subgroup G}
    (hB : IsSylowOf 3 B (Cen b)) : Data b J B := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨hE, hB0, hsup, hBcen⟩ := ff79_1_3_struct hK hn h hB
  obtain ⟨hJC, hcomp, huniq⟩ := h.std
  have hJq : CFSG.IsQuasisimple ↥J :=
    CFSG.IsQuasisimple.of_mulEquiv (Subgroup.subgroupOfEquivOfLe hJC).symm hcomp.1
  obtain ⟨hZ3, hSyl, -⟩ := hK G n J hn hJq h.model
  have h3J := three_dvd_card_of_sylow hSyl
  have hbB : b ∈ B := by
    have : b ∈ Subgroup.zpowers b ⊔ (B ⊓ J) := Subgroup.mem_sup_left (Subgroup.mem_zpowers b)
    rwa [hsup] at this
  have hbcen : b ∈ CenS J := by
    have : b ∈ B ⊓ CenS J := by rw [hBcen]; exact Subgroup.mem_zpowers b
    exact this.2
  have hbJ : b ∉ J := by
    intro hbJ
    have hz : (⟨b, hbJ⟩ : ↥J) ∈ Subgroup.center ↥J := by
      rw [Subgroup.mem_center_iff]
      intro g
      exact Subtype.ext (Subgroup.mem_centralizer_iff.mp hbcen g g.2)
    have h1 : orderOf (⟨b, hbJ⟩ : ↥J) ∣ Nat.card ↥(Subgroup.center ↥J) := by
      have := orderOf_dvd_natCard (⟨(⟨b, hbJ⟩ : ↥J), hz⟩ : ↥(Subgroup.center ↥J))
      simpa [Subgroup.orderOf_mk] using this
    rw [Subgroup.orderOf_mk, h.ord] at h1
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp hZ3 h1
  have hnormJ : ∀ k : G, (k * b * k⁻¹ = b ∨ k * b * k⁻¹ = b⁻¹) → ∀ j ∈ J, k * j * k⁻¹ ∈ J :=
    fun k hk j hj => conj_mem_J ⟨hJC, hcomp, huniq⟩ h3J (cen_conj_iff hk) hj
  have hB0syl : IsSylowOf 3 (B ⊓ J) J := by
    refine isSylowOf_inf_normal hB hJC fun g hg j hj => hnormJ g ?_ j hj
    left
    have := mem_cen_iff'.mp hg
    calc g * b * g⁻¹ = b * g * g⁻¹ := by rw [this]
      _ = b := by group
  haveI : IsElementaryAbelian 3 ↥B := hE.1
  have hab : ∀ x ∈ B, ∀ y ∈ B, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val ((IsMulCommutative.is_comm (M := ↥B)).comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hN' := hN G n J (B ⊓ J) hn hJq h.model inf_le_right hB0syl
  exact ⟨h.ord, hB, hJC, hE, hB0, hsup, hbJ, hab, hbB, hnormJ, hB0syl, hN'.1, hN'.2.1,
    hN'.2.2.1, hN'.2.2.2, h.nsc⟩

end CFSG.RankThree.PartTwo.Sec21.FF79.L13b

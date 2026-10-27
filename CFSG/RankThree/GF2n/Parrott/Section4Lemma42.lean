module

public import CFSG.RankThree.GF2n.Parrott.Section4Lemma42Steps
public import CFSG.RankThree.GF2n.Parrott.Section1

public section

namespace CFSG.RankThree.GF2n.Parrott

open CFSG CFSG.Open CFSG.ABGLocalTools CFSG.GroupTheory Subgroup

variable {G : Type} [Group G] [Finite G] {z : G}

theorem mem_centerIn_J_iff (h : Tim79a.ParrottHyp z) {z₁ : G} (hz₁ : z₁ ∈ centerIn (J z))
    (hz₁z : z₁ ∉ Subgroup.zpowers z) (hord : orderOf z₁ = 2) {e : G} :
    e ∈ centerIn (J z) ↔ e = 1 ∨ e = z ∨ e = z₁ ∨ e = z * z₁ := by
  have hz2 : orderOf z = 2 := h.1
  have hzA : z ∈ centerIn (J z) := z_mem_centerIn_J h
  have hcomm : Commute z z₁ := by
    exact Subgroup.mem_centralizer_iff.mp hz₁.2 z (z_mem_J h)
  have hdisj : Subgroup.zpowers z ⊓ Subgroup.zpowers z₁ = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    rw [Subgroup.mem_bot]
    rcases CFSG.GF2Type.Aschbacher1976Full.Z4Q8.mem_zpowers_two hord hx.2 with h1 | h1
    · exact h1
    · exact absurd (h1 ▸ hx.1) hz₁z
  have hB : Subgroup.zpowers z ⊔ Subgroup.zpowers z₁ = centerIn (J z) := by
    apply Subgroup.eq_of_le_of_card_ge
    · exact sup_le (Subgroup.zpowers_le.mpr hzA) (Subgroup.zpowers_le.mpr hz₁)
    · rw [CFSG.card_sup_eq_mul_of_commute (Subgroup.zpowers z) (Subgroup.zpowers z₁)
        (fun a ha b hb => by
          obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
          obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
          exact (hcomm.zpow_left i).zpow_right k) hdisj, Nat.card_zpowers, Nat.card_zpowers,
        hz2, hord, card_centerIn_J h]
  constructor
  · intro he
    rw [← hB] at he
    have hcm : ∀ a ∈ Subgroup.zpowers z, ∀ b ∈ Subgroup.zpowers z₁, Commute a b := by
      intro a ha b hb
      obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
      exact (hcomm.zpow_left i).zpow_right k
    obtain ⟨a, ha, b, hb, rfl⟩ := (CFSG.mem_sup_of_commute hcm).mp he
    rcases CFSG.GF2Type.Aschbacher1976Full.Z4Q8.mem_zpowers_two hz2 ha with rfl | rfl <;>
      rcases CFSG.GF2Type.Aschbacher1976Full.Z4Q8.mem_zpowers_two hord hb with rfl | rfl <;>
      simp
  · rintro (rfl | rfl | rfl | rfl)
    · exact Subgroup.one_mem _
    · exact hzA
    · exact hz₁
    · exact Subgroup.mul_mem _ hzA hz₁

section Certified


theorem lemma42_of_noFusion (h : Tim79a.ParrottHyp z) (hZ : centerIn (J z) = centerIn (H z))
    (hne : H z ⊔ pPrimeCore 2 G ≠ ⊤) {z₁ : G} (hz₁ : z₁ ∈ centerIn (J z))
    (hz₁z : z₁ ∉ Subgroup.zpowers z) (hord : orderOf z₁ = 2)
    (hNF : (∀ g : G, (g ∈ centralizer ({z₁} : Set G) ∨ g ∈ centralizer ({z * z₁} : Set G)) →
        g * z * g⁻¹ ∈ H z → g * z * g⁻¹ = z) →
      ∀ y : G, y ∈ H z → y ∉ J z → orderOf y = 2 → ¬ IsConj z y) :
    ∃ g : G, (g ∈ centralizer ({z₁} : Set G) ∨ g ∈ centralizer ({z * z₁} : Set G)) ∧
      g * z * g⁻¹ ∈ H z ∧ g * z * g⁻¹ ∉ Subgroup.zpowers z := by
  have hz2 : orderOf z = 2 := h.1
  have hconjord : ∀ g : G, orderOf (g * z * g⁻¹) = 2 := fun g => by
    rw [← MulAut.conj_apply, MulEquiv.orderOf_eq]
    exact hz2
  by_contra hcon
  have hA : ∀ g : G, (g ∈ centralizer ({z₁} : Set G) ∨ g ∈ centralizer ({z * z₁} : Set G)) →
      g * z * g⁻¹ ∈ H z → g * z * g⁻¹ = z := by
    intro g hg hgH
    by_contra hne'
    apply hcon
    refine ⟨g, hg, hgH, fun hmem => ?_⟩
    rcases CFSG.GF2Type.Aschbacher1976Full.Z4Q8.mem_zpowers_two hz2 hmem with h1 | h1
    · have := hconjord g
      rw [h1, orderOf_one] at this
      exact absurd this (by norm_num)
    · exact hne' h1
  have hAe : ∀ g : G, (∃ e ∈ centerIn (J z), e ≠ 1 ∧ e ≠ z ∧ g ∈ centralizer ({e} : Set G)) →
      g * z * g⁻¹ ∈ J z → g * z * g⁻¹ = z := by
    rintro g ⟨e, he, he1, hez, hge⟩ hgJ
    rcases (mem_centerIn_J_iff h hz₁ hz₁z hord).mp he with rfl | rfl | rfl | rfl
    · exact absurd rfl he1
    · exact absurd rfl hez
    · exact hA g (Or.inl hge) (J_le_H hgJ)
    · exact hA g (Or.inr hge) (J_le_H hgJ)
  apply hne
  refine prop2_eq_centralizer_mul_oddCore hz2 ?_
  intro g hcomm
  by_contra hgz
  have hyH : g * z * g⁻¹ ∈ H z := mem_centralizer_singleton_iff.mpr hcomm
  have hconj : IsConj z (g * z * g⁻¹) := isConj_iff.mpr ⟨g, rfl⟩
  by_cases hyJ : g * z * g⁻¹ ∈ J z
  · have hyz : g * z * g⁻¹ ∉ Subgroup.zpowers z := fun hm => by
      rcases CFSG.GF2Type.Aschbacher1976Full.Z4Q8.mem_zpowers_two hz2 hm with h1 | h1
      · have := hconjord g
        rw [h1, orderOf_one] at this
        exact absurd this (by norm_num)
      · exact hgz h1
    exact not_isConj_of_mem_J h hZ hAe hyJ hyz hconj
  · exact hNF hA _ hyH hyJ (hconjord g) hconj

end Certified

end CFSG.RankThree.GF2n.Parrott

module

public import CFSG.RankThree.GF2n.Parrott.Section4Lemma45

public section

namespace CFSG.RankThree.GF2n.Parrott

open CFSG CFSG.Open CFSG.ABGLocalTools CFSG.GroupTheory Subgroup
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {z : G}

theorem commutator_sup_zpowers_eq_commutator_sup_centerIn (h : Tim79a.ParrottHyp z) {z₁ : G}
    (hz₁ : z₁ ∈ centerIn (J z)) (hz₁z : z₁ ∉ Subgroup.zpowers z) (hz₁2 : orderOf z₁ = 2) :
    ⁅H z, H z⁆ ⊔ Subgroup.zpowers z₁ = ⁅H z, H z⁆ ⊔ centerIn (J z) := by
  have hsub : ⁅H z, H z⁆ ⊔ Subgroup.zpowers z₁ ≤ ⁅H z, H z⁆ ⊔ centerIn (J z) :=
    sup_le_sup_left (Subgroup.zpowers_le.mpr hz₁) _
  have hzH' : z ∈ ⁅H z, H z⁆ := by
    have h1 : z ∈ ⁅J z, J z⁆ := by
      rw [show ⁅J z, J z⁆ = Subgroup.zpowers z from h.2.2.1]
      exact Subgroup.mem_zpowers z
    exact Subgroup.commutator_mono (J_le_H (z := z)) (J_le_H (z := z)) h1
  have hZsub : centerIn (J z) ≤ ⁅H z, H z⁆ ⊔ Subgroup.zpowers z₁ := by
    intro e he
    rcases (mem_centerIn_J_iff h hz₁ hz₁z hz₁2).mp he with h1 | h1 | h1 | h1
    · rw [h1]
      exact Subgroup.one_mem _
    · rw [h1]
      exact Subgroup.mem_sup_left hzH'
    · rw [h1]
      exact Subgroup.mem_sup_right (Subgroup.mem_zpowers z₁)
    · rw [h1]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hzH')
        (Subgroup.mem_sup_right (Subgroup.mem_zpowers z₁))
  exact le_antisymm hsub (sup_le le_sup_left hZsub)

theorem centralizer_eq_top_of_lemma44_dichotomy (h : Tim79a.ParrottHyp z)
    (hZ : centerIn (J z) = centerIn (H z)) {z₁ : G} (hz₁ : z₁ ∈ centerIn (J z))
    (hz₁z : z₁ ∉ Subgroup.zpowers z) (hz₁2 : orderOf z₁ = 2)
    (hfuse : ∃ g ∈ centralizer ({z₁} : Set G), g * z * g⁻¹ ∈ H z ∧ g * z * g⁻¹ ≠ z)
    (h44 : ∀ y ∈ ⁅H z, H z⁆ ⊔ Subgroup.zpowers z₁, orderOf y = 2 → IsConj z₁ y → y = z₁)
    (hH' : (⁅H z, H z⁆ ⊔ Subgroup.zpowers z₁).relIndex (H z) = 2)
    (hG₀' : (∃ G₀ : Subgroup G, G₀.Normal ∧ G₀.index = 2 ∧ ¬ H z ≤ G₀) ∨
      (∀ y ∈ H z, y * y = 1 → y ∈ ⁅H z, H z⁆ ⊔ centerIn (J z)))
    (hO : ∃ t' j₀ : G, orderOf t' = 2 ∧ IsConj z t' ∧ j₀ ∈ J z ∧ j₀ ∉ centerIn (J z) ∧
      IsConj (t' * z) j₀)
    (hB5 : ∀ G₀ : Subgroup G, G₀.Normal → G₀.index = 2 → z ∈ G₀ → z₁ ∉ G₀ →
      (∃ g ∈ G₀, g * z * g⁻¹ ∈ H z ∧ g * z * g⁻¹ ≠ z) →
      ∃ G₁ : Subgroup G, G₁ ≤ G₀ ∧ G₁.relIndex G₀ = 2 ∧
        (∀ c ∈ G₀, (∀ x ∈ G₁, c * x = x * c) → c = 1) ∧
        ∃ (X : Type) (_ : Group X), CFSG.Blueprint.LieModel X .PSU 6 2 1 ∧
          Nonempty (↥G₁ ≃* X)) :
    centralizer ({z₁} : Set G) = ⊤ := by
  rcases hG₀' with hG₀ | hinvH
  · exact centralizer_eq_top_of_lemma44 h hZ hz₁ hz₁z hz₁2 hfuse h44 hH' hG₀ hO hB5
  · have hsupeq := commutator_sup_zpowers_eq_commutator_sup_centerIn h hz₁ hz₁z hz₁2
    obtain ⟨T, hT⟩ := exists_isSylowOf 2 (H z)
    have hJT : J z ≤ T := J_le_of_isSylowOf T hT
    have hTtop : IsSylowOf 2 T ⊤ := isSylowOf_top_of_isSylowOf_H h hZ T hT
    have hwc : ∀ g : G, g * z₁ * g⁻¹ ∈ T → g * z₁ * g⁻¹ = z₁ := by
      intro g hg
      have hyH : g * z₁ * g⁻¹ ∈ H z := hT.le hg
      have hord : orderOf (g * z₁ * g⁻¹) = 2 := by
        rw [← MulAut.conj_apply, MulEquiv.orderOf_eq]
        exact hz₁2
      have hyy : (g * z₁ * g⁻¹) * (g * z₁ * g⁻¹) = 1 := by
        have h1 := pow_orderOf_eq_one (g * z₁ * g⁻¹)
        rwa [hord, pow_two] at h1
      refine h44 _ ?_ hord (isConj_iff.mpr ⟨g, rfl⟩)
      rw [hsupeq]
      exact hinvH _ hyH hyy
    have hsup := eq_centralizer_sup_pPrimeCore_of_weakly_closed hTtop hz₁2 (hJT hz₁.1) hwc
    obtain ⟨t', j₀, ht', hzt', hj₀, hj₀c, hconj⟩ := hO
    rw [pPrimeCore_eq_bot_of_fusion h ht' hzt' hj₀ hj₀c hconj, sup_bot_eq] at hsup
    exact hsup

end CFSG.RankThree.GF2n.Parrott

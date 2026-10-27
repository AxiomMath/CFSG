module

public import CFSG.RankThree.GF2n.Parrott.Section4Theorem4
public import CFSG.RankThree.GF2n.Parrott.Section4Lemma45Dichotomy

public section

namespace CFSG.RankThree.GF2n.Parrott

open CFSG CFSG.Open CFSG.ABGLocalTools CFSG.GroupTheory Subgroup
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {z : G}

section Certified


theorem parrott_theorem4_of_dichotomy (h : Tim79a.ParrottHyp z)
    (hZ : centerIn (J z) = centerIn (H z))
    (hne : H z ⊔ pPrimeCore 2 G ≠ ⊤)
    (hNF : (∀ g : G, (∃ e ∈ centerIn (J z), e ≠ 1 ∧ e ≠ z ∧ g ∈ centralizer ({e} : Set G)) →
        g * z * g⁻¹ ∈ H z → g * z * g⁻¹ = z) →
      ∀ y ∈ H z, y ∉ J z → orderOf y = 2 → ¬ IsConj z y)
    (hB2 : ∀ z₁ ∈ centerIn (J z), z₁ ∉ Subgroup.zpowers z → orderOf z₁ = 2 →
      (∃ g ∈ centralizer ({z₁} : Set G), g * z * g⁻¹ ∈ H z ∧ g * z * g⁻¹ ≠ z) →
      ∃ U : Subgroup G, U ≤ centralizer ({z₁} : Set G) ∧
        U.relIndex (centralizer ({z₁} : Set G)) = 2 ∧ J z ≤ U ∧
        (∃ (_ : ((Subgroup.zpowers z₁).subgroupOf U).Normal) (X : Type) (_ : Group X),
          CFSG.Blueprint.LieModel X .PSU 6 2 1 ∧
            Nonempty (↥U ⧸ (Subgroup.zpowers z₁).subgroupOf U ≃* X)) ∧
        ∃ E : Subgroup G, IsParrottE z E ∧ E ≤ U ∧
          ((E.subgroupOf (normalizer (E : Set G) ⊓ U)).Normal ∧
             Nat.card (↥(normalizer (E : Set G) ⊓ U) ⧸
               E.subgroupOf (normalizer (E : Set G) ⊓ U)) = 20160 ∧
             ∀ L : Subgroup G, E ≤ L → L ≤ normalizer (E : Set G) ⊓ U →
               L.relIndex (normalizer (E : Set G) ⊓ U) ≠ 2) ∧
          (∀ T : Subgroup G, IsSylowOf 2 T (H z) → E ≤ T →
            ∀ g : G, CFSG.conjugate E g ≤ T → CFSG.conjugate E g = E) ∧
          (∀ y ∈ ⁅H z, H z⁆ ⊔ centerIn (J z), orderOf y = 2 → ∃ c ∈ H z, c * y * c⁻¹ ∈ E) ∧
          ∃ t' j₀ : G, t' ∈ E ∧ t' ∉ J z ∧ orderOf t' = 2 ∧ IsConj z t' ∧ j₀ ∈ J z ∧
            j₀ ∉ centerIn (J z) ∧ IsConj (t' * z) j₀)
    (hB3 : ∀ e ∈ centerIn (J z), e ≠ 1 → e ≠ z →
      (∃ g ∈ centralizer ({e} : Set G), g * z * g⁻¹ ∈ H z ∧ g * z * g⁻¹ ≠ z) →
      ∀ j ∈ J z, orderOf j = 2 → j ∉ Subgroup.zpowers z →
        ∀ g ∈ centralizer ({e} : Set G), g * z * g⁻¹ ≠ j)
    (hB6 : ∀ E : Subgroup G, IsParrottE z E →
      (∀ T : Subgroup G, IsSylowOf 2 T (H z) → E ≤ T →
        ∀ g : G, CFSG.conjugate E g ≤ T → CFSG.conjugate E g = E) →
      (∀ j ∈ J z, j ∉ Subgroup.zpowers z → ¬ IsConj z j) →
      (∃ e ∈ E, e ≠ z ∧ ∃ n ∈ normalizer (E : Set G), n * z * n⁻¹ = e) →
      ∃ K : Subgroup G, E ≤ K ∧ K.relIndex (normalizer (E : Set G)) = 2 ∧
        ¬ (normalizer (E : Set G) ⊓ H z ≤ K) ∧
        (E.subgroupOf K).Normal ∧ Nat.card (↥K ⧸ E.subgroupOf K) = 20160 ∧
          ∀ L : Subgroup G, E ≤ L → L ≤ K → L.relIndex K ≠ 2)
    (hH' : (⁅H z, H z⁆ ⊔ centerIn (J z)).relIndex (H z) = 2)
    (hG₀' : (∃ G₀ : Subgroup G, G₀.Normal ∧ G₀.index = 2 ∧ ¬ H z ≤ G₀) ∨
      (∀ y ∈ H z, y * y = 1 → y ∈ ⁅H z, H z⁆ ⊔ centerIn (J z)))
    (hB5 : ∀ z₁ ∈ centerIn (J z), z₁ ∉ Subgroup.zpowers z → orderOf z₁ = 2 →
      ∀ G₀ : Subgroup G, G₀.Normal → G₀.index = 2 → z ∈ G₀ → z₁ ∉ G₀ →
        (∃ g ∈ G₀, g * z * g⁻¹ ∈ H z ∧ g * z * g⁻¹ ≠ z) →
        ∃ G₁ : Subgroup G, G₁ ≤ G₀ ∧ G₁.relIndex G₀ = 2 ∧
          (∀ c ∈ G₀, (∀ x ∈ G₁, c * x = x * c) → c = 1) ∧
          ∃ (X : Type) (_ : Group X), CFSG.Blueprint.LieModel X .PSU 6 2 1 ∧
            Nonempty (↥G₁ ≃* X)) :
    Tim79a.ParrottCaseII z := by
  have hz2 : orderOf z = 2 := h.1
  obtain ⟨z₁₀, hZeq, hz₁₀z, hz₁₀2⟩ := exists_z1 h
  have hz₁₀ : z₁₀ ∈ centerIn (J z) := by
    rw [hZeq]
    exact Subgroup.mem_sup_right (Subgroup.mem_zpowers z₁₀)
  have hNF' : (∀ g : G, (g ∈ centralizer ({z₁₀} : Set G) ∨ g ∈ centralizer ({z * z₁₀} : Set G)) →
      g * z * g⁻¹ ∈ H z → g * z * g⁻¹ = z) →
      ∀ y ∈ H z, y ∉ J z → orderOf y = 2 → ¬ IsConj z y := by
    intro hA
    apply hNF
    rintro g ⟨e, he, he1, hez, hge⟩ hgH
    rcases (mem_centerIn_J_iff h hz₁₀ hz₁₀z hz₁₀2).mp he with h1 | h1 | h1 | h1
    · exact absurd h1 he1
    · exact absurd h1 hez
    · rw [h1] at hge
      exact hA g (Or.inl hge) hgH
    · rw [h1] at hge
      exact hA g (Or.inr hge) hgH
  obtain ⟨g, hg, hgH, hgz⟩ := lemma42_of_noFusion h hZ hne hz₁₀ hz₁₀z hz₁₀2 hNF'
  have hgz' : g * z * g⁻¹ ≠ z := fun h1 => hgz (by rw [h1]; exact Subgroup.mem_zpowers z)
  obtain ⟨z₁, hz₁, hz₁z, hz₁2, hfuse⟩ : ∃ z₁ : G, z₁ ∈ centerIn (J z) ∧
      z₁ ∉ Subgroup.zpowers z ∧ orderOf z₁ = 2 ∧
      ∃ g ∈ centralizer ({z₁} : Set G), g * z * g⁻¹ ∈ H z ∧ g * z * g⁻¹ ≠ z := by
    rcases hg with hg | hg
    · exact ⟨z₁₀, hz₁₀, hz₁₀z, hz₁₀2, g, hg, hgH, hgz'⟩
    · obtain ⟨h1, h2, h3⟩ := exists_z1_mul h hz₁₀ hz₁₀z hz₁₀2
      exact ⟨z * z₁₀, h1, h2, h3, g, hg, hgH, hgz'⟩
  obtain ⟨U, hUC, hUi, hJU, hUq, E, hE, hEU, hQ, hweak, hconjE, t', j₀, ht'E, ht'J, ht'2, hzt',
    hj₀, hj₀c, hconj⟩ := hB2 z₁ hz₁ hz₁z hz₁2 hfuse
  have hJ : ∀ j ∈ J z, j ∉ Subgroup.zpowers z → ¬ IsConj z j := fun j hj hjz =>
    not_isConj_of_mem_J_of_lemma32 h hZ hB3 hj hjz
  have hzE : z ∈ E := hE.2.2.1 (z_mem_centerIn_J h)
  have hzt'N : ∃ e ∈ E, e ≠ z ∧ ∃ n ∈ normalizer (E : Set G), n * z * n⁻¹ = e := by
    obtain ⟨n, hn, hnz⟩ := exists_mem_normalizer_of_isConj_of_mem h hZ hE hweak hzE ht'E hzt'
    exact ⟨t', ht'E, fun h1 => ht'J (by rw [h1]; exact z_mem_J h), n, hn, hnz⟩
  obtain ⟨K, hEK, hKi, hNH, hKq⟩ := hB6 E hE hweak hJ hzt'N
  have hN : normalizer (E : Set G) ≤ centralizer ({z₁} : Set G) :=
    normalizer_le_centralizer_of_lemma43 hZ hz₁ hUC hEU hQ ⟨K, hEK, hKi, hNH, hKq⟩
  have hsupeq := commutator_sup_zpowers_eq_commutator_sup_centerIn h hz₁ hz₁z hz₁2
  have hsub : ⁅H z, H z⁆ ⊔ Subgroup.zpowers z₁ ≤ ⁅H z, H z⁆ ⊔ centerIn (J z) := hsupeq.le
  have h44 : ∀ y ∈ ⁅H z, H z⁆ ⊔ Subgroup.zpowers z₁, orderOf y = 2 → IsConj z₁ y → y = z₁ :=
    fun y hy hy2 hyz => eq_of_isConj_of_mem_commutator_sup h hZ hz₁ hE hN hweak
      (fun y' hy' hy'2 => hconjE y' (hsub hy') hy'2) hy hy2 hyz
  have hH'' : (⁅H z, H z⁆ ⊔ Subgroup.zpowers z₁).relIndex (H z) = 2 := by
    rw [hsupeq]
    exact hH'
  have hC : centralizer ({z₁} : Set G) = ⊤ :=
    centralizer_eq_top_of_lemma44_dichotomy h hZ hz₁ hz₁z hz₁2 hfuse h44 hH'' hG₀'
      ⟨t', j₀, ht'2, hzt', hj₀, hj₀c, hconj⟩ (hB5 z₁ hz₁ hz₁z hz₁2)
  have hcentral : ∀ g' : G, g' * z₁ = z₁ * g' := fun g' =>
    mem_centralizer_singleton_iff.mp (hC ▸ Subgroup.mem_top g')
  refine ⟨z₁, hz₁, hz₁z, hz₁2, ?_, U, ?_, Subgroup.zpowers_le.mpr (hJU hz₁.1), hUq⟩
  · refine ⟨fun x hx g' => ?_⟩
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    have hc : Commute g' z₁ := hcentral g'
    rw [(hc.zpow_right k).eq, mul_inv_cancel_right]
    exact Subgroup.mem_zpowers_iff.mpr ⟨k, rfl⟩
  · rw [hC, Subgroup.relIndex_top_right] at hUi
    exact hUi

end Certified

end CFSG.RankThree.GF2n.Parrott

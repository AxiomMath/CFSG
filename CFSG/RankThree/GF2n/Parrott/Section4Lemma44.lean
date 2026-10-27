module

public import CFSG.GroupTheory.SimpleQuotientIndexTwo
public import CFSG.RankThree.GF2n.Parrott.Section4Defs
public import CFSG.GF2Type.Aschbacher1976Full.HSBurnside
public import CFSG.RankThree.GF2n.Parrott.Section4Lemma42Steps

public section

namespace CFSG.RankThree.GF2n.Parrott

open CFSG CFSG.Open CFSG.ABGLocalTools CFSG.GroupTheory Subgroup

variable {G : Type} [Group G] [Finite G] {z : G}

section Certified


theorem not_isConj_of_mem_J_of_lemma32 (h : Tim79a.ParrottHyp z)
    (hZ : centerIn (J z) = centerIn (H z))
    (hB3 : ∀ e ∈ centerIn (J z), e ≠ 1 → e ≠ z →
      (∃ g ∈ centralizer ({e} : Set G), g * z * g⁻¹ ∈ H z ∧ g * z * g⁻¹ ≠ z) →
      ∀ j ∈ J z, orderOf j = 2 → j ∉ Subgroup.zpowers z →
        ∀ g ∈ centralizer ({e} : Set G), g * z * g⁻¹ ≠ j)
    {j : G} (hj : j ∈ J z) (hjz : j ∉ Subgroup.zpowers z) : ¬ IsConj z j := by
  have hz2 : orderOf z = 2 := h.1
  refine not_isConj_of_mem_J h hZ ?_ hj hjz
  rintro g ⟨e, he, he1, hez, hge⟩ hgJ
  by_contra hne
  by_cases hex : ∃ g' ∈ centralizer ({e} : Set G), g' * z * g'⁻¹ ∈ H z ∧ g' * z * g'⁻¹ ≠ z
  · have hord : orderOf (g * z * g⁻¹) = 2 := by
      rw [← MulAut.conj_apply, MulEquiv.orderOf_eq]
      exact hz2
    have hnot : g * z * g⁻¹ ∉ Subgroup.zpowers z := fun hm => by
      rcases CFSG.GF2Type.Aschbacher1976Full.Z4Q8.mem_zpowers_two hz2 hm with h1 | h1
      · rw [h1, orderOf_one] at hord
        exact absurd hord (by norm_num)
      · exact hne h1
    exact hB3 e he he1 hez hex (g * z * g⁻¹) hgJ hord hnot g hge rfl
  · push Not at hex
    exact hne (hex g hge (J_le_H hgJ))

end Certified

theorem normalizer_le_centralizer_of_lemma43 (hZ : centerIn (J z) = centerIn (H z)) {z₁ : G}
    (hz₁ : z₁ ∈ centerIn (J z)) {U E : Subgroup G} (hU : U ≤ centralizer ({z₁} : Set G))
    (hEU : E ≤ U)
    (hQ : (E.subgroupOf (normalizer (E : Set G) ⊓ U)).Normal ∧
            Nat.card (↥(normalizer (E : Set G) ⊓ U) ⧸
              E.subgroupOf (normalizer (E : Set G) ⊓ U)) = 20160 ∧
            ∀ L : Subgroup G, E ≤ L → L ≤ normalizer (E : Set G) ⊓ U →
              L.relIndex (normalizer (E : Set G) ⊓ U) ≠ 2)
    (hK : ∃ K : Subgroup G, E ≤ K ∧ K.relIndex (normalizer (E : Set G)) = 2 ∧
      ¬ (normalizer (E : Set G) ⊓ H z ≤ K) ∧
      (E.subgroupOf K).Normal ∧ Nat.card (↥K ⧸ E.subgroupOf K) = 20160 ∧
        ∀ L : Subgroup G, E ≤ L → L ≤ K → L.relIndex K ≠ 2) :
    normalizer (E : Set G) ≤ centralizer ({z₁} : Set G) := by
  obtain ⟨-, hc₁, hQ⟩ := hQ
  obtain ⟨K, hEK, hKi, hNH, -, hc₂, -⟩ := hK
  have hz₁H : H z ≤ centralizer ({z₁} : Set G) := by
    intro x hx
    have hz₁' : z₁ ∈ centerIn (H z) := hZ ▸ hz₁
    rw [mem_centralizer_singleton_iff]
    exact Subgroup.mem_centralizer_iff.mp hz₁'.2 x hx
  have hEN₁ : E ≤ normalizer (E : Set G) ⊓ U := le_inf Subgroup.le_normalizer hEU
  have hEq : normalizer (E : Set G) ⊓ U = K :=
    eq_of_le_of_relIndex_two_of_forall_relIndex_ne_two hEN₁ inf_le_left hEK hKi hQ
      (hc₁.trans hc₂.symm)
  have hKU : K ≤ centralizer ({z₁} : Set G) := hEq ▸ inf_le_right.trans hU
  obtain ⟨a, ha, hab⟩ := Subgroup.relIndex_eq_two_iff.mp hKi
  intro n hn
  by_cases hnK : n ∈ K
  · exact hKU hnK
  · obtain ⟨h₀, ⟨hh₀N, hh₀H⟩, hh₀K⟩ := Set.not_subset.mp hNH
    have h1 : n * a ∈ K := by
      rcases hab n hn with h' | h'
      · exact h'.1
      · exact absurd h'.1 hnK
    have h2 : h₀ * a ∈ K := by
      rcases hab h₀ hh₀N with h' | h'
      · exact h'.1
      · exact absurd h'.1 hh₀K
    have h3 : n * h₀⁻¹ ∈ K := by
      have := Subgroup.mul_mem K h1 (Subgroup.inv_mem K h2)
      simpa [mul_assoc] using this
    have h4 : n = (n * h₀⁻¹) * h₀ := by group
    rw [h4]
    exact Subgroup.mul_mem _ (hKU h3) (hz₁H hh₀H)

omit [Finite G] in
private theorem exists_sylow_coe_eq_of_isSylowOf_top [Finite G] {p : ℕ} [Fact p.Prime]
    {T : Subgroup G} (hT : IsSylowOf p T ⊤) : ∃ P : Sylow p G, (P : Subgroup G) = T := by
  obtain ⟨-, hp, hdvd⟩ := isSylowOf_iff.mp hT
  rw [Subgroup.relIndex_top_right] at hdvd
  exact ⟨hp.toSylow hdvd, IsPGroup.toSylow_coe _ _⟩

theorem exists_mem_normalizer_of_isConj_of_mem (h : Tim79a.ParrottHyp z)
    (hZ : centerIn (J z) = centerIn (H z)) {E : Subgroup G} (hE : IsParrottE z E)
    (hweak : ∀ T : Subgroup G, IsSylowOf 2 T (H z) → E ≤ T →
      ∀ g : G, CFSG.conjugate E g ≤ T → CFSG.conjugate E g = E)
    {a b : G} (ha : a ∈ E) (hb : b ∈ E) (hab : IsConj a b) :
    ∃ n ∈ normalizer (E : Set G), n * a * n⁻¹ = b := by
  have hEH : E ≤ H z := hE.1
  have hEp : IsPGroup 2 E := IsPGroup.of_card (n := 10) hE.2.2.2.2.1
  obtain ⟨T, hT, hET⟩ : ∃ T : Subgroup G, IsSylowOf 2 T (H z) ∧ E ≤ T := by
    have hEpH : IsPGroup 2 (E.subgroupOf (H z)) := hEp.comap_subtype
    obtain ⟨Q, hQ⟩ := hEpH.exists_le_sylow
    refine ⟨(Q : Subgroup ↥(H z)).map (H z).subtype, ⟨Q, rfl⟩, fun x hx => ?_⟩
    exact ⟨⟨x, hEH hx⟩, hQ (Subgroup.mem_subgroupOf.mpr hx), rfl⟩
  have hTtop : IsSylowOf 2 T ⊤ := isSylowOf_top_of_isSylowOf_H h hZ T hT
  obtain ⟨P, hP⟩ := exists_sylow_coe_eq_of_isSylowOf_top hTtop
  obtain ⟨g, hg⟩ := isConj_iff.mp hab
  have hcomm : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x := fun x hx y hy =>
    (commute_of_mem_of_isMulCommutative hE.2.2.2.1.1 hx hy).eq
  obtain ⟨n, hn, hnz⟩ := CFSG.GF2Type.Aschbacher1976Full.HS.burnside_fusion P E (hP ▸ hET) hcomm
    (fun g' hg' => hweak T hT hET g' (hP ▸ hg')) ha (hg ▸ hb)
  exact ⟨n, hn, hnz.trans hg⟩

theorem eq_of_isConj_of_mem_commutator_sup (h : Tim79a.ParrottHyp z)
    (hZ : centerIn (J z) = centerIn (H z)) {z₁ : G} (hz₁ : z₁ ∈ centerIn (J z))
    {E : Subgroup G} (hE : IsParrottE z E)
    (hN : normalizer (E : Set G) ≤ centralizer ({z₁} : Set G))
    (hweak : ∀ T : Subgroup G, IsSylowOf 2 T (H z) → E ≤ T →
      ∀ g : G, CFSG.conjugate E g ≤ T → CFSG.conjugate E g = E)
    (hconj : ∀ y ∈ ⁅H z, H z⁆ ⊔ Subgroup.zpowers z₁, orderOf y = 2 →
      ∃ c ∈ H z, c * y * c⁻¹ ∈ E)
    {y : G} (hy : y ∈ ⁅H z, H z⁆ ⊔ Subgroup.zpowers z₁) (hy2 : orderOf y = 2)
    (hyz : IsConj z₁ y) : y = z₁ := by
  obtain ⟨c, hcH, hce⟩ := hconj y hy hy2
  have hz₁E : z₁ ∈ E := hE.2.2.1 hz₁
  have hcy : IsConj z₁ (c * y * c⁻¹) := hyz.trans (isConj_iff.mpr ⟨c, rfl⟩)
  obtain ⟨n, hn, hnz⟩ := exists_mem_normalizer_of_isConj_of_mem h hZ hE hweak hz₁E hce hcy
  have hnc : n * z₁ = z₁ * n := mem_centralizer_singleton_iff.mp (hN hn)
  have hnz' : n * z₁ * n⁻¹ = z₁ := by
    calc n * z₁ * n⁻¹ = z₁ * n * n⁻¹ := by rw [hnc]
      _ = z₁ := by group
  have h1 : c * y * c⁻¹ = z₁ := hnz.symm.trans hnz'
  have hz₁H : z₁ * c = c * z₁ := by
    have hz₁' : z₁ ∈ centerIn (H z) := hZ ▸ hz₁
    exact (Subgroup.mem_centralizer_iff.mp hz₁'.2 c hcH).symm
  calc y = c⁻¹ * (c * y * c⁻¹) * c := by group
    _ = c⁻¹ * z₁ * c := by rw [h1]
    _ = c⁻¹ * (z₁ * c) := by group
    _ = c⁻¹ * (c * z₁) := by rw [hz₁H]
    _ = z₁ := by group

end CFSG.RankThree.GF2n.Parrott

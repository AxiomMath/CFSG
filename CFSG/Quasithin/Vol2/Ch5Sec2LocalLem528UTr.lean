module

public import CFSG.Quasithin.Vol2.Ch5Sec2LocalLem528STr
public import CFSG.Quasithin.Vol2.Ch5Sec2LocalLem528UKG

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.LieType.BorelTits

section Model

variable {G : Type} [Group G] {G₂ : Subgroup G} {Y : Type} [Group Y] {M : Subgroup Y}

theorem module_transport (e : ↥G₂ ≃* ↥M) {m : ℕ}
    (h1 : perfectCore M ≤ Subgroup.centralizer (centerOf (pCoreOf 2 (perfectCore M)) : Set Y))
    (h2 : ⁅pCoreOf 2 (perfectCore M), perfectCore M⁆ = pCoreOf 2 (perfectCore M))
    (h3 : ∀ R : Subgroup Y, R ≤ pCoreOf 2 (perfectCore M) →
      perfectCore M ≤ Subgroup.normalizer (R : Set Y) →
      ¬ R ≤ centerOf (pCoreOf 2 (perfectCore M)) →
      R ⊔ centerOf (pCoreOf 2 (perfectCore M)) ≠ pCoreOf 2 (perfectCore M) →
        ⁅R, pCoreOf 2 (perfectCore M)⁆ = centerOf (pCoreOf 2 (perfectCore M)) ∧
          Nat.card ↥(R ⊔ centerOf (pCoreOf 2 (perfectCore M))) = (2 ^ m) ^ 3) :
    perfectCore G₂ ≤ Subgroup.centralizer (centerOf (pCoreOf 2 (perfectCore G₂)) : Set G) ∧
      ⁅pCoreOf 2 (perfectCore G₂), perfectCore G₂⁆ = pCoreOf 2 (perfectCore G₂) ∧
      ∀ R : Subgroup G, R ≤ pCoreOf 2 (perfectCore G₂) →
        perfectCore G₂ ≤ Subgroup.normalizer (R : Set G) →
        ¬ R ≤ centerOf (pCoreOf 2 (perfectCore G₂)) →
        R ⊔ centerOf (pCoreOf 2 (perfectCore G₂)) ≠ pCoreOf 2 (perfectCore G₂) →
          ⁅R, pCoreOf 2 (perfectCore G₂)⁆ = centerOf (pCoreOf 2 (perfectCore G₂)) ∧
            Nat.card ↥(R ⊔ centerOf (pCoreOf 2 (perfectCore G₂))) = (2 ^ m) ^ 3 := by
  obtain ⟨K', hKg, hKf, hQg, hQf, hZg, hZf⟩ := model_data e
  have hg : Function.Injective G₂.subtype := G₂.subtype_injective
  have hf : Function.Injective (M.subtype.comp e.toMonoidHom) :=
    M.subtype_injective.comp e.injective
  have hQ₀ : pCoreOf 2 (perfectCore G₂) ≤ G₂ := by
    rw [hQg]
    exact (Subgroup.map_le_range _ _).trans (le_of_eq (Subgroup.range_subtype G₂))
  rw [hZf, hKf] at h1
  rw [hQf, hKf, ← Subgroup.map_commutator] at h2
  have h2' : ⁅pCoreOf 2 K', K'⁆ = pCoreOf 2 K' := Subgroup.map_injective hf h2
  refine ⟨?_, ?_, fun R hRQ hKR hRZ hRQne => ?_⟩
  · rw [hZg, hKg, map_le_centralizer_map_iff _ hg]
    exact (map_le_centralizer_map_iff _ hf _ _).mp h1
  · rw [hQg, hKg, ← Subgroup.map_commutator, h2']
  obtain ⟨R', rfl⟩ := exists_map_subtype_of_le hQ₀ hRQ
  rw [hQg, Subgroup.map_le_map_iff_of_injective hg] at hRQ
  rw [hKg, map_le_normalizer_map_iff _ hg] at hKR
  rw [hZg, Subgroup.map_le_map_iff_of_injective hg] at hRZ
  rw [hZg, hQg, ← Subgroup.map_sup] at hRQne
  have hne : R' ⊔ centerOf (pCoreOf 2 K') ≠ pCoreOf 2 K' := fun h => hRQne (by rw [h])
  obtain ⟨h4, h5⟩ := h3 (R'.map (M.subtype.comp e.toMonoidHom))
    ((Subgroup.map_mono hRQ).trans (le_of_eq hQf.symm))
    (by rw [hKf]; exact (map_le_normalizer_map_iff _ hf _ _).mpr hKR)
    (by rw [hZf, Subgroup.map_le_map_iff_of_injective hf]; exact hRZ)
    (by
      rw [hZf, hQf, ← Subgroup.map_sup]
      exact fun h => hne (Subgroup.map_injective hf h))
  rw [hZf, hQf, ← Subgroup.map_commutator] at h4
  rw [hZf, ← Subgroup.map_sup, Subgroup.card_map_of_injective hf] at h5
  refine ⟨?_, ?_⟩
  · rw [hZg, hQg, ← Subgroup.map_commutator, Subgroup.map_injective hf h4]
  · rw [hZg, ← Subgroup.map_sup, Subgroup.card_map_of_injective hg]
    exact h5

theorem ext_center_transport (e : ↥G₂ ≃* ↥M)
    (h : ∀ t ∈ M, t ^ 2 = 1 → t ∉ pCoreOf 2 (perfectCore M) →
      (∀ k ∈ perfectCore M, t * k * t⁻¹ * k⁻¹ ∈ pCoreOf 2 (perfectCore M)) →
        t ∈ Subgroup.centralizer (centerOf (pCoreOf 2 (perfectCore M)) : Set Y)) :
    ∀ t ∈ G₂, t ^ 2 = 1 → t ∉ pCoreOf 2 (perfectCore G₂) →
      (∀ k ∈ perfectCore G₂, t * k * t⁻¹ * k⁻¹ ∈ pCoreOf 2 (perfectCore G₂)) →
        t ∈ Subgroup.centralizer (centerOf (pCoreOf 2 (perfectCore G₂)) : Set G) := by
  obtain ⟨K', hKg, hKf, hQg, hQf, hZg, hZf⟩ := model_data e
  have hf : Function.Injective (M.subtype.comp e.toMonoidHom) :=
    M.subtype_injective.comp e.injective
  intro t htG ht2 htQ htk
  set f := M.subtype.comp e.toMonoidHom with hfdef
  set t' : ↥G₂ := ⟨t, htG⟩ with ht'
  have hgt : G₂.subtype t' = t := rfl
  have ht'2 : t' ^ 2 = 1 := Subtype.ext (by rw [SubgroupClass.coe_pow]; exact ht2)
  have h1 := h (f t') (e t').2 (by rw [← map_pow, ht'2, map_one])
    (by
      intro hmem
      rw [hQf] at hmem
      obtain ⟨c, hc, hc'⟩ := hmem
      apply htQ
      rw [hQg]
      exact ⟨c, hc, by rw [hf hc', hgt]⟩)
    (by
      intro k hk
      rw [hKf] at hk
      obtain ⟨k', hk', rfl⟩ := hk
      have h2 := htk (G₂.subtype k') (by rw [hKg]; exact ⟨k', hk', rfl⟩)
      rw [hQg] at h2
      obtain ⟨c, hc, hc'⟩ := h2
      have hc'' : c = t' * k' * t'⁻¹ * k'⁻¹ := G₂.subtype_injective (by
        rw [hc', map_mul, map_mul, map_mul, map_inv, map_inv, hgt])
      rw [hQf, ← map_mul, ← map_inv, ← map_mul, ← map_inv, ← map_mul, ← hc'']
      exact ⟨c, hc, rfl⟩)
  rw [hZf] at h1
  rw [hZg, Subgroup.mem_centralizer_iff]
  rintro _ ⟨z, hz, rfl⟩
  have h3 := Subgroup.mem_centralizer_iff.mp h1 (f z) ⟨z, hz, rfl⟩
  rw [← map_mul, ← map_mul] at h3
  have h4 := hf h3
  rw [← hgt, ← map_mul, ← map_mul, h4]

end Model

section Amalgam

variable {G : Type} [Group G] {G₁ G₂ : Subgroup G}

theorem module_of_amalgam (hU4b : FactU4ParabolicModule) {m : ℕ} (hm : 2 ≤ m)
    (h : IsAmalgamOfGroup (RankTwoAmalgam.ofSubgroups G₁ G₂) (IsLieOverTwo .PSU 4 m) ∨
      IsU4ExtTwo m (RankTwoAmalgam.ofSubgroups G₁ G₂))
    (hsp : IsSpecialPow 2 (2 ^ m) 2 ↥(pCoreOf 2 (perfectCore G₂))) :
    perfectCore G₂ ≤ Subgroup.centralizer (centerOf (pCoreOf 2 (perfectCore G₂)) : Set G) ∧
      ⁅pCoreOf 2 (perfectCore G₂), perfectCore G₂⁆ = pCoreOf 2 (perfectCore G₂) ∧
      ∀ R : Subgroup G, R ≤ pCoreOf 2 (perfectCore G₂) →
        perfectCore G₂ ≤ Subgroup.normalizer (R : Set G) →
        ¬ R ≤ centerOf (pCoreOf 2 (perfectCore G₂)) →
        R ⊔ centerOf (pCoreOf 2 (perfectCore G₂)) ≠ pCoreOf 2 (perfectCore G₂) →
          ⁅R, pCoreOf 2 (perfectCore G₂)⁆ = centerOf (pCoreOf 2 (perfectCore G₂)) ∧
            Nat.card ↥(R ⊔ centerOf (pCoreOf 2 (perfectCore G₂))) = (2 ^ m) ^ 3 := by
  rcases h with ⟨Y, _, hY, T, M₁, M₂, hpair, ⟨φ⟩⟩ |
      ⟨Y₀, _, Y, _, ι, hY₀, hι, hidx, T, M₁, M₂, hpair, ⟨φ⟩⟩
  · obtain ⟨h1, h2, h3⟩ := hU4b Y m T M₁ M₂ hm (Or.inl hY) hpair (isSpecialPow_model φ.φ2 hsp)
    exact module_transport φ.φ2 h1 h2 h3
  · obtain ⟨h1, h2, h3⟩ := hU4b Y m T M₁ M₂ hm (Or.inr ⟨Y₀, inferInstance, ι, hY₀, hι, hidx⟩)
      hpair (isSpecialPow_model φ.φ2 hsp)
    exact module_transport φ.φ2 h1 h2 h3

theorem ext_center_of_amalgam (hU4a : FactU4ExtCenter) {m : ℕ} (hm : 2 ≤ m)
    (h : IsU4ExtTwo m (RankTwoAmalgam.ofSubgroups G₁ G₂))
    (hsp : IsSpecialPow 2 (2 ^ m) 2 ↥(pCoreOf 2 (perfectCore G₂))) :
    ∀ t ∈ G₂, t ^ 2 = 1 → t ∉ pCoreOf 2 (perfectCore G₂) →
      (∀ k ∈ perfectCore G₂, t * k * t⁻¹ * k⁻¹ ∈ pCoreOf 2 (perfectCore G₂)) →
        t ∈ Subgroup.centralizer (centerOf (pCoreOf 2 (perfectCore G₂)) : Set G) := by
  obtain ⟨Y₀, _, Y, _, ι, hY₀, hι, hidx, T, M₁, M₂, hpair, ⟨φ⟩⟩ := h
  exact ext_center_transport φ.φ2 (hU4a Y m T M₁ M₂ hm ⟨Y₀, inferInstance, ι, hY₀, hι, hidx⟩
    hpair (isSpecialPow_model φ.φ2 hsp))

end Amalgam

end CFSG.Quasithin.H13

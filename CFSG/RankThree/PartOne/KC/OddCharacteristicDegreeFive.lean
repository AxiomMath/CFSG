module

public import CFSG.RankThree.PartOne.KC.EvenCenterSection
public import CFSG.RankThree.GroupTheory.SteinbergBYDegreeFourRank
public import CFSG.RankThree.SteinbergR3ECADegreeFiveSection
public import CFSG.Assembly.RankThreeEvenDefs

public section

namespace CFSG.RankThree.PartOne

open CFSG CFSG.Assembly CFSG.Assembly.LowTwoRank

theorem split_degree_five_prime_restrictions {ℓ f : ℕ} {c : StatedLieTag} (hf : 1 ≤ f)
    (hdiv : (c = .PSL ∧ 5 ∣ ℓ ^ f - 1) ∨ (c = .PSU ∧ 5 ∣ ℓ ^ f + 1)) :
    ℓ ≠ 5 ∧ (ℓ = 3 → 2 ≤ f) := by
  have h1 : 1 ≤ ℓ ^ f ∨ ℓ = 0 := by
    rcases Nat.eq_zero_or_pos ℓ with h | h
    · exact Or.inr h
    · exact Or.inl (Nat.one_le_pow _ _ h)
  refine ⟨?_, ?_⟩
  · rintro rfl
    have h5 : 5 ∣ 5 ^ f := dvd_pow_self 5 (by omega)
    have h1' : 1 ≤ 5 ^ f := Nat.one_le_pow _ _ (by norm_num)
    rcases hdiv with ⟨-, h⟩ | ⟨-, h⟩
    · have := Nat.dvd_sub h5 h
      have e : 5 ^ f - (5 ^ f - 1) = 1 := by omega
      rw [e] at this
      omega
    · have := (Nat.dvd_add_right h5).mp h
      omega
  · rintro rfl
    by_contra hf2
    have hf1 : f = 1 := by omega
    subst hf1
    rcases hdiv with ⟨-, h⟩ | ⟨-, h⟩ <;> norm_num at h

theorem split_degree_five_rank_ge_four {G : Type} [Group G] [Finite G]
    {ℓ f : ℕ} (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2) (hf : 1 ≤ f) {c : StatedLieTag}
    (hc : c = .PSL ∨ c = .PSU)
    (hdiv : (c = .PSL ∧ 5 ∣ ℓ ^ f - 1) ∨ (c = .PSU ∧ 5 ∣ ℓ ^ f + 1)) {T : Type} [Group T]
    (hT : StatedClassicalModel T c 5 ℓ f) (H : Subgroup G) (π : H →* T)
    (hπ : Function.Surjective π) : 4 ≤ evenRank G := by
  classical
  by_contra hlt
  have he : evenRank G ≤ 3 := by omega
  obtain ⟨hℓ5, hℓ3⟩ := split_degree_five_prime_restrictions (ℓ := ℓ) hf hdiv
  have hTfin : Finite T := by
    rcases hc with rfl | rfl
    · obtain ⟨-, K, _, hKfin, -, ⟨e⟩⟩ := hT
      exact Finite.of_equiv _ e.symm.toEquiv
    · obtain ⟨-, K, _, hKfin, -, ⟨e⟩⟩ := hT
      exact Finite.of_equiv _ e.symm.toEquiv
  obtain ⟨M, hMq, hMeven, hS4, E, hEel, hEcard⟩ :=
    CFSG.RankThree.DegreeFiveSection.degree_five_classical_even_center_four_dimensional_section
      hℓ2 hc T hT
  let ρ : (M.comap π) →* M := (π.comp (M.comap π).subtype).codRestrict M fun x => x.2
  let H₀ : Subgroup G := (M.comap π).map H.subtype
  let e₀ : (M.comap π) ≃* H₀ := Subgroup.equivMapOfInjective _ H.subtype H.subtype_injective
  let π₀ : H₀ →* M := ρ.comp e₀.symm.toMonoidHom
  have hπ₀ : Function.Surjective π₀ := by
    intro m
    obtain ⟨h, hh⟩ := hπ (m : T)
    have hmem : h ∈ M.comap π := by
      show π h ∈ M
      rw [hh]
      exact m.2
    refine ⟨e₀ ⟨h, hmem⟩, ?_⟩
    show ρ (e₀.symm (e₀ ⟨h, hmem⟩)) = m
    rw [MulEquiv.symm_apply_apply]
    exact Subtype.ext hh
  have : Finite M := inferInstance
  obtain ⟨Y, _, _, _, φ, hφ, hker, hYr⟩ :=
    even_center_section_global_rank_central_cover (G := G) 3 he hMq hMeven
      ⟨E, hEel, by rw [hEcard]; norm_num⟩ H₀ π₀ hπ₀
  have h4 :=
    CFSG.RankThree.GroupTheory.SteinbergBY.degree_four_classical_odd_central_cover_rank_four
      hℓ hℓ2 hℓ5 hf hℓ3 hc hS4 φ hφ hker
  have h3 := hYr ℓ hℓ hℓ2
  omega

theorem not_split_degree_five_of_component {G : Type} [Group G] [Finite G]
    (he : evenRank G ≤ 3) (N : Subgroup G) [N.Normal] (L : Subgroup (G ⧸ N)) {ℓ f : ℕ}
    (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2) (hf : 1 ≤ f)
    {c : StatedLieTag} (hc : c = .PSL ∨ c = .PSU)
    (hmod : StatedClassicalModel (L ⧸ Subgroup.center L) c 5 ℓ f) :
    ¬ ((c = .PSL ∧ 5 ∣ ℓ ^ f - 1) ∨ (c = .PSU ∧ 5 ∣ ℓ ^ f + 1)) := by
  intro hdiv
  let q : G →* G ⧸ N := QuotientGroup.mk' N
  let π0 : L.comap q →* L := (q.comp (L.comap q).subtype).codRestrict L fun x => x.2
  let π : L.comap q →* L ⧸ Subgroup.center L :=
    (QuotientGroup.mk' (Subgroup.center L)).comp π0
  have hπ : Function.Surjective π := by
    intro y
    obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective y
    obtain ⟨g, hg⟩ := QuotientGroup.mk_surjective (l : G ⧸ N)
    have hmem : g ∈ L.comap q := by
      show q g ∈ L
      rw [show q g = (l : G ⧸ N) from hg]
      exact l.2
    refine ⟨⟨g, hmem⟩, ?_⟩
    have h1 : π0 ⟨g, hmem⟩ = l := Subtype.ext hg
    show QuotientGroup.mk' (Subgroup.center L) (π0 ⟨g, hmem⟩) = QuotientGroup.mk l
    rw [h1]
    rfl
  have := split_degree_five_rank_ge_four hℓ hℓ2 hf hc hdiv hmod (L.comap q) π hπ
  omega

theorem odd_characteristic_split_degree_five_sections_force_two_local_rank_four {G : Type}
    [Group G] [Finite G] :
    (∀ {ℓ f : ℕ} {c : StatedLieTag} {T : Type} [Group T], ℓ.Prime → ℓ ≠ 2 → 1 ≤ f →
      (c = .PSL ∨ c = .PSU) → ((c = .PSL ∧ 5 ∣ ℓ ^ f - 1) ∨ (c = .PSU ∧ 5 ∣ ℓ ^ f + 1)) →
      StatedClassicalModel T c 5 ℓ f → ∀ (H : Subgroup G) (π : H →* T),
        Function.Surjective π → 4 ≤ evenRank G) ∧
    (evenRank G ≤ 3 → ∀ (N : Subgroup G) [N.Normal] (L : Subgroup (G ⧸ N)) {ℓ f : ℕ},
      ℓ.Prime → ℓ ≠ 2 → 1 ≤ f → ∀ {c : StatedLieTag}, (c = .PSL ∨ c = .PSU) →
      StatedClassicalModel (L ⧸ Subgroup.center L) c 5 ℓ f →
      ¬ ((c = .PSL ∧ 5 ∣ ℓ ^ f - 1) ∨ (c = .PSU ∧ 5 ∣ ℓ ^ f + 1))) := by
  refine ⟨?_, ?_⟩
  · intro ℓ f c T _ hℓ hℓ2 hf hc hdiv hT H π hπ
    exact split_degree_five_rank_ge_four hℓ hℓ2 hf hc hdiv hT H π hπ
  · intro he N _ L ℓ f hℓ hℓ2 hf c hc hmod
    exact not_split_degree_five_of_component he N L hℓ hℓ2 hf hc hmod

end CFSG.RankThree.PartOne

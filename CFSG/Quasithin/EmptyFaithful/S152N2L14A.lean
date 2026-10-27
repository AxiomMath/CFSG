module

public import CFSG.Quasithin.EmptyFaithful.S152N2Lin

public section

namespace CFSG.Quasithin

namespace S152N2

variable {G : Type*} [Group G]

theorem isKleinFour_of_card {K : Subgroup G} (hK2 : ∀ k ∈ K, k * k = 1) (hcard : Nat.card K = 4) :
    IsKleinFour ↥K := by
  refine ⟨hcard, ?_⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite ↥K := Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
  have hnt : Nontrivial ↥K := Finite.one_lt_card_iff_nontrivial.mp (by rw [hcard]; norm_num)
  rw [Monoid.exponent_eq_prime_iff Nat.prime_two]
  intro g hg
  refine orderOf_eq_prime ?_ hg
  apply Subtype.ext
  simpa [sq] using hK2 g g.2

theorem klein_basis [Finite G] {T K : Subgroup G} (hT : IsPGroup 2 T) (hKT : K ≤ T)
    (hKn : T ≤ Subgroup.normalizer (K : Set G)) (hK2 : ∀ k ∈ K, k * k = 1)
    (hcard : Nat.card K = 4) :
    ∃ k₀ ∈ K, ∃ k₁ ∈ K, k₀ ≠ 1 ∧ (∀ t ∈ T, t * k₀ = k₀ * t) ∧ k₁ ≠ 1 ∧ k₁ ≠ k₀ ∧
      ∀ k ∈ K, k = 1 ∨ k = k₀ ∨ k = k₁ ∨ k = k₀ * k₁ := by
  have : IsKleinFour ↥K := isKleinFour_of_card hK2 hcard
  have hK1 : K ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hcard
    omega
  obtain ⟨k₀, hk₀K, hk₀1, hk₀c⟩ := exists_central_of_normalized hT hKT hKn hK1
  obtain ⟨k₁', hk₁'1, hk₁'0⟩ : ∃ k : ↥K, k ≠ 1 ∧ k ≠ ⟨k₀, hk₀K⟩ := by
    by_contra h
    push Not at h
    have hle : Nat.card ↥K ≤ 2 := by
      have hsub : (Set.univ : Set ↥K) ⊆ {1, ⟨k₀, hk₀K⟩} := by
        intro k _
        by_cases hk1 : k = 1
        · simp [hk1]
        · simp [h k hk1]
      calc Nat.card ↥K = (Set.univ : Set ↥K).ncard := by rw [Set.ncard_univ]
        _ ≤ ({1, ⟨k₀, hk₀K⟩} : Set ↥K).ncard := Set.ncard_le_ncard hsub (Set.toFinite _)
        _ ≤ 2 := by
          refine (Set.ncard_insert_le _ _).trans ?_
          simp
    omega
  have hk₀' : (⟨k₀, hk₀K⟩ : ↥K) ≠ 1 := fun h => hk₀1 (congrArg Subtype.val h)
  refine ⟨k₀, hk₀K, k₁', k₁'.2, hk₀1, hk₀c, fun h => hk₁'1 (Subtype.ext h),
    fun h => hk₁'0 (Subtype.ext h), fun k hk => ?_⟩
  by_cases h1 : k = 1
  · exact Or.inl h1
  by_cases h2 : k = k₀
  · exact Or.inr (Or.inl h2)
  by_cases h3 : k = k₁'
  · exact Or.inr (Or.inr (Or.inl h3))
  refine Or.inr (Or.inr (Or.inr ?_))
  have := IsKleinFour.eq_mul_of_ne_all (x := (⟨k₀, hk₀K⟩ : ↥K)) (y := k₁') (z := ⟨k, hk⟩)
    hk₀' hk₁'1 (fun h => hk₁'0 h.symm) (fun h => h1 (congrArg Subtype.val h))
    (fun h => h2 (congrArg Subtype.val h)) (fun h => h3 (congrArg Subtype.val h))
  exact congrArg Subtype.val this

theorem klein_action [Finite G] {T K : Subgroup G} (hT : IsPGroup 2 T) (hKT : K ≤ T)
    (hKn : T ≤ Subgroup.normalizer (K : Set G)) (hK2 : ∀ k ∈ K, k * k = 1)
    (hcard : Nat.card K = 4) :
    (T ⊓ Subgroup.centralizer (K : Set G)).relIndex T ≤ 2 ∧
      (T ⊓ Subgroup.centralizer (K : Set G) ≠ T →
        Nat.card (K ⊓ Subgroup.centralizer (T : Set G) : Subgroup G) = 2) := by
  obtain ⟨k₀, hk₀K, k₁, hk₁K, hk₀1, hk₀c, hk₁1, hk₁0, hen⟩ := klein_basis hT hKT hKn hK2 hcard
  have hk₀2 : k₀ * k₀ = 1 := hK2 k₀ hk₀K
  have hk₁2 : k₁ * k₁ = 1 := hK2 k₁ hk₁K
  have hk₀inv : k₀⁻¹ = k₀ := inv_eq_of_mul_eq_one_right hk₀2
  have hk₁inv : k₁⁻¹ = k₁ := inv_eq_of_mul_eq_one_right hk₁2
  have hact : ∀ τ ∈ T, τ * k₁ * τ⁻¹ = k₁ ∨ τ * k₁ * τ⁻¹ = k₀ * k₁ := by
    intro τ hτ
    have hk' : τ * k₁ * τ⁻¹ ∈ K := (Subgroup.mem_normalizer_iff.mp (hKn hτ) k₁).mp hk₁K
    have hτ0 : τ * k₀ * τ⁻¹ = k₀ := by rw [hk₀c τ hτ]; group
    rcases hen _ hk' with h | h | h | h
    · exfalso
      apply hk₁1
      have h3 := congrArg (fun x => τ⁻¹ * x * τ) h
      have e : τ⁻¹ * (τ * k₁ * τ⁻¹) * τ = k₁ := by group
      simp only [e, mul_one, inv_mul_cancel] at h3
      exact h3
    · exfalso
      apply hk₁0
      have h2 : τ * k₁ * τ⁻¹ = τ * k₀ * τ⁻¹ := by rw [h, hτ0]
      have h3 := congrArg (fun x => τ⁻¹ * x * τ) h2
      have e1 : τ⁻¹ * (τ * k₁ * τ⁻¹) * τ = k₁ := by group
      have e2 : τ⁻¹ * (τ * k₀ * τ⁻¹) * τ = k₀ := by group
      simp only [e1, e2] at h3
      exact h3
    · exact Or.inl h
    · exact Or.inr h
  have hcen : ∀ τ ∈ T, τ ∈ Subgroup.centralizer (K : Set G) ↔ τ * k₁ * τ⁻¹ = k₁ := by
    intro τ hτ
    constructor
    · intro h
      have := Subgroup.mem_centralizer_iff.mp h k₁ hk₁K
      rw [← this]; group
    · intro h
      have hτ1 : k₁ * τ = τ * k₁ := by
        have := congrArg (· * τ) h
        simpa [mul_assoc] using this.symm
      rw [Subgroup.mem_centralizer_iff]
      intro k hk
      rcases hen k hk with rfl | rfl | rfl | rfl
      · simp
      · exact (hk₀c τ hτ).symm
      · exact hτ1
      · rw [mul_assoc, hτ1, ← mul_assoc, ← hk₀c τ hτ, mul_assoc]
  have hmoved : ∀ τ ∈ T, τ ∉ Subgroup.centralizer (K : Set G) → τ * k₁ * τ⁻¹ = k₀ * k₁ := by
    intro τ hτ hτC
    rcases hact τ hτ with h | h
    · exact absurd ((hcen τ hτ).mpr h) hτC
    · exact h
  have hprod : ∀ σ ∈ T, ∀ τ ∈ T, σ ∉ Subgroup.centralizer (K : Set G) →
      τ ∉ Subgroup.centralizer (K : Set G) → σ * τ ∈ Subgroup.centralizer (K : Set G) := by
    intro σ hσ τ hτ hσC hτC
    refine (hcen (σ * τ) (T.mul_mem hσ hτ)).mpr ?_
    have hσ' := hmoved σ hσ hσC
    have hτ' := hmoved τ hτ hτC
    have hσ0 : σ * k₀ * σ⁻¹ = k₀ := by rw [hk₀c σ hσ]; group
    calc σ * τ * k₁ * (σ * τ)⁻¹ = σ * (τ * k₁ * τ⁻¹) * σ⁻¹ := by group
      _ = σ * (k₀ * k₁) * σ⁻¹ := by rw [hτ']
      _ = (σ * k₀ * σ⁻¹) * (σ * k₁ * σ⁻¹) := by group
      _ = k₀ * (k₀ * k₁) := by rw [hσ0, hσ']
      _ = k₁ := by rw [← mul_assoc, hk₀2, one_mul]
  constructor
  · by_cases hC : T ≤ Subgroup.centralizer (K : Set G)
    · have : T ⊓ Subgroup.centralizer (K : Set G) = T := inf_eq_left.mpr hC
      rw [this, Subgroup.relIndex_self]; norm_num
    · obtain ⟨τ, hτT, hτC⟩ : ∃ τ ∈ T, τ ∉ Subgroup.centralizer (K : Set G) := by
        by_contra hcon
        push Not at hcon
        exact hC fun a ha => hcon a ha
      have h2 : (T ⊓ Subgroup.centralizer (K : Set G)).relIndex T = 2 := by
        rw [Subgroup.relIndex_eq_two_iff_exists_notMem_and]
        refine ⟨τ, hτT, fun h => hτC h.2, fun b hb => ?_⟩
        by_cases hbC : b ∈ Subgroup.centralizer (K : Set G)
        · exact Or.inr ⟨hb, hbC⟩
        · exact Or.inl ⟨T.mul_mem hb hτT, hprod b hb τ hτT hbC hτC⟩
      rw [h2]
  · intro hne
    have hC : ¬ T ≤ Subgroup.centralizer (K : Set G) := fun h => hne (inf_eq_left.mpr h)
    obtain ⟨τ, hτT, hτC⟩ : ∃ τ ∈ T, τ ∉ Subgroup.centralizer (K : Set G) := by
      by_contra hcon
      push Not at hcon
      exact hC fun a ha => hcon a ha
    have hτ' := hmoved τ hτT hτC
    have hτ0 : τ * k₀ * τ⁻¹ = k₀ := by rw [hk₀c τ hτT]; group
    have hord : orderOf k₀ = 2 := by
      have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      exact orderOf_eq_prime (by rw [sq]; exact hk₀2) hk₀1
    have heq : K ⊓ Subgroup.centralizer (T : Set G) = Subgroup.zpowers k₀ := by
      ext x
      constructor
      · rintro ⟨hxK, hxC⟩
        have hxτ : τ * x * τ⁻¹ = x := by
          have := Subgroup.mem_centralizer_iff.mp hxC τ hτT
          rw [this]; group
        rcases hen x hxK with rfl | rfl | rfl | rfl
        · exact Subgroup.one_mem _
        · exact Subgroup.mem_zpowers _
        · exfalso
          rw [hτ'] at hxτ
          apply hk₀1
          have := congrArg (fun y => k₀⁻¹ * y) hxτ
          simpa using this
        · exfalso
          have h1 : τ * (k₀ * k₁) * τ⁻¹ = k₁ := by
            calc τ * (k₀ * k₁) * τ⁻¹ = (τ * k₀ * τ⁻¹) * (τ * k₁ * τ⁻¹) := by group
              _ = k₀ * (k₀ * k₁) := by rw [hτ0, hτ']
              _ = k₁ := by rw [← mul_assoc, hk₀2, one_mul]
          rw [h1] at hxτ
          apply hk₀1
          have := congrArg (fun y => y * k₁⁻¹) hxτ
          simp only [mul_inv_cancel, ] at this
          simpa using this.symm
      · intro hx
        obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
        refine ⟨Subgroup.zpow_mem _ hk₀K k, Subgroup.mem_centralizer_iff.mpr ?_⟩
        intro t ht
        have h1 : t * k₀ = k₀ * t := hk₀c t ht
        have : Commute t k₀ := h1
        exact ((this.symm.zpow_left k).eq).symm
    rw [heq, Nat.card_zpowers, hord]

end S152N2

end CFSG.Quasithin

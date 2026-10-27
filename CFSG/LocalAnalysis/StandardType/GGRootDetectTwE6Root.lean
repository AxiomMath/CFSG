module

public import CFSG.LocalAnalysis.StandardType.GGRootDetectTwE6Field
public import CFSG.LocalAnalysis.StandardType.GGRootDetectExcCore

public section

namespace CFSG.StandardType

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint

namespace RootDetectTwE6


variable {τ : Tag} (F : RootOperatorFamily τ) {K : Type} [Field K]

theorem exists_cubic_of_conj_elt_on (α : Root τ) (M : (Module.End K (RootModule τ K))ˣ)
    (σ : K → K) {s : K} (hs : s ≠ 0) (T : Set K)
    (h : ∀ t ∈ T, ((M⁻¹ : (Module.End K (RootModule τ K))ˣ) : Module.End K (RootModule τ K)) *
      F.elt K α (s * t) * (M : Module.End K (RootModule τ K)) = F.elt K α (s * σ t)) :
    ∃ d : K, d ≠ 0 ∧ ∃ e₁ e₂ e₃ : K, ∀ t ∈ T, d * σ t = e₁ * t + e₂ * t ^ 2 + e₃ * t ^ 3 := by
  obtain ⟨a, b, hab⟩ := RootOperatorFamily'.exists_D_one_apply_ne_zero F (R := K) α
  have hshift : labelWt τ a = labelWt τ b + α.1 := by
    have := F.mapsLabelWt_D (R := K) α le_rfl a b hab
    rwa [one_nsmul] at this
  have hba : b ≠ a := by
    rintro rfl
    exact α.2.ne_zero (by simpa using hshift)
  set Mk : ℕ → K := fun k =>
    (((M⁻¹ : (Module.End K (RootModule τ K))ˣ) : Module.End K (RootModule τ K)) *
      F.D K α k * (M : Module.End K (RootModule τ K))) (Finsupp.single b 1) a with hMk
  have hM0 : Mk 0 = 0 := by
    simp only [hMk, F.D_zero, mul_one, Units.inv_mul, Module.End.one_apply]
    simp [hba]
  refine ⟨s * F.D K α 1 (Finsupp.single b 1) a, mul_ne_zero hs hab, s * Mk 1, s ^ 2 * Mk 2,
    s ^ 3 * Mk 3, fun t ht => ?_⟩
  have e := congrArg (fun A : Module.End K (RootModule τ K) => A (Finsupp.single b 1) a) (h t ht)
  rw [RootOperatorFamily'.elt_apply_of_shift F α (s * σ t) hshift] at e
  have e' : s * F.D K α 1 (Finsupp.single b 1) a * σ t =
      s * σ t * F.D K α 1 (Finsupp.single b 1) a := by
    ring
  rw [e', ← e, RootOperatorFamily.elt, Finset.mul_sum, Finset.sum_mul, LinearMap.sum_apply,
    Finsupp.finsetSum_apply]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, mul_smul_comm, smul_mul_assoc,
    LinearMap.smul_apply, Finsupp.smul_apply, smul_eq_mul]
  have h0 := hM0
  simp only [hMk] at h0
  rw [h0]
  simp only [hMk]
  ring

theorem exists_pow_mul_pow_of_conj_pair (α β : Root τ) (hαβ : β.1 ≠ α.1)
    (φ : (Fin τ.rank → ℤ) →+ ℤ) (hφα : 1 ≤ φ α.1) (hφβ : φ α.1 ≤ φ β.1)
    (M : (Module.End K (RootModule τ K))ˣ) (θ σ : K → K) {s₁ s₂ : K} (hs₁ : s₁ ≠ 0)
    (h : ∀ t, ((M⁻¹ : (Module.End K (RootModule τ K))ˣ) : Module.End K (RootModule τ K)) *
      (F.elt K α (s₁ * t) * F.elt K β (s₂ * θ t)) * (M : Module.End K (RootModule τ K)) =
        F.elt K α (s₁ * σ t) * F.elt K β (s₂ * θ (σ t))) :
    ∃ d : K, d ≠ 0 ∧ ∃ e : ℕ → ℕ → K, ∀ t, d * σ t =
      ∑ k ∈ Finset.range 4, ∑ l ∈ Finset.range 4, e k l * (t ^ k * θ t ^ l) := by
  classical
  obtain ⟨a, b, hab⟩ := RootOperatorFamily'.exists_D_one_apply_ne_zero F (R := K) α
  have hshift : labelWt τ a = labelWt τ b + α.1 := by
    have := F.mapsLabelWt_D (R := K) α le_rfl a b hab
    rwa [one_nsmul] at this
  have hentry : ∀ x y : K, (F.elt K α x * F.elt K β y) (Finsupp.single b 1) a =
      x * F.D K α 1 (Finsupp.single b 1) a := by
    intro x y
    let c : (Fin τ.rank → ℤ) → K := fun γ => if γ = α.1 then x else y
    have hp := RootOperatorFamily'.prod_apply_of_shift F (φ := φ) α.2 hφα c hshift [β.1]
      (fun γ hγ => by
        rw [List.mem_singleton] at hγ
        subst hγ
        exact ⟨hαβ, hφβ⟩)
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one,
      RootOperatorFamily'.eltOr_of_isRoot F K α.2, RootOperatorFamily'.eltOr_of_isRoot F K β.2,
      c, hαβ, ↓reduceIte] at hp
    exact hp
  set E : ℕ → ℕ → K := fun k l =>
    (((M⁻¹ : (Module.End K (RootModule τ K))ˣ) : Module.End K (RootModule τ K)) *
      (F.D K α k * F.D K β l) * (M : Module.End K (RootModule τ K))) (Finsupp.single b 1) a
    with hE
  refine ⟨s₁ * F.D K α 1 (Finsupp.single b 1) a, mul_ne_zero hs₁ hab,
    fun k l => s₁ ^ k * s₂ ^ l * E k l, fun t => ?_⟩
  have e := congrArg (fun A : Module.End K (RootModule τ K) => A (Finsupp.single b 1) a) (h t)
  rw [hentry] at e
  have e' : s₁ * F.D K α 1 (Finsupp.single b 1) a * σ t =
      s₁ * σ t * F.D K α 1 (Finsupp.single b 1) a := by ring
  rw [e', ← e]
  simp only [RootOperatorFamily.elt, Finset.sum_mul, Finset.mul_sum, LinearMap.sum_apply,
    Finsupp.finsetSum_apply, smul_mul_assoc, mul_smul_comm, LinearMap.smul_apply,
    Finsupp.smul_apply, smul_eq_mul, hE]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
  rw [mul_pow, mul_pow]
  ring

theorem fixed_or_sq_of_cubic_cases [CharP K 2] (Fs : Subfield K) (σ : K →+* K)
    (h : (∀ t ∈ Fs, σ t = t) ∨ (∀ t ∈ Fs, σ t = t ^ 2) ∨ (∀ t ∈ Fs, σ t = t ^ 3)) :
    (∀ t ∈ Fs, σ t = t) ∨ (∀ t ∈ Fs, σ t = t ^ 2) := by
  rcases h with h | h | h
  · exact Or.inl h
  · exact Or.inr h
  · left
    intro t ht
    have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
    have e := h (t + 1) (add_mem ht (one_mem _))
    rw [map_add, map_one, h t ht] at e
    have e3 : t * (t + 1) = 0 := by linear_combination -e - (t ^ 2 + t) * h2
    rcases mul_eq_zero.mp e3 with e0 | e0
    · rw [e0, map_zero]
    · have : t = 1 := by linear_combination e0 - h2
      rw [this, map_one]

theorem eq_one_of_conj_fixed [CharP K 2] (θ : K →+* K) (hθ : ∀ c, θ (θ c) = c) (α : Root τ)
    {s : K} (hs : s ≠ 0) {σ : K ≃+* K} (hσs : σ s = s) (hcomm : ∀ x, σ (θ x) = θ (σ x))
    {p : ℕ} (hp : Odd p) (hσp : σ ^ p = 1) (N : ModGL τ K)
    (h : ∀ c, θ c = c →
      N * Units.map (entrywiseHom σ.toRingHom) (F.eltUnit K α (s * c)) * N⁻¹ =
        F.eltUnit K α (s * c)) : σ = 1 := by
  set Fs : Subfield K := θ.eqLocusField (RingHom.id K) with hFs
  have hmem : ∀ c, c ∈ Fs ↔ θ c = c := fun c => Iff.rfl
  have hmap : ∀ c, Units.map (entrywiseHom σ.toRingHom) (F.eltUnit K α (s * c)) =
      F.eltUnit K α (s * σ c) := by
    intro c
    rw [RootDetectExc.units_map_entrywiseHom_eltUnit, map_mul, hσs]
  have hcomm' : ∀ x, σ⁻¹ (θ x) = θ (σ⁻¹ x) := by
    intro x
    apply σ.injective
    change σ (σ.symm (θ x)) = σ (θ (σ.symm x))
    rw [RingEquiv.apply_symm_apply, hcomm, RingEquiv.apply_symm_apply]
  have h1 : ∀ t ∈ (Fs : Set K), ((N⁻¹ : ModGL τ K) : Module.End K (RootModule τ K)) *
      F.elt K α (s * t) * (N : Module.End K (RootModule τ K)) = F.elt K α (s * σ t) := by
    intro t ht
    have e := h t ((hmem t).1 ht)
    rw [hmap] at e
    have e' : F.eltUnit K α (s * σ t) = N⁻¹ * F.eltUnit K α (s * t) * N := by
      rw [← e]; group
    exact (congrArg Units.val e').symm
  have h2 : ∀ t ∈ (Fs : Set K), ((N⁻¹⁻¹ : ModGL τ K) : Module.End K (RootModule τ K)) *
      F.elt K α (s * t) * ((N⁻¹ : ModGL τ K) : Module.End K (RootModule τ K)) =
        F.elt K α (s * σ⁻¹ t) := by
    intro t ht
    have hσt : θ (σ⁻¹ t) = σ⁻¹ t := by rw [← hcomm', (hmem t).1 ht]
    have e := h (σ⁻¹ t) hσt
    rw [hmap] at e
    have hσσ : σ (σ⁻¹ t) = t := σ.apply_symm_apply t
    rw [hσσ] at e
    rw [inv_inv]
    exact congrArg Units.val e
  have hc1 : (∀ c, θ c = c → σ c = c) ∨ (∀ c, θ c = c → σ c = c ^ 2) := by
    obtain ⟨d, hd, e₁, e₂, e₃, he⟩ := exists_cubic_of_conj_elt_on F α N σ hs Fs h1
    rcases fixed_or_sq_of_cubic_cases Fs σ.toRingHom
      (cases_of_cubic_on Fs σ.toMonoidHom hd he) with h' | h'
    · exact Or.inl fun c hc => h' c ((hmem c).2 hc)
    · exact Or.inr fun c hc => h' c ((hmem c).2 hc)
  have hc2 : (∀ c, θ c = c → σ⁻¹ c = c) ∨ (∀ c, θ c = c → σ⁻¹ c = c ^ 2) := by
    obtain ⟨d, hd, e₁, e₂, e₃, he⟩ := exists_cubic_of_conj_elt_on F α N⁻¹ (σ⁻¹ : K ≃+* K) hs Fs h2
    rcases fixed_or_sq_of_cubic_cases Fs (σ⁻¹ : K ≃+* K).toRingHom
      (cases_of_cubic_on Fs (σ⁻¹ : K ≃+* K).toMonoidHom hd he) with h' | h'
    · exact Or.inl fun c hc => h' c ((hmem c).2 hc)
    · exact Or.inr fun c hc => h' c ((hmem c).2 hc)
  exact eq_one_of_fixed_or_sq θ hθ hcomm hp hσp hc1 hc2

theorem eq_one_of_conj_pair [CharP K 2] (θ : K →+* K) (hθ : ∀ c, θ (θ c) = c)
    (hne : ∃ b, θ b ≠ b) (α β : Root τ) (hαβ : β.1 ≠ α.1) (φ : (Fin τ.rank → ℤ) →+ ℤ)
    (hφα : 1 ≤ φ α.1) (hφβ : φ α.1 ≤ φ β.1) {s₁ s₂ : K} (hs₁ : s₁ ≠ 0) {σ : K ≃+* K}
    (hσs₁ : σ s₁ = s₁) (hσs₂ : σ s₂ = s₂) (hcomm : ∀ x, σ (θ x) = θ (σ x)) {p : ℕ}
    (hp : Odd p) (hσp : σ ^ p = 1) (N : ModGL τ K)
    (h : ∀ c, N * Units.map (entrywiseHom σ.toRingHom)
      (F.eltUnit K α (s₁ * c) * F.eltUnit K β (s₂ * θ c)) * N⁻¹ =
        F.eltUnit K α (s₁ * c) * F.eltUnit K β (s₂ * θ c)) : σ = 1 := by
  have hmap : ∀ c, Units.map (entrywiseHom σ.toRingHom)
      (F.eltUnit K α (s₁ * c) * F.eltUnit K β (s₂ * θ c)) =
        F.eltUnit K α (s₁ * σ c) * F.eltUnit K β (s₂ * θ (σ c)) := by
    intro c
    rw [map_mul, RootDetectExc.units_map_entrywiseHom_eltUnit,
      RootDetectExc.units_map_entrywiseHom_eltUnit, map_mul, map_mul, hσs₁, hσs₂]
    rw [hcomm]
  have h1 : ∀ t, ((N⁻¹ : ModGL τ K) : Module.End K (RootModule τ K)) *
      (F.elt K α (s₁ * t) * F.elt K β (s₂ * θ t)) * (N : Module.End K (RootModule τ K)) =
        F.elt K α (s₁ * σ t) * F.elt K β (s₂ * θ (σ t)) := by
    intro t
    have e := h t
    rw [hmap] at e
    have e' : F.eltUnit K α (s₁ * σ t) * F.eltUnit K β (s₂ * θ (σ t)) =
        N⁻¹ * (F.eltUnit K α (s₁ * t) * F.eltUnit K β (s₂ * θ t)) * N := by
      rw [← e]; group
    exact (congrArg Units.val e').symm
  have h2 : ∀ t, ((N⁻¹⁻¹ : ModGL τ K) : Module.End K (RootModule τ K)) *
      (F.elt K α (s₁ * t) * F.elt K β (s₂ * θ t)) *
        ((N⁻¹ : ModGL τ K) : Module.End K (RootModule τ K)) =
        F.elt K α (s₁ * σ⁻¹ t) * F.elt K β (s₂ * θ (σ⁻¹ t)) := by
    intro t
    have e := h (σ⁻¹ t)
    rw [hmap] at e
    have hσσ : σ (σ⁻¹ t) = t := σ.apply_symm_apply t
    rw [hσσ] at e
    rw [inv_inv]
    exact congrArg Units.val e
  have hc1 : (∀ c, θ c = c → σ c = c) ∨ (∀ c, θ c = c → σ c = c ^ 2) := by
    obtain ⟨d, hd, e, he⟩ := exists_pow_mul_pow_of_conj_pair F α β hαβ φ hφα hφβ N θ σ hs₁ h1
    obtain ⟨k, hk, l, hl, hkl⟩ := exists_eq_pow_mul_pow θ.toMonoidHom σ.toMonoidHom hd e he
    exact fixed_or_sq_of_eq_pow_mul_pow θ hθ hne σ.toRingHom hk hl hkl
  have hc2 : (∀ c, θ c = c → σ⁻¹ c = c) ∨ (∀ c, θ c = c → σ⁻¹ c = c ^ 2) := by
    obtain ⟨d, hd, e, he⟩ := exists_pow_mul_pow_of_conj_pair F α β hαβ φ hφα hφβ N⁻¹ θ
      (σ⁻¹ : K ≃+* K) hs₁ h2
    obtain ⟨k, hk, l, hl, hkl⟩ := exists_eq_pow_mul_pow θ.toMonoidHom
      (σ⁻¹ : K ≃+* K).toMonoidHom hd e he
    exact fixed_or_sq_of_eq_pow_mul_pow θ hθ hne (σ⁻¹ : K ≃+* K).toRingHom hk hl hkl
  exact eq_one_of_fixed_or_sq θ hθ hcomm hp hσp hc1 hc2

end RootDetectTwE6

end CFSG.StandardType

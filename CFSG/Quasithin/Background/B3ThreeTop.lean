module

public import CFSG.Quasithin.Background.B3ThreeStruct

public section

namespace CFSG.Quasithin.B3

variable {Γ : Type*} [Group Γ] {V : Type*} [CommGroup V] {X : Type*} [CommGroup X]

theorem exists_corr_zero {ρX : Γ →* MulAut X} (hz : ZeroClass ρX) {ρ : Γ →* MulAut V}
    {M : Subgroup V} (hM : ∀ g v, ρ g v * v⁻¹ ∈ M) (φ : ↥M ≃* X)
    (hφ : IsModIso (resAct ρ M (isInv_of_trivQ hM)) ρX φ) (s : V) :
    ∃ m : ↥M, s * (m : V)⁻¹ ∈ fixG ρ := by
  have hp : IsPrin ρX (fun x => φ (dsM ρ hM s x) * (fun _ : Γ => (1 : X)) x) := by
    simpa using hz _ (hφ.isDer (isDer_dsM ρ hM s))
  obtain ⟨m, hm⟩ := exists_corr hM φ hφ s (fun _ => 1) hp
  refine ⟨m, fun g => ?_⟩
  have h := hm g
  simp only [map_one, OneMemClass.coe_one, inv_one] at h
  exact mul_inv_eq_one.1 h

theorem exists_corr_two (hX2 : ∀ x : X, x ^ 2 = 1) {ρX : Γ →* MulAut X} {d₀ : Γ → X}
    (ht : TwoClass ρX d₀) {ρ : Γ →* MulAut V} {M : Subgroup V}
    (hM : ∀ g v, ρ g v * v⁻¹ ∈ M) (φ : ↥M ≃* X)
    (hφ : IsModIso (resAct ρ M (isInv_of_trivQ hM)) ρX φ) (s : V) :
    (∃ m : ↥M, s * (m : V)⁻¹ ∈ fixG ρ) ∨
      ∃ m : ↥M, ∀ x, ρ x (s * (m : V)⁻¹) * (s * (m : V)⁻¹)⁻¹ = ((φ.symm (d₀ x) : ↥M) : V) := by
  rcases ht.2.2 _ (hφ.isDer (isDer_dsM ρ hM s)) with hp | hp
  · left
    have hp' : IsPrin ρX (fun x => φ (dsM ρ hM s x) * (fun _ : Γ => (1 : X)) x) := by
      simpa using hp
    obtain ⟨m, hm⟩ := exists_corr hM φ hφ s (fun _ => 1) hp'
    refine ⟨m, fun g => ?_⟩
    have h := hm g
    simp only [map_one, OneMemClass.coe_one, inv_one] at h
    exact mul_inv_eq_one.1 h
  · right
    obtain ⟨m, hm⟩ := exists_corr hM φ hφ s d₀ hp
    refine ⟨m, fun x => ?_⟩
    rw [hm x]
    have h2 : (φ.symm (d₀ x)) * (φ.symm (d₀ x)) = 1 := by
      rw [← map_mul, ← pow_two, hX2, map_one]
    have h3 : ((φ.symm (d₀ x) : ↥M) : V) * ((φ.symm (d₀ x) : ↥M) : V) = 1 := by
      have := congrArg Subtype.val h2
      simpa using this
    exact inv_eq_of_mul_eq_one_right h3

theorem top_classify_two (hX2 : ∀ x : X, x ^ 2 = 1) {ρX : Γ →* MulAut X} {d₀ : Γ → X}
    (ht : TwoClass ρX d₀) {ρ : Γ →* MulAut V} {M : Subgroup V}
    (hM : ∀ g v, ρ g v * v⁻¹ ∈ M) (φ : ↥M ≃* X)
    (hφ : IsModIso (resAct ρ M (isInv_of_trivQ hM)) ρX φ) :
    M ⊔ fixG ρ = ⊤ ∨ ∃ s₁ : V, s₁ ∉ M ⊔ fixG ρ ∧
      (∀ x, ρ x s₁ * s₁⁻¹ = ((φ.symm (d₀ x) : ↥M) : V)) ∧
        (M ⊔ fixG ρ) ⊔ Subgroup.zpowers s₁ = ⊤ := by
  by_cases hall : ∀ s : V, ∃ m : ↥M, s * (m : V)⁻¹ ∈ fixG ρ
  · left
    rw [eq_top_iff]
    intro s _
    obtain ⟨m, hm⟩ := hall s
    have h1 : (s * (m : V)⁻¹) * (m : V) ∈ fixG ρ ⊔ M := Subgroup.mul_mem_sup hm m.2
    rw [show (s * (m : V)⁻¹) * (m : V) = s by simp, sup_comm] at h1
    exact h1
  · right
    push Not at hall
    obtain ⟨s₀, hs₀⟩ := hall
    rcases exists_corr_two hX2 ht hM φ hφ s₀ with h | ⟨m, hm⟩
    · obtain ⟨m, hm⟩ := h
      exact absurd hm (hs₀ m)
    · set s₁ : V := s₀ * (m : V)⁻¹ with hs₁
      have hs₁d : ∀ x, ρ x s₁ * s₁⁻¹ = ((φ.symm (d₀ x) : ↥M) : V) := hm
      have hs₁n : s₁ ∉ M ⊔ fixG ρ := by
        intro h
        obtain ⟨a, ha, c, hc, hac⟩ := Subgroup.mem_sup.1 h
        apply hs₀ (⟨a, ha⟩ * m)
        have : s₀ * (((⟨a, ha⟩ * m : ↥M)) : V)⁻¹ = c := by
          have e : s₀ = s₁ * (m : V) := by simp [hs₁]
          rw [e, ← hac]
          calc a * c * (m : V) * (((⟨a, ha⟩ * m : ↥M)) : V)⁻¹
              = c * (a * a⁻¹) * ((m : V) * (m : V)⁻¹) := by
                simp only [Subgroup.coe_mul, mul_inv]
                ac_rfl
            _ = c := by simp
        rw [this]
        exact hc
      refine ⟨s₁, hs₁n, hs₁d, ?_⟩
      set S : Subgroup V := (M ⊔ fixG ρ) ⊔ Subgroup.zpowers s₁ with hS
      have hMS : M ≤ S := le_sup_of_le_left le_sup_left
      have hCS : fixG ρ ≤ S := le_sup_of_le_left le_sup_right
      have hs₁S : s₁ ∈ S := Subgroup.mem_sup_right (Subgroup.mem_zpowers s₁)
      rw [eq_top_iff]
      intro s _
      rcases exists_corr_two hX2 ht hM φ hφ s with ⟨m', hm'⟩ | ⟨m', hm'⟩
      · have : s = (s * (m' : V)⁻¹) * (m' : V) := by simp
        rw [this]
        exact S.mul_mem (hCS hm') (hMS m'.2)
      · set t : V := s * (m' : V)⁻¹ with ht'
        have hfix : t * s₁⁻¹ ∈ fixG ρ := by
          intro g
          have h1 : ρ g t = ((φ.symm (d₀ g) : ↥M) : V) * t := by
            have := hm' g
            rw [← this]
            simp
          have h2 : ρ g s₁ = ((φ.symm (d₀ g) : ↥M) : V) * s₁ := by
            rw [← hs₁d g]
            simp
          rw [map_mul, map_inv, h1, h2]
          simp [mul_comm, mul_left_comm]
        have : s = (t * s₁⁻¹) * s₁ * (m' : V) := by simp [ht']
        rw [this]
        exact S.mul_mem (S.mul_mem (hCS hfix) hs₁S) (hMS m'.2)

end CFSG.Quasithin.B3

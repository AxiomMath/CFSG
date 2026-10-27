module

public import CFSG.Quasithin.Background.JonesParshallSmallSL

public section

namespace CFSG.Quasithin.SzN28

open Matrix CFSG.Quasithin.JonesParshall

theorem h1_four {K : Type*} [Group K] {M : Type*} [AddCommGroup M]
    [Module (ZMod 2) M] (hM : Module.finrank (ZMod 2) M = 4) (θ : K →* Module.End (ZMod 2) M)
    (hθ : ∀ g : M ≃ₗ[ZMod 2] M, ∃ k, θ k = (g : M →ₗ[ZMod 2] M)) (δ : K → M)
    (hδ : ∀ k l, δ (k * l) = δ k + θ k (δ l)) (hker : ∀ k, θ k = 1 → δ k = 0) :
    ∃ n : M, ∀ k, δ k = θ k n - n := by
  classical
  have : Module.Finite (ZMod 2) M := Module.finite_of_finrank_pos (by omega)
  let e : M ≃ₗ[ZMod 2] (Fin 4 → ZMod 2) :=
    LinearEquiv.ofFinrankEq M (Fin 4 → ZMod 2) (by simp [hM])
  let T : SpecialLinearGroup (Fin 4) (ZMod 2) → Module.End (ZMod 2) M := fun g =>
    e.symm.toLinearMap ∘ₗ Matrix.toLin' (g : Matrix (Fin 4) (Fin 4) (ZMod 2)) ∘ₗ e.toLinearMap
  have hTmul : ∀ g h, T (g * h) = T g * T h := by
    intro g h
    apply LinearMap.ext
    intro x
    simp [T, Matrix.toLin'_mul]
  have hTone : T 1 = 1 := by
    apply LinearMap.ext
    intro x
    simp [T]
  have hTapp : ∀ g x, e (T g x) = (g : Matrix (Fin 4) (Fin 4) (ZMod 2)) *ᵥ e x := by
    intro g x
    simp [T]
  have hTinv : ∀ g, T g * T g⁻¹ = 1 := fun g => by rw [← hTmul, mul_inv_cancel, hTone]
  have hTinv' : ∀ g, T g⁻¹ * T g = 1 := fun g => by rw [← hTmul, inv_mul_cancel, hTone]
  let Tl : SpecialLinearGroup (Fin 4) (ZMod 2) → (M ≃ₗ[ZMod 2] M) := fun g =>
    LinearEquiv.ofLinearMap (T g) (T g⁻¹) (hTinv g) (hTinv' g)
  have hkof : ∀ g, ∃ k, θ k = T g := fun g => hθ (Tl g)
  choose kof hkof using hkof
  have hδθ : ∀ k k', θ k = θ k' → δ k = δ k' := by
    intro k k' h
    have h1 : θ (k⁻¹ * k') = 1 := by
      rw [map_mul, ← h, ← map_mul, inv_mul_cancel, map_one]
    have h2 := hδ k (k⁻¹ * k')
    rw [mul_inv_cancel_left, hker _ h1, map_zero, add_zero] at h2
    exact h2.symm
  have hSL : ∀ k, ∃ g : SpecialLinearGroup (Fin 4) (ZMod 2), T g = θ k := by
    intro k
    let A : Matrix (Fin 4) (Fin 4) (ZMod 2) :=
      LinearMap.toMatrix' (e.toLinearMap ∘ₗ θ k ∘ₗ e.symm.toLinearMap)
    let A' : Matrix (Fin 4) (Fin 4) (ZMod 2) :=
      LinearMap.toMatrix' (e.toLinearMap ∘ₗ θ k⁻¹ ∘ₗ e.symm.toLinearMap)
    have hAA' : A * A' = 1 := by
      rw [← LinearMap.toMatrix'_comp]
      have : (e.toLinearMap ∘ₗ θ k ∘ₗ e.symm.toLinearMap) ∘ₗ
          (e.toLinearMap ∘ₗ θ k⁻¹ ∘ₗ e.symm.toLinearMap) = LinearMap.id := by
        apply LinearMap.ext
        intro x
        have h1 : θ k (θ k⁻¹ (e.symm x)) = e.symm x := by
          rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one]
          rfl
        simp [h1]
      rw [this]
      exact LinearMap.toMatrix'_id
    have hdet : A.det = 1 := by
      have h := congrArg Matrix.det hAA'
      rw [Matrix.det_mul, Matrix.det_one] at h
      have key : ∀ x y : ZMod 2, x * y = 1 → x = 1 := by decide
      exact key _ _ h
    obtain ⟨g, hgA⟩ : ∃ g : SpecialLinearGroup (Fin 4) (ZMod 2),
        (g : Matrix (Fin 4) (Fin 4) (ZMod 2)) = A := ⟨⟨A, hdet⟩, rfl⟩
    refine ⟨g, ?_⟩
    apply LinearMap.ext
    intro x
    apply e.injective
    refine (hTapp g x).trans ?_
    rw [hgA]
    have : A *ᵥ e x = (e.toLinearMap ∘ₗ θ k ∘ₗ e.symm.toLinearMap) (e x) := by
      rw [← Matrix.toLin'_apply, Matrix.toLin'_toMatrix']
    rw [this]
    simp
  let f : SpecialLinearGroup (Fin 4) (ZMod 2) → (Fin 4 → ZMod 2) := fun g => e (δ (kof g))
  have hf : f ∈ Z1A (muF2 4) := by
    intro g h
    have h1 : θ (kof (g * h)) = θ (kof g * kof h) := by
      rw [hkof, map_mul, hkof, hkof, hTmul]
    change e (δ (kof (g * h))) = e (δ (kof g)) + (g : Matrix (Fin 4) (Fin 4) (ZMod 2)) *ᵥ
      e (δ (kof h))
    rw [hδθ _ _ h1, hδ, map_add, hkof, hTapp]
  have hB : f ∈ B1A (muF2 4) := by
    rw [← Z1A_eq_B1A_four]
    exact hf
  obtain ⟨v, hv⟩ := hB
  refine ⟨e.symm v, fun k => ?_⟩
  obtain ⟨g, hg⟩ := hSL k
  have hθk : θ k = θ (kof g) := by rw [hkof, hg]
  have h1 : δ k = δ (kof g) := hδθ _ _ hθk
  have h2 : f g = (g : Matrix (Fin 4) (Fin 4) (ZMod 2)) *ᵥ v - v := by
    have := congrFun hv g
    exact this.symm
  rw [h1]
  apply e.injective
  rw [map_sub, ← hg, hTapp, LinearEquiv.apply_symm_apply]
  exact h2

end CFSG.Quasithin.SzN28

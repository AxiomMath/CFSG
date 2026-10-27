module

public import CFSG.Quasithin.Vol2.Ch8Sec2L828USL2Hom
public import CFSG.Quasithin.Vol2.Ch8Sec2L828USL2

public section

namespace CFSG.Quasithin.H13

section Th

variable {F M : Type} [Field F] [AddCommGroup M] [Module F M]

theorem ob5_det_E (b : Module.Basis (Fin 2) F M) :
    (LinearMap.toMatrix b b (ob5E b)).det = 1 := by
  have h0 : ob5E b (b 0) = b 0 := ob5E_zero b
  have h1 : ob5E b (b 1) = b 0 + b 1 := by
    simpa using ob5E_apply b 0 1
  have hm : LinearMap.toMatrix b b (ob5E b) = !![1, 1; 0, 1] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [LinearMap.toMatrix_apply, h0, h1, Module.Basis.repr_self, Finsupp.single_apply]
  rw [hm, Matrix.det_fin_two_of]
  ring

theorem ob5_det_Dg (b : Module.Basis (Fin 2) F M) {μ : F} (hμ : μ ≠ 0) :
    (LinearMap.toMatrix b b (ob5Dg b μ)).det = 1 := by
  have h0 : ob5Dg b μ (b 0) = μ • b 0 := ob5Dg_zero b μ
  have h1 : ob5Dg b μ (b 1) = μ⁻¹ • b 1 := ob5Dg_one b μ
  have hm : LinearMap.toMatrix b b (ob5Dg b μ) = !![μ, 0; 0, μ⁻¹] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [LinearMap.toMatrix_apply, h0, h1, Module.Basis.repr_self, Finsupp.single_apply]
  rw [hm, Matrix.det_fin_two_of]
  simp [mul_inv_cancel₀ hμ]

theorem ob5_det_Wr (b : Module.Basis (Fin 2) F M) :
    (LinearMap.toMatrix b b (ob5Wr b)).det = 1 := by
  have h0 : ob5Wr b (b 0) = b 1 := ob5Wr_zero b
  have h1 : ob5Wr b (b 1) = -b 0 := by
    simpa using ob5Wr_apply b 0 1
  have hm : LinearMap.toMatrix b b (ob5Wr b) = !![0, -1; 1, 0] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [LinearMap.toMatrix_apply, h0, h1, Module.Basis.repr_self, Finsupp.single_apply]
  rw [hm, Matrix.det_fin_two_of]
  ring

theorem ob5_realize {K : Type} [Group K] (b : Module.Basis (Fin 2) F M)
    (φ : K →* (M →ₗ[F] M)ˣ) (θ : K →* Matrix.SpecialLinearGroup (Fin 2) F)
    (hθ : ∀ κ : K, ((θ κ : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) =
      ob5mat b (φ κ))
    (hsurj : Function.Surjective θ) (ℓ : M →ₗ[F] M)
    (hℓ : (LinearMap.toMatrix b b ℓ).det = 1) :
    ∃ κ : K, ((φ κ : (M →ₗ[F] M)ˣ) : M →ₗ[F] M) = ℓ := by
  obtain ⟨κ, hκ⟩ := hsurj ⟨LinearMap.toMatrix b b ℓ, hℓ⟩
  refine ⟨κ, ?_⟩
  apply (LinearMap.toMatrixAlgEquiv b).injective
  have h := hθ κ
  rw [hκ] at h
  exact h.symm

theorem ob5_scalar_of_surj {K : Type} [Group K] (b : Module.Basis (Fin 2) F M)
    (φ : K →* (M →ₗ[F] M)ˣ) (θ : K →* Matrix.SpecialLinearGroup (Fin 2) F)
    (hθ : ∀ κ : K, ((θ κ : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) =
      ob5mat b (φ κ))
    (hsurj : Function.Surjective θ) (ρv : M →+ M)
    (hcomm : ∀ (κ : K) (m : M), ((φ κ : (M →ₗ[F] M)ˣ) : M →ₗ[F] M) (ρv m) =
      ρv (((φ κ : (M →ₗ[F] M)ˣ) : M →ₗ[F] M) m)) :
    ∃ α : F, ∀ w : M, ρv w = α • w := by
  apply ob5_commutant_scalar b ρv
  · intro w
    obtain ⟨κ, hκ⟩ := ob5_realize b φ θ hθ hsurj (ob5E b) (ob5_det_E b)
    have h := hcomm κ w
    rw [hκ] at h
    exact h.symm
  · intro μ hμ w
    obtain ⟨κ, hκ⟩ := ob5_realize b φ θ hθ hsurj (ob5Dg b μ) (ob5_det_Dg b hμ)
    have h := hcomm κ w
    rw [hκ] at h
    exact h.symm
  · intro w
    obtain ⟨κ, hκ⟩ := ob5_realize b φ θ hθ hsurj (ob5Wr b) (ob5_det_Wr b)
    have h := hcomm κ w
    rw [hκ] at h
    exact h.symm

end Th

section ZeroDiv

variable {ι N : Type} [AddCommGroup N] [Module (ZMod 2) N]

theorem ob5_zero_div_end (b : Module.Basis ι (ZMod 2) N) {i j : ι} (hij : i ≠ j) :
    ∃ p q : AddMonoid.End N, p ≠ 0 ∧ q ≠ 0 ∧ p * q = 0 := by
  have hci : b.coord i (b i) = 1 := by
    simp [Module.Basis.coord_apply, Module.Basis.repr_self]
  have hcj : b.coord i (b j) = 0 := by
    simp [Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_apply, hij.symm]
  refine ⟨((b.coord i).smulRight (b i)).toAddMonoidHom,
    ((b.coord i).smulRight (b j)).toAddMonoidHom, ?_, ?_, ?_⟩
  · intro hp
    have h : ((b.coord i).smulRight (b i)).toAddMonoidHom (b i) = 0 := by rw [hp]; rfl
    change b.coord i (b i) • b i = 0 at h
    rw [hci, one_smul] at h
    exact b.ne_zero i h
  · intro hq
    have h : ((b.coord i).smulRight (b j)).toAddMonoidHom (b i) = 0 := by rw [hq]; rfl
    change b.coord i (b i) • b j = 0 at h
    rw [hci, one_smul] at h
    exact b.ne_zero j h
  · ext z
    change b.coord i (b.coord i z • b j) • b i = 0
    rw [map_smul, hcj, smul_zero, zero_smul]

end ZeroDiv

end CFSG.Quasithin.H13

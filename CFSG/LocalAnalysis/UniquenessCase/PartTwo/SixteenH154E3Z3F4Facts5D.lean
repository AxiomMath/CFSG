module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3Z3F4Facts5C

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.LinearAlgebra CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open Matrix

local notation "F" => OmegaField

private noncomputable def s16h_e3_z3f5_matrixLinearHom :
    GL (Fin 3) F ≃* ((Fin 3 → F) ≃ₗ[F] (Fin 3 → F)) :=
  Matrix.GeneralLinearGroup.toLin.trans
    (LinearMap.GeneralLinearGroup.generalLinearEquiv F (Fin 3 → F))

private theorem s16h_e3_z3f5_matrixLinearEquiv_injective :
    Function.Injective (matrixLinearEquiv (d := 3) (K := F)) :=
  s16h_e3_z3f5_matrixLinearHom.injective

private theorem s16h_e3_z3f5_matrixLinearEquiv_inv (A : GL (Fin 3) F) :
    matrixLinearEquiv A⁻¹ = (matrixLinearEquiv A)⁻¹ :=
  map_inv s16h_e3_z3f5_matrixLinearHom A

private theorem s16h_e3_z3f5_coordinateSemilinearMap_inl (A : GL (Fin 3) F)
    (v : Fin 3 → F) :
    coordinateSemilinearMap (SemidirectProduct.inl A) v = matrixLinearEquiv A v := by
  rw [coordinateSemilinearMap_apply, matrixLinearEquiv_apply]
  simp [SemidirectProduct.left_inl, SemidirectProduct.right_inl]

private theorem s16h_e3_z3f5_coordinateSemilinearMap_inl' (A : GL (Fin 3) F)
    (v : Fin 3 → F) :
    coordinateSemilinearMap (SemidirectProduct.inl A) v =
      (Matrix.GeneralLinearGroup.toLin A : Module.End F (Fin 3 → F)) v := by
  rw [s16h_e3_z3f5_coordinateSemilinearMap_inl, matrixLinearEquiv_apply]
  rfl

theorem s16h_e3_z3f5_semilinear_unit_inv {f : (Module.End F (Fin 3 → F))ˣ}
    (hf5 : (f : Module.End F (Fin 3 → F)) ^ 5 = 1)
    {T : (Fin 3 → F) ≃+ (Fin 3 → F)}
    (hτs : ∀ (c : F) (v : Fin 3 → F), T (c • v) = c ^ 2 • T v)
    (hτe : ∀ v, T (s16h_e3_z3f5_e (f : Module.End F (Fin 3 → F)) v) =
      s16h_e3_z3f5_e (f : Module.End F (Fin 3 → F)) (T v))
    {a : (Module.End F (Fin 3 → F))ˣ}
    (ha : a ∈ (s16h_e3_z3f5_diagHom hf5).range) :
    ∀ v, T ((a : Module.End F (Fin 3 → F)) (T.symm v)) =
      ((a⁻¹ : (Module.End F (Fin 3 → F))ˣ) : Module.End F (Fin 3 → F)) v := by
  obtain ⟨p, hp⟩ := MonoidHom.mem_range.mp ha
  have haL : (a : Module.End F (Fin 3 → F)) =
      (p.1 : F) • (1 - s16h_e3_z3f5_e (f : Module.End F (Fin 3 → F))) +
      (p.2 : F) • s16h_e3_z3f5_e (f : Module.End F (Fin 3 → F)) := by
    have := congrArg (fun u : (Module.End F (Fin 3 → F))ˣ => (u : Module.End F (Fin 3 → F))) hp
    simpa using this.symm
  have hα : (p.1 : F) ^ 3 = 1 := congrArg Units.val (s16h_e3_z3f5_unit_pow_three p.1)
  have hμ : (p.2 : F) ^ 3 = 1 := congrArg Units.val (s16h_e3_z3f5_unit_pow_three p.2)
  have hprod : ((p.1 : F) ^ 2 • (1 - s16h_e3_z3f5_e (f : Module.End F (Fin 3 → F))) +
      (p.2 : F) ^ 2 • s16h_e3_z3f5_e (f : Module.End F (Fin 3 → F))) *
      (a : Module.End F (Fin 3 → F)) = 1 := by
    rw [haL]
    exact s16h_e3_z3f5_sq_mul_eq_one hf5 hα hμ
  have hα2 : (p.1 : F) ^ 2 ≠ 0 := by
    intro h
    have h3 := hα
    rw [show (p.1 : F) ^ 3 = (p.1) ^ 2 * p.1 by ring, h, zero_mul] at h3
    exact one_ne_zero h3.symm
  have hμ2 : (p.2 : F) ^ 2 ≠ 0 := by
    intro h
    have h3 := hμ
    rw [show (p.2 : F) ^ 3 = (p.2) ^ 2 * p.2 by ring, h, zero_mul] at h3
    exact one_ne_zero h3.symm
  have hprod' : (a : Module.End F (Fin 3 → F)) *
      ((p.1 : F) ^ 2 • (1 - s16h_e3_z3f5_e (f : Module.End F (Fin 3 → F))) +
       (p.2 : F) ^ 2 • s16h_e3_z3f5_e (f : Module.End F (Fin 3 → F))) = 1 := by
    rw [haL, s16h_e3_z3f5_diag_mul hf5]
    rw [show (p.1 : F) * (p.1) ^ 2 = 1 by rw [← pow_succ', hα],
      show (p.2 : F) * (p.2) ^ 2 = 1 by rw [← pow_succ', hμ]]
    simp
  have hunit : a⁻¹ = s16h_e3_z3f5_diagUnit hf5 (Units.mk0 ((p.1 : F) ^ 2) hα2)
      (Units.mk0 ((p.2 : F) ^ 2) hμ2) := by
    rw [inv_eq_iff_mul_eq_one]
    apply Units.ext
    simp only [s16h_e3_z3f5_diagUnit_val, Units.val_mul]
    exact hprod' 
  have hinv : ((a⁻¹ : (Module.End F (Fin 3 → F))ˣ) : Module.End F (Fin 3 → F)) =
      (p.1 : F) ^ 2 • (1 - s16h_e3_z3f5_e (f : Module.End F (Fin 3 → F))) +
      (p.2 : F) ^ 2 • s16h_e3_z3f5_e (f : Module.End F (Fin 3 → F)) := by
    rw [hunit]
    simp
  intro v
  calc T ((a : Module.End F (Fin 3 → F)) (T.symm v))
      = T (((p.1 : F) • (1 - s16h_e3_z3f5_e (f : Module.End F (Fin 3 → F))) +
          (p.2 : F) • s16h_e3_z3f5_e (f : Module.End F (Fin 3 → F))) (T.symm v)) := by
        rw [haL]
    _ = ((p.1 : F) ^ 2 • (1 - s16h_e3_z3f5_e (f : Module.End F (Fin 3 → F))) +
          (p.2 : F) ^ 2 • s16h_e3_z3f5_e (f : Module.End F (Fin 3 → F))) (T (T.symm v)) :=
        s16h_e3_z3f5_tau_conj T hτs hτe (p.1) (p.2) (T.symm v)
    _ = ((p.1 : F) ^ 2 • (1 - s16h_e3_z3f5_e (f : Module.End F (Fin 3 → F))) +
          (p.2 : F) ^ 2 • s16h_e3_z3f5_e (f : Module.End F (Fin 3 → F))) v := by
        rw [AddEquiv.apply_symm_apply]
    _ = ((a⁻¹ : (Module.End F (Fin 3 → F))ˣ) : Module.End F (Fin 3 → F)) v := by rw [hinv]

theorem s16h_e3_z3f5_semilinear_inverts {f₀ : GL (Fin 3) F}
    (hf5 : (Matrix.GeneralLinearGroup.toLin f₀ : Module.End F (Fin 3 → F)) ^ 5 = 1)
    (hf1 : (Matrix.GeneralLinearGroup.toLin f₀ : Module.End F (Fin 3 → F)) ≠ 1)
    {τ : coordinateSemilinearGroup 3 F}
    (hτnorm : τ ∈ Subgroup.normalizer
      (Subgroup.zpowers (SemidirectProduct.inl f₀ : coordinateSemilinearGroup 3 F) :
        Set (coordinateSemilinearGroup 3 F)))
    (hτright : SemidirectProduct.rightHom τ ≠ 1)
    {a : GL (Fin 3) F}
    (ha : Matrix.GeneralLinearGroup.toLin a ∈
      (s16h_e3_z3f5_diagHom hf5).range) :
    τ * SemidirectProduct.inl a * τ⁻¹ = SemidirectProduct.inl a⁻¹ := by
  have hf0_5 : f₀ ^ 5 = 1 := by
    apply Matrix.GeneralLinearGroup.toLin.injective
    rw [map_pow, show (Matrix.GeneralLinearGroup.toLin f₀) ^ 5 = 1 from Units.ext hf5, map_one]
  have hord_inl : orderOf (SemidirectProduct.inl f₀ : coordinateSemilinearGroup 3 F) = 5 := by
    have h1 : (SemidirectProduct.inl f₀ : coordinateSemilinearGroup 3 F) ^ 5 = 1 := by
      rw [← map_pow, hf0_5, map_one]
    have hdvd : orderOf (SemidirectProduct.inl f₀ : coordinateSemilinearGroup 3 F) ∣ 5 :=
      orderOf_dvd_of_pow_eq_one h1
    rcases (Nat.dvd_prime Nat.prime_five).mp hdvd with h | h
    · exact absurd (orderOf_eq_one_iff.mp h) (fun h0 => hf1 (by
        rw [SemidirectProduct.inl_injective h0, map_one]
        rfl))
    · exact h
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp
    (((Subgroup.mem_normalizer_iff.mp hτnorm) (SemidirectProduct.inl f₀)).1
      (Subgroup.mem_zpowers _))
  let m : ℕ := (k % 5).toNat
  have hm : (m : ℤ) = k % ((5 : ℕ) : ℤ) :=
    Int.toNat_of_nonneg (Int.emod_nonneg _ (by norm_num))
  have hk_eq : (SemidirectProduct.inl f₀ : coordinateSemilinearGroup 3 F) ^ k =
      (SemidirectProduct.inl f₀) ^ m := by
    rw [← zpow_mod_orderOf, hord_inl, ← hm, zpow_natCast]
  have hconj : τ * SemidirectProduct.inl f₀ * τ⁻¹ = SemidirectProduct.inl (f₀ ^ m) := by
    rw [← hk, hk_eq, map_pow]
  have hm_lt : m < 5 := by
    have h1 : (m : ℤ) < 5 := by
      rw [hm]
      exact Int.emod_lt_of_pos _ (by norm_num)
    exact_mod_cast h1
  have hk5 : ¬ 5 ∣ m := by
    intro h5
    have hm0 : m = 0 := by obtain ⟨j, hj⟩ := h5; omega
    have h1 : τ * SemidirectProduct.inl f₀ * τ⁻¹ = 1 := by
      rw [hconj, hm0, pow_zero, map_one]
    have h2 : (SemidirectProduct.inl f₀ : coordinateSemilinearGroup 3 F) = 1 := by
      have := congrArg (fun x : coordinateSemilinearGroup 3 F => τ⁻¹ * x * τ) h1
      simpa [mul_assoc] using this
    have h3 : f₀ = 1 := SemidirectProduct.inl_injective h2
    exact hf1 (by rw [h3, map_one]; rfl)
  have hτ : ∀ v : Fin 3 → F,
      coordinateSemilinearMap τ
        ((Matrix.GeneralLinearGroup.toLin f₀ : Module.End F (Fin 3 → F)) v) =
      ((Matrix.GeneralLinearGroup.toLin f₀ : Module.End F (Fin 3 → F)) ^ m)
        (coordinateSemilinearMap τ v) := by
    intro v
    have hcomp : ∀ w, coordinateSemilinearMap (τ * SemidirectProduct.inl f₀ * τ⁻¹) w =
        coordinateSemilinearMap τ
          ((Matrix.GeneralLinearGroup.toLin f₀ : Module.End F (Fin 3 → F))
            ((coordinateSemilinearMap τ).symm w)) := by
      intro w
      rw [coordinateSemilinearMap_mul, coordinateSemilinearMap_mul, coordinateSemilinearMap_inv,
        s16h_e3_z3f5_coordinateSemilinearMap_inl']
    have h1 : coordinateSemilinearMap (τ * SemidirectProduct.inl f₀ * τ⁻¹)
          (coordinateSemilinearMap τ v) =
        coordinateSemilinearMap τ
          ((Matrix.GeneralLinearGroup.toLin f₀ : Module.End F (Fin 3 → F)) v) := by
      have := hcomp (coordinateSemilinearMap τ v)
      rwa [AddEquiv.symm_apply_apply] at this
    have h2 : coordinateSemilinearMap (τ * SemidirectProduct.inl f₀ * τ⁻¹)
          (coordinateSemilinearMap τ v) =
        (Matrix.GeneralLinearGroup.toLin (f₀ ^ m) : Module.End F (Fin 3 → F))
          (coordinateSemilinearMap τ v) := by
      rw [hconj]
      exact s16h_e3_z3f5_coordinateSemilinearMap_inl' (f₀ ^ m)
        (coordinateSemilinearMap τ v)
    have h3 : (Matrix.GeneralLinearGroup.toLin (f₀ ^ m) : Module.End F (Fin 3 → F)) =
        ((Matrix.GeneralLinearGroup.toLin f₀ : Module.End F (Fin 3 → F)) ^ m) := by
      have := congrArg (fun u : (Module.End F (Fin 3 → F))ˣ =>
        (u : Module.End F (Fin 3 → F))) (map_pow Matrix.GeneralLinearGroup.toLin f₀ m)
      simpa using this
    rw [← h1, h2, h3]
  have hτe : ∀ v, coordinateSemilinearMap τ
        (s16h_e3_z3f5_e (Matrix.GeneralLinearGroup.toLin f₀ : Module.End F (Fin 3 → F)) v) =
      s16h_e3_z3f5_e (Matrix.GeneralLinearGroup.toLin f₀ : Module.End F (Fin 3 → F))
        (coordinateSemilinearMap τ v) :=
    s16h_e3_z3f5_tau_e hf5 (coordinateSemilinearMap τ) hk5 hτ
  have hτs : ∀ (c : F) (v : Fin 3 → F),
      coordinateSemilinearMap τ (c • v) = c ^ 2 • coordinateSemilinearMap τ v := by
    intro c v
    rw [coordinateSemilinearMap_smul, s16h_e3_z3f5_ringEquiv_eq_sq τ.right hτright c]
  have hmain := s16h_e3_z3f5_semilinear_unit_inv hf5 hτs hτe ha
  have hcright : (τ * SemidirectProduct.inl a * τ⁻¹).right = 1 := by
    change SemidirectProduct.rightHom (τ * SemidirectProduct.inl a * τ⁻¹) = 1
    rw [map_mul, map_mul, map_inv, SemidirectProduct.rightHom_inl, mul_one, mul_inv_cancel]
  have hleft : (τ * SemidirectProduct.inl a * τ⁻¹).left = a⁻¹ := by
    apply s16h_e3_z3f5_matrixLinearEquiv_injective
    ext v
    have h1 : matrixLinearEquiv (τ * SemidirectProduct.inl a * τ⁻¹).left v =
        coordinateSemilinearMap (τ * SemidirectProduct.inl a * τ⁻¹) v := by
      rw [coordinateSemilinearMap_apply, matrixLinearEquiv_apply, hcright]
      simp
    have h2 : coordinateSemilinearMap (τ * SemidirectProduct.inl a * τ⁻¹) v =
        coordinateSemilinearMap τ
          ((Matrix.GeneralLinearGroup.toLin a : Module.End F (Fin 3 → F))
            ((coordinateSemilinearMap τ).symm v)) := by
      rw [coordinateSemilinearMap_mul, coordinateSemilinearMap_mul, coordinateSemilinearMap_inv,
        s16h_e3_z3f5_coordinateSemilinearMap_inl']
    have h3 : coordinateSemilinearMap τ
          ((Matrix.GeneralLinearGroup.toLin a : Module.End F (Fin 3 → F))
            ((coordinateSemilinearMap τ).symm v)) = matrixLinearEquiv a⁻¹ v := by
      rw [s16h_e3_z3f5_matrixLinearEquiv_inv]
      exact hmain v
    rw [h1, h2, h3]
  have h1 := SemidirectProduct.inl_left_mul_inr_right (τ * SemidirectProduct.inl a * τ⁻¹)
  rw [hcright, map_one, mul_one, hleft] at h1
  exact h1.symm

end CFSG.LocalAnalysis.UniquenessCase.PartTwo

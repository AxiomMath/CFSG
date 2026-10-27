module

import CFSG.ClassicalGroups.Unitary.Finite
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.K328.Matrix

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.K328

open CFSG.Open
open Matrix Polynomial LinearMap
open scoped Polynomial
open CFSG.LieType.Universal.Unitary CFSG.ClassicalGroups.Unitary

private theorem k328r6c_three_ne_zero {F : Type} [Field F] [CharP F 2] : (3 : F) ≠ 0 := by
  have h2 : (2 : F) = 0 := CharP.cast_eq_zero F 2
  have h31 : (3 : F) = 1 := by rw [show (3 : F) = 2 + 1 by norm_num, h2, zero_add]
  rw [h31]; exact one_ne_zero

private theorem k328r6c_omega_ne_one {F : Type} [Field F] [CharP F 2] {ω : F}
    (hω : ω ^ 2 + ω + 1 = 0) : ω ≠ 1 := by
  intro h
  rw [h] at hω
  have h3 : (3 : F) = 0 := by linear_combination hω
  exact k328r6c_three_ne_zero h3

private theorem k328r6c_omega_pow_three {F : Type} [Field F] {ω : F}
    (hω : ω ^ 2 + ω + 1 = 0) : ω ^ 3 = 1 := by
  linear_combination (ω - 1) * hω

private theorem k328r6c_poly_prod {F : Type} [Field F] [CharP F 2] {ω : F}
    (hω : ω ^ 2 + ω + 1 = 0) :
    (X - C (1 : F)) * (X - C ω) * (X - C (ω ^ 2)) = X ^ 3 - 1 := by
  have h1 : ω + ω ^ 2 = -1 := by linear_combination hω
  have h3 : ω ^ 3 = 1 := k328r6c_omega_pow_three hω
  have h2 : ω * ω ^ 2 = 1 := by rw [← pow_succ', h3]
  have hfac : (X - C ω) * (X - C (ω ^ 2)) = X ^ 2 + X + 1 := by
    calc (X - C ω) * (X - C (ω ^ 2))
        = X ^ 2 - (C ω + C (ω ^ 2)) * X + C ω * C (ω ^ 2) := by ring
      _ = X ^ 2 - C (ω + ω ^ 2) * X + C (ω * ω ^ 2) := by rw [← C_add, ← C_mul]
      _ = X ^ 2 - C (-1) * X + C 1 := by rw [h1, h2]
      _ = X ^ 2 + X + 1 := by simp only [C_neg, C_1]; ring
  rw [mul_assoc, hfac]
  simp only [C_1]
  ring

private theorem k328r6c_eigenspace_finrank_sum {F : Type} [Field F] [CharP F 2]
    (ω : F) (hω : ω ^ 2 + ω + 1 = 0) (Z : (Fin 4 → F) →ₗ[F] (Fin 4 → F))
    (hZ : Z ^ 3 = 1) :
    Module.finrank F (LinearMap.ker (Z - 1)) +
      Module.finrank F (LinearMap.ker (Z - ω • 1)) +
      Module.finrank F (LinearMap.ker (Z - ω ^ 2 • 1)) = 4 := by
  have hωne1 : ω ≠ 1 := k328r6c_omega_ne_one hω
  have hωne : ω ^ 2 ≠ 1 := by
    intro h
    have h3 : ω ^ 3 = 1 := k328r6c_omega_pow_three hω
    have : ω = 1 := by
      calc ω = ω * ω ^ 2 := by rw [h, mul_one]
        _ = ω ^ 3 := by ring
        _ = 1 := h3
    exact hωne1 this
  have hωω2 : ω ≠ ω ^ 2 := by
    intro h
    apply hωne
    calc ω ^ 2 = ω * ω := by ring
      _ = ω * ω ^ 2 := by rw [← h]
      _ = ω ^ 3 := by ring
      _ = 1 := k328r6c_omega_pow_three hω
  have hcop12 : IsCoprime (X - C 1) (X - C ω : F[X]) :=
    isCoprime_X_sub_C_of_isUnit_sub
      (by rw [isUnit_iff_ne_zero]; exact sub_ne_zero.mpr (Ne.symm hωne1))
  have hcop13 : IsCoprime (X - C 1) (X - C (ω ^ 2) : F[X]) :=
    isCoprime_X_sub_C_of_isUnit_sub
      (by rw [isUnit_iff_ne_zero]; exact sub_ne_zero.mpr (Ne.symm hωne))
  have hcop23 : IsCoprime (X - C ω) (X - C (ω ^ 2) : F[X]) :=
    isCoprime_X_sub_C_of_isUnit_sub (by rw [isUnit_iff_ne_zero]; exact sub_ne_zero.mpr hωω2)
  have hcop123 : IsCoprime ((X - C 1) * (X - C ω)) (X - C (ω ^ 2) : F[X]) :=
    hcop13.mul_left hcop23
  have hzero : aeval Z ((X - C 1) * (X - C ω) * (X - C (ω ^ 2))) = 0 := by
    rw [k328r6c_poly_prod hω]
    simp [aeval_X, hZ]
  have hk12 := sup_ker_aeval_eq_ker_aeval_mul_of_coprime Z hcop12
  have hk123 := sup_ker_aeval_eq_ker_aeval_mul_of_coprime Z hcop123
  have htop : (⊤ : Submodule F (Fin 4 → F)) =
      LinearMap.ker (aeval Z (X - C (1 : F) : F[X])) ⊔
        LinearMap.ker (aeval Z (X - C ω : F[X])) ⊔
        LinearMap.ker (aeval Z (X - C (ω ^ 2) : F[X])) := by
    rw [hk12, hk123]
    rw [show aeval Z ((X - C 1) * (X - C ω) * (X - C (ω ^ 2))) = 0 from hzero,
      LinearMap.ker_zero]
  have hd12 : Disjoint (LinearMap.ker (aeval Z (X - C (1 : F) : F[X])))
      (LinearMap.ker (aeval Z (X - C ω : F[X]))) :=
    disjoint_ker_aeval_of_isCoprime Z hcop12
  have hd23 : Disjoint (LinearMap.ker (aeval Z (X - C ω : F[X])))
      (LinearMap.ker (aeval Z (X - C (ω ^ 2) : F[X]))) :=
    disjoint_ker_aeval_of_isCoprime Z hcop23
  have hA : aeval Z (X - C (1 : F) : F[X]) = Z - 1 := by
    rw [map_sub, aeval_X, aeval_C, map_one]
  have hB : aeval Z (X - C ω : F[X]) = Z - ω • 1 := by
    rw [map_sub, aeval_X, aeval_C, Module.algebraMap_end_eq_smul_id]
    rfl
  have hC : aeval Z (X - C (ω ^ 2) : F[X]) = Z - ω ^ 2 • 1 := by
    rw [map_sub, aeval_X, aeval_C, Module.algebraMap_end_eq_smul_id]
    rfl
  simp only [hA, hB, hC] at htop hd12 hd23 hk12
  have hfr : Module.finrank F (LinearMap.ker (Z - 1) ⊔ LinearMap.ker (Z - ω • 1) ⊔
      LinearMap.ker (Z - ω ^ 2 • 1) : Submodule F (Fin 4 → F)) = 4 := by
    rw [← htop]
    simp
  have hd_AB_C : Disjoint (LinearMap.ker (Z - 1) ⊔ LinearMap.ker (Z - ω • 1))
      (LinearMap.ker (Z - ω ^ 2 • 1)) := by
    have h := disjoint_ker_aeval_of_isCoprime Z hcop123
    rw [hC] at h
    rw [← hk12] at h
    exact h
  have hfr1 : Module.finrank F (LinearMap.ker (Z - 1) ⊔ LinearMap.ker (Z - ω • 1) :
        Submodule F (Fin 4 → F)) =
      Module.finrank F (LinearMap.ker (Z - 1)) +
        Module.finrank F (LinearMap.ker (Z - ω • 1)) := by
    have := Submodule.finrank_sup_add_finrank_inf_eq (LinearMap.ker (Z - 1))
      (LinearMap.ker (Z - ω • 1))
    rw [hd12.eq_bot, finrank_bot, add_zero] at this
    exact this
  have hfr2 : Module.finrank F (LinearMap.ker (Z - 1) ⊔ LinearMap.ker (Z - ω • 1) ⊔
      LinearMap.ker (Z - ω ^ 2 • 1) : Submodule F (Fin 4 → F)) =
      Module.finrank F (LinearMap.ker (Z - 1) ⊔ LinearMap.ker (Z - ω • 1) :
        Submodule F (Fin 4 → F)) +
        Module.finrank F (LinearMap.ker (Z - ω ^ 2 • 1)) := by
    have := Submodule.finrank_sup_add_finrank_inf_eq
      (LinearMap.ker (Z - 1) ⊔ LinearMap.ker (Z - ω • 1)) (LinearMap.ker (Z - ω ^ 2 • 1))
    rw [hd_AB_C.eq_bot, finrank_bot, add_zero] at this
    exact this
  rw [hfr2, hfr1] at hfr
  omega

private theorem k328r6c_three_dvd_finrank_eigenspace {F : Type} [Field F] [Fintype F]
    [DecidableEq F] [CharP F 2] {c : F} (hc3 : c ^ 3 = 1) (hc1 : c ≠ 1)
    {z : GL (Fin 4) F} {X : Subgroup (GL (Fin 4) F)} (hzX : z ∈ X)
    (hXc : X ≤ Subgroup.centralizer {z}) (hXperf : ⁅X, X⁆ = X) :
    3 ∣ Module.finrank F
      (LinearMap.ker (Matrix.toLin' (z : Matrix (Fin 4) (Fin 4) F) - c • 1)) := by
  let Z : (Fin 4 → F) →ₗ[F] (Fin 4 → F) := Matrix.toLin' (z : Matrix (Fin 4) (Fin 4) F)
  let W : Submodule F (Fin 4 → F) := LinearMap.ker (Z - c • 1)
  have hW : ∀ v ∈ W, Z v = c • v := by
    intro v hv
    have h := hv
    rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, sub_eq_zero] at h
    exact h
  let Xm : X → Module.End F (Fin 4 → F) := fun x =>
    Matrix.toLin' (((x : GL (Fin 4) F)) : Matrix (Fin 4) (Fin 4) F)
  have hXm_mul : ∀ x y : X, Xm (x * y) = Xm x * Xm y := by
    intro x y
    show Matrix.toLin' ((((x * y : X) : GL (Fin 4) F)) : Matrix (Fin 4) (Fin 4) F) =
      Matrix.toLin' (((x : X) : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) *
        Matrix.toLin' (((y : X) : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F)
    rw [show ((((x * y : X) : GL (Fin 4) F)) : Matrix (Fin 4) (Fin 4) F) =
      (((x : X) : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) *
        (((y : X) : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) from rfl, Matrix.toLin'_mul,
      Module.End.mul_eq_comp]
  have hcommZ : ∀ x : X, Xm x * Z = Z * Xm x := by
    intro x
    have hx : (x : GL (Fin 4) F) * z = z * (x : GL (Fin 4) F) :=
      (Subgroup.mem_centralizer_iff.mp (hXc x.2) z (Set.mem_singleton z)).symm
    have hm : (((x : X) : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) *
        (z : Matrix (Fin 4) (Fin 4) F) =
        (z : Matrix (Fin 4) (Fin 4) F) *
          (((x : X) : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) := by
      rw [← Units.val_mul, ← Units.val_mul, hx]
    show Matrix.toLin' (((x : X) : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) *
        Matrix.toLin' (z : Matrix (Fin 4) (Fin 4) F) =
      Matrix.toLin' (z : Matrix (Fin 4) (Fin 4) F) *
        Matrix.toLin' (((x : X) : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F)
    rw [Module.End.mul_eq_comp, Module.End.mul_eq_comp, ← Matrix.toLin'_mul, ← Matrix.toLin'_mul,
      hm]
  have hpres : ∀ x : X, ∀ v ∈ W, Xm x v ∈ W := by
    intro x v hv
    rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply]
    have h1 : Z (Xm x v) = Xm x (Z v) := by
      have h := congrArg (fun f : Module.End F (Fin 4 → F) => f v) (hcommZ x)
      simpa [Module.End.mul_apply] using h.symm
    rw [h1, hW v hv, map_smul]
    simp
  let XlFun : X → Module.End F W := fun x => (Xm x).restrict (hpres x)
  have hXl_one : XlFun 1 = 1 := by
    apply LinearMap.ext
    intro v
    apply Subtype.ext
    simp [XlFun, Xm, Matrix.toLin'_one]
  have hXl_mul : ∀ x y : X, XlFun (x * y) = XlFun x * XlFun y := by
    intro x y
    apply LinearMap.ext
    intro v
    apply Subtype.ext
    simp only [XlFun, Module.End.mul_apply, LinearMap.restrict_apply, hXm_mul x y]
  let XlHom : X →* Module.End F W :=
    { toFun := XlFun, map_one' := hXl_one, map_mul' := hXl_mul }
  have hunit : ∀ x : X, IsUnit (XlHom x) := by
    intro x
    refine ⟨⟨XlHom x, XlHom x⁻¹, ?_, ?_⟩, rfl⟩
    · rw [← map_mul, mul_inv_cancel, map_one]
    · rw [← map_mul, inv_mul_cancel, map_one]
  let δ : X →* Fˣ :=
    { toFun := fun x => Units.mk0 (LinearMap.det (XlHom x)) ((hunit x).map LinearMap.det).ne_zero
      map_one' := by
        ext
        rw [Units.val_mk0, map_one XlHom]
        simp
      map_mul' := by
        intro x y
        ext
        simp only [Units.val_mk0, Units.val_mul, map_mul XlHom x y, map_mul LinearMap.det] }
  have hker : commutator X ≤ δ.ker := Abelianization.commutator_subset_ker δ
  have htop : commutator X = ⊤ := by
    have hmap : (commutator X).map X.subtype = X := by
      rw [Subgroup.map_subtype_commutator, hXperf]
    have h := congrArg (Subgroup.comap X.subtype) hmap
    rw [Subgroup.comap_map_eq_self_of_injective X.subtype_injective] at h
    have hcomap : Subgroup.comap X.subtype X = ⊤ := by
      ext y; simp
    rwa [hcomap] at h
  have hδ : δ = 1 := by
    ext x
    have hx : x ∈ δ.ker := hker (by rw [htop]; exact Subgroup.mem_top x)
    simpa [MonoidHom.mem_ker] using hx
  have hzval : δ ⟨z, hzX⟩ = 1 := by rw [hδ]; rfl
  have hzres : XlHom ⟨z, hzX⟩ = c • 1 := by
    apply LinearMap.ext
    intro v
    apply Subtype.ext
    simp only [XlHom, XlFun, Xm, LinearMap.smul_apply, Module.End.one_apply]
    exact hW v v.2
  have hdet : c ^ Module.finrank F W = 1 := by
    have h := congrArg (fun u : Fˣ => (u : F)) hzval
    simp only [Units.val_one] at h
    rw [show (δ ⟨z, hzX⟩ : F) = LinearMap.det (XlHom ⟨z, hzX⟩) from rfl, hzres,
      LinearMap.det_smul, map_one, mul_one] at h
    exact h
  have hord : orderOf c = 3 := orderOf_eq_prime hc3 hc1
  have := orderOf_dvd_of_pow_eq_one hdet
  rwa [hord] at this

private theorem k328r6c_eigenspace_sup_eq_top {F : Type} [Field F] [CharP F 2]
    (ω : F) (hω : ω ^ 2 + ω + 1 = 0) (Z : (Fin 4 → F) →ₗ[F] (Fin 4 → F))
    (hZ : Z ^ 3 = 1) :
    (⊤ : Submodule F (Fin 4 → F)) =
      LinearMap.ker (Z - 1) ⊔ LinearMap.ker (Z - ω • 1) ⊔
        LinearMap.ker (Z - ω ^ 2 • 1) := by
  have hωne1 : ω ≠ 1 := k328r6c_omega_ne_one hω
  have hωne : ω ^ 2 ≠ 1 := by
    intro h
    have h3 : ω ^ 3 = 1 := k328r6c_omega_pow_three hω
    have : ω = 1 := by
      calc ω = ω * ω ^ 2 := by rw [h, mul_one]
        _ = ω ^ 3 := by ring
        _ = 1 := h3
    exact hωne1 this
  have hωω2 : ω ≠ ω ^ 2 := by
    intro h
    apply hωne
    calc ω ^ 2 = ω * ω := by ring
      _ = ω * ω ^ 2 := by rw [← h]
      _ = ω ^ 3 := by ring
      _ = 1 := k328r6c_omega_pow_three hω
  have hcop12 : IsCoprime (X - C 1) (X - C ω : F[X]) :=
    isCoprime_X_sub_C_of_isUnit_sub
      (by rw [isUnit_iff_ne_zero]; exact sub_ne_zero.mpr (Ne.symm hωne1))
  have hcop13 : IsCoprime (X - C 1) (X - C (ω ^ 2) : F[X]) :=
    isCoprime_X_sub_C_of_isUnit_sub
      (by rw [isUnit_iff_ne_zero]; exact sub_ne_zero.mpr (Ne.symm hωne))
  have hcop23 : IsCoprime (X - C ω) (X - C (ω ^ 2) : F[X]) :=
    isCoprime_X_sub_C_of_isUnit_sub (by rw [isUnit_iff_ne_zero]; exact sub_ne_zero.mpr hωω2)
  have hcop123 : IsCoprime ((X - C 1) * (X - C ω)) (X - C (ω ^ 2) : F[X]) :=
    hcop13.mul_left hcop23
  have hzero : aeval Z ((X - C 1) * (X - C ω) * (X - C (ω ^ 2))) = 0 := by
    rw [k328r6c_poly_prod hω]
    simp [aeval_X, hZ]
  have hk12 := sup_ker_aeval_eq_ker_aeval_mul_of_coprime Z hcop12
  have hk123 := sup_ker_aeval_eq_ker_aeval_mul_of_coprime Z hcop123
  have htop : (⊤ : Submodule F (Fin 4 → F)) =
      LinearMap.ker (aeval Z (X - C (1 : F) : F[X])) ⊔
        LinearMap.ker (aeval Z (X - C ω : F[X])) ⊔
        LinearMap.ker (aeval Z (X - C (ω ^ 2) : F[X])) := by
    rw [hk12, hk123]
    rw [show aeval Z ((X - C 1) * (X - C ω) * (X - C (ω ^ 2))) = 0 from hzero,
      LinearMap.ker_zero]
  have hA : aeval Z (X - C (1 : F) : F[X]) = Z - 1 := by
    rw [map_sub, aeval_X, aeval_C, map_one]
  have hB : aeval Z (X - C ω : F[X]) = Z - ω • 1 := by
    rw [map_sub, aeval_X, aeval_C, Module.algebraMap_end_eq_smul_id]
    rfl
  have hC : aeval Z (X - C (ω ^ 2) : F[X]) = Z - ω ^ 2 • 1 := by
    rw [map_sub, aeval_X, aeval_C, Module.algebraMap_end_eq_smul_id]
    rfl
  simp only [hA, hB, hC] at htop
  exact htop

private theorem k328r6c_herm_eq_zero_of_eigen {F : Type} [Field F] {σ : F ≃+* F}
    {c d : F} (hcd : σ c * d ≠ 1)
    {z : GL (Fin 4) F} (hz : z ∈ SUid σ 4) {x y : Fin 4 → F}
    (hx : (z : Matrix (Fin 4) (Fin 4) F) *ᵥ x = c • x)
    (hy : (z : Matrix (Fin 4) (Fin 4) F) *ᵥ y = d • y) :
    herm σ x y = 0 := by
  have h : herm σ ((z : Matrix (Fin 4) (Fin 4) F) *ᵥ x)
      ((z : Matrix (Fin 4) (Fin 4) F) *ᵥ y) = herm σ x y := by
    have := CFSG.ClassicalGroups.Unitary.herm_smul_smul σ (⟨z, hz⟩ : SUid σ 4) x y
    simpa [CFSG.ClassicalGroups.Unitary.smul_def σ] using this
  rw [hx, hy, herm_smul_left, herm_smul_right] at h
  have h0 : (σ c * d - 1) * herm σ x y = 0 := by
    linear_combination h
  rcases mul_eq_zero.mp h0 with h1 | h1
  · exact absurd (sub_eq_zero.mp h1) hcd
  · exact h1

private theorem k328r6c_ker_sub_one_ne_top {F : Type} [Field F] {z : GL (Fin 4) F}
    (hz : z ≠ 1) :
    LinearMap.ker (Matrix.toLin' (z : Matrix (Fin 4) (Fin 4) F) - 1) ≠ ⊤ := by
  intro h
  apply hz
  have h0 : Matrix.toLin' (z : Matrix (Fin 4) (Fin 4) F) - 1 = 0 := by
    rwa [LinearMap.ker_eq_top] at h
  have h1 : Matrix.toLin' (z : Matrix (Fin 4) (Fin 4) F) = 1 := sub_eq_zero.mp h0
  have hmat : (z : Matrix (Fin 4) (Fin 4) F) = 1 := by
    apply Matrix.toLinAlgEquiv'.injective
    show Matrix.toLinAlgEquiv' (z : Matrix (Fin 4) (Fin 4) F) = Matrix.toLinAlgEquiv' 1
    rw [Matrix.toLinAlgEquiv'_one]
    rw [show Matrix.toLinAlgEquiv' (z : Matrix (Fin 4) (Fin 4) F) =
      Matrix.toLin' (z : Matrix (Fin 4) (Fin 4) F) from rfl, h1]
    rfl
  exact Units.ext hmat

private theorem k328r6c_norm_one_fixed {F : Type} [Field F] [Fintype F] [DecidableEq F]
    {σ : F ≃+* F} (hσ : IsUnitaryInvolution σ) {z : GL (Fin 4) F} (hzSU : z ∈ SUid σ 4)
    {c : F} (hc1 : c ≠ 1)
    (h1 : Module.finrank F
      (LinearMap.ker (Matrix.toLin' (z : Matrix (Fin 4) (Fin 4) F) - 1)) = 1)
    (hsup : (⊤ : Submodule F (Fin 4 → F)) =
      LinearMap.ker (Matrix.toLin' (z : Matrix (Fin 4) (Fin 4) F) - 1) ⊔
        LinearMap.ker (Matrix.toLin' (z : Matrix (Fin 4) (Fin 4) F) - c • 1)) :
    ∃ v : Fin 4 → F, herm σ v v = 1 ∧ (z : Matrix (Fin 4) (Fin 4) F) *ᵥ v = v := by
  set Z : (Fin 4 → F) →ₗ[F] (Fin 4 → F) := Matrix.toLin' (z : Matrix (Fin 4) (Fin 4) F) with hZdef
  set V1 : Submodule F (Fin 4 → F) := LinearMap.ker (Z - 1) with hV1def
  set Vc : Submodule F (Fin 4 → F) := LinearMap.ker (Z - c • 1) with hVcdef
  have h1' : Module.finrank F V1 = 1 := by rw [hV1def, hZdef]; exact h1
  have hV1ne : V1 ≠ ⊥ := by
    intro h
    rw [h, finrank_bot] at h1'
    omega
  obtain ⟨v, hv1, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hV1ne
  have hV1span : V1 = F ∙ v := by
    symm
    refine Submodule.eq_of_le_of_finrank_eq ?_ ?_
    · rw [Submodule.span_le]; exact Set.singleton_subset_iff.mpr hv1
    · rw [finrank_span_singleton hv0, h1']
  have hvv : herm σ v v ≠ 0 := by
    intro h0
    apply hv0
    apply eq_zero_of_herm σ
    intro w
    have hw : w ∈ V1 ⊔ Vc := by
      rw [← hsup]
      exact Submodule.mem_top
    rcases Submodule.mem_sup.mp hw with ⟨a, ha, b, hb, rfl⟩
    have ha' : (z : Matrix (Fin 4) (Fin 4) F) *ᵥ a = (1 : F) • a := by
      have hmem : a ∈ LinearMap.ker (Z - 1) := ha
      rw [LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero] at hmem
      simpa [hZdef, Matrix.toLin'_apply] using hmem
    have hb' : (z : Matrix (Fin 4) (Fin 4) F) *ᵥ b = c • b := by
      have hmem : b ∈ LinearMap.ker (Z - c • 1) := hb
      rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply,
        sub_eq_zero] at hmem
      simpa [hZdef, Matrix.toLin'_apply] using hmem
    have hva : herm σ v a = 0 := by
      have hspan : a ∈ F ∙ v := by rw [← hV1span]; exact ha
      rcases Submodule.mem_span_singleton.mp hspan with ⟨d, rfl⟩
      rw [herm_smul_right, h0, mul_zero]
    have hv' : (z : Matrix (Fin 4) (Fin 4) F) *ᵥ v = (1 : F) • v := by
      have hmem : v ∈ LinearMap.ker (Z - 1) := hv1
      rw [LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero] at hmem
      simpa [hZdef, Matrix.toLin'_apply] using hmem
    have hvb : herm σ v b = 0 :=
      k328r6c_herm_eq_zero_of_eigen (by rw [map_one, one_mul]; exact hc1) hzSU hv' hb'
    rw [herm_add_right, hva, hvb, add_zero]
  obtain ⟨a, ha⟩ := exists_smul_norm_one hσ hvv
  refine ⟨a • v, ha, ?_⟩
  have hZv : (z : Matrix (Fin 4) (Fin 4) F) *ᵥ v = v := by
    have hmem : v ∈ LinearMap.ker (Z - 1) := hv1
    rw [LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero] at hmem
    simpa [hZdef, Matrix.toLin'_apply] using hmem
  rw [Matrix.mulVec_smul, hZv]

private theorem k328r6c_conj_diag {F : Type} [Field F] [Fintype F] [DecidableEq F] [CharP F 2]
    {σ : F ≃+* F} (hσ : IsUnitaryInvolution σ) {c : F} (hc1 : c ≠ 1)
    {z : GL (Fin 4) F} (hzSU : z ∈ SUid σ 4) {v : Fin 4 → F}
    (hvnorm : herm σ v v = 1) (hvfix : (z : Matrix (Fin 4) (Fin 4) F) *ᵥ v = v)
    (hc : Module.finrank F
      (LinearMap.ker (Matrix.toLin' (z : Matrix (Fin 4) (Fin 4) F) - c • 1)) = 3) :
    ∃ g ∈ SUid σ 4, ((g * z * g⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) =
      Matrix.diagonal ![c, c, c, 1] := by
  set Z : (Fin 4 → F) →ₗ[F] (Fin 4 → F) := Matrix.toLin' (z : Matrix (Fin 4) (Fin 4) F) with hZdef
  set Vc : Submodule F (Fin 4 → F) := LinearMap.ker (Z - c • 1) with hVcdef
  let e3 : Fin 4 → F := Pi.single 3 1
  have he3norm : herm σ e3 e3 = 1 := by
    rw [show e3 = Pi.single 3 1 from rfl, herm_single_left, Pi.single_eq_same, map_one, one_mul]
  obtain ⟨g, _hgT, hgv⟩ :=
    exists_mem_T_smul_eq_of_norm_one hσ (n := 4) (Or.inl (by norm_num)) hvnorm he3norm
  refine ⟨g, g.2, ?_⟩
  let G : (Fin 4 → F) →ₗ[F] (Fin 4 → F) :=
    Matrix.toLin' ((g : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F)
  let Ginv : (Fin 4 → F) →ₗ[F] (Fin 4 → F) :=
    Matrix.toLin' (((g : GL (Fin 4) F)⁻¹) : Matrix (Fin 4) (Fin 4) F)
  have hGv : G v = e3 := by
    have h := hgv
    rw [CFSG.ClassicalGroups.Unitary.smul_def σ] at h
    simpa [G, Matrix.toLin'_apply] using h
  have hmat_mul : ((g : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) *
      (((g : GL (Fin 4) F)⁻¹) : Matrix (Fin 4) (Fin 4) F) = 1 := by
    have h : (g : GL (Fin 4) F) * ((g : GL (Fin 4) F))⁻¹ = 1 :=
      mul_inv_cancel (g : GL (Fin 4) F)
    have h' := congrArg (fun u : GL (Fin 4) F => (u : Matrix (Fin 4) (Fin 4) F)) h
    simp
  have hmat_invmul : (((g : GL (Fin 4) F)⁻¹) : Matrix (Fin 4) (Fin 4) F) *
      ((g : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) = 1 := by
    have h : ((g : GL (Fin 4) F))⁻¹ * (g : GL (Fin 4) F) = 1 :=
      inv_mul_cancel (g : GL (Fin 4) F)
    have h' := congrArg (fun u : GL (Fin 4) F => (u : Matrix (Fin 4) (Fin 4) F)) h
    simp
  have hGmul : G * Ginv = 1 := by
    change Matrix.toLin' ((g : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) *
      Matrix.toLin' (((g : GL (Fin 4) F)⁻¹) : Matrix (Fin 4) (Fin 4) F) = 1
    rw [Module.End.mul_eq_comp, ← Matrix.toLin'_mul, hmat_mul, Matrix.toLin'_one]
    rfl
  have hGinvmul : Ginv * G = 1 := by
    change Matrix.toLin' (((g : GL (Fin 4) F)⁻¹) : Matrix (Fin 4) (Fin 4) F) *
      Matrix.toLin' ((g : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) = 1
    rw [Module.End.mul_eq_comp, ← Matrix.toLin'_mul, hmat_invmul, Matrix.toLin'_one]
    rfl
  let φ : Module.Dual F (Fin 4 → F) := hermL σ e3
  have hφ : φ ≠ 0 := by
    intro h
    have h1 := congrArg (fun f : Module.Dual F (Fin 4 → F) => f e3) h
    rw [show φ e3 = herm σ e3 e3 from rfl, show e3 = Pi.single 3 1 from rfl, herm_single_left,
      Pi.single_eq_same, map_one, one_mul] at h1
    exact one_ne_zero h1
  have hkerφ : Module.finrank F (LinearMap.ker φ) = 3 := by
    have h1 := Module.Dual.finrank_ker_add_one_of_ne_zero hφ
    rw [Module.finrank_fin_fun] at h1
    omega
  have hGVc_le : Vc.map G ≤ LinearMap.ker φ := by
    rintro w ⟨u, hu, rfl⟩
    change herm σ e3 (G u) = 0
    rw [← hGv]
    have hiso : herm σ (G v) (G u) = herm σ v u := by
      have h := CFSG.ClassicalGroups.Unitary.herm_smul_smul σ g v u
      simp only [CFSG.ClassicalGroups.Unitary.smul_def σ] at h
      simpa only [G, Matrix.toLin'_apply] using h
    have hu' : (z : Matrix (Fin 4) (Fin 4) F) *ᵥ u = c • u := by
      have hmem : u ∈ LinearMap.ker (Z - c • 1) := hu
      rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply,
        sub_eq_zero] at hmem
      simpa [hZdef, Matrix.toLin'_apply] using hmem
    have hv' : (z : Matrix (Fin 4) (Fin 4) F) *ᵥ v = (1 : F) • v := by rw [hvfix, one_smul]
    rw [hiso, k328r6c_herm_eq_zero_of_eigen (by rw [map_one, one_mul]; exact hc1) hzSU hv' hu']
  let Gle : (Fin 4 → F) ≃ₗ[F] (Fin 4 → F) :=
    (Matrix.GeneralLinearGroup.toLin (g : GL (Fin 4) F)).toLinearEquiv
  have hGle : (Gle : (Fin 4 → F) →ₗ[F] (Fin 4 → F)) = G := by
    ext x
    simp [Gle, G, Matrix.toLin'_apply]
  have hGVc_fin : Module.finrank F (Vc.map G) = 3 := by
    rw [← hGle, LinearEquiv.finrank_map_eq]
    exact hc
  have hGVc_eq : Vc.map G = LinearMap.ker φ :=
    Submodule.eq_of_le_of_finrank_eq hGVc_le (by rw [hGVc_fin, hkerφ])
  have hei_ker (i : Fin 4) (hi : i ≠ 3) : Pi.single i 1 ∈ LinearMap.ker φ := by
    change herm σ e3 (Pi.single i 1) = 0
    rw [show e3 = Pi.single 3 1 from rfl, herm_single_left, map_one, one_mul]
    simp [hi]
  have hZv : Z v = v := by
    simpa [Z, Matrix.toLin'_apply] using hvfix
  have hZmul : Matrix.toLin' (((g * z * g⁻¹ : GL (Fin 4) F)) : Matrix (Fin 4) (Fin 4) F) =
      G * Z * Ginv := by
    simp only [G, Ginv, Z, ← Matrix.toLin'_mul, Module.End.mul_eq_comp]
    rw [show (((g * z * g⁻¹ : GL (Fin 4) F)) : Matrix (Fin 4) (Fin 4) F) =
      ((g : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) * (z : Matrix (Fin 4) (Fin 4) F) *
        (((g : GL (Fin 4) F)⁻¹) : Matrix (Fin 4) (Fin 4) F) from by
      simp]
  have hZ'e3 :
      Matrix.toLin' (((g * z * g⁻¹ : GL (Fin 4) F)) : Matrix (Fin 4) (Fin 4) F) e3 = e3 := by
    rw [hZmul, Module.End.mul_apply, Module.End.mul_apply]
    have hGinv_e3 : Ginv e3 = v := by
      rw [← hGv, ← Module.End.mul_apply, hGinvmul, Module.End.one_apply]
    rw [hGinv_e3, hZv, hGv]
  have hZ'ei (i : Fin 4) (hi : i ≠ 3) :
      Matrix.toLin' (((g * z * g⁻¹ : GL (Fin 4) F)) : Matrix (Fin 4) (Fin 4) F)
        (Pi.single i 1) = c • Pi.single i 1 := by
    rw [hZmul, Module.End.mul_apply, Module.End.mul_apply]
    have hei : Pi.single i 1 ∈ Vc.map G := by rw [hGVc_eq]; exact hei_ker i hi
    rcases hei with ⟨w, hw, hwG⟩
    rw [← hwG]
    rw [show Ginv (G w) = (Ginv * G) w from rfl, hGinvmul, Module.End.one_apply]
    have hZw : Z w = c • w := by
      have hmem : w ∈ LinearMap.ker (Z - c • 1) := hw
      rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply,
        sub_eq_zero] at hmem
      exact hmem
    rw [hZw, map_smul, hwG]
  have hZ₀ (i : Fin 4) : Matrix.toLin' (Matrix.diagonal ![c, c, c, 1]) (Pi.single i 1) =
      ![c, c, c, 1] i • Pi.single i 1 := by
    rw [Matrix.toLin'_apply, Matrix.mulVec_single_one]
    funext j
    by_cases hji : j = i
    · subst hji; simp [Matrix.col_apply]
    · simp [Matrix.col_apply, hji]
  have hZ'_eq : Matrix.toLin' (((g * z * g⁻¹ : GL (Fin 4) F)) : Matrix (Fin 4) (Fin 4) F) =
      Matrix.toLin' (Matrix.diagonal ![c, c, c, 1]) := by
    apply (Pi.basisFun F (Fin 4)).ext
    intro i
    rw [Pi.basisFun_apply]
    by_cases hi : i = 3
    · subst hi
      rw [hZ'e3, hZ₀ 3]; simp [e3]
    · rw [hZ'ei i hi, hZ₀ i]
      fin_cases i <;> simp_all
  exact Matrix.toLinAlgEquiv'.injective hZ'_eq

theorem row6_class (F : Type) [Field F] [Fintype F] [DecidableEq F]
    (hF : Fintype.card F = 64) (ω : F)
    (hω : ω ^ 2 + ω + 1 = 0) (z₀ t₀ : GL (Fin 4) F)
    (hz : (z₀ : Matrix (Fin 4) (Fin 4) F) = Matrix.diagonal ![ω, ω, ω, 1])
    (ht : (t₀ : Matrix (Fin 4) (Fin 4) F) = Matrix.diagonal ![ω, ω ^ 2, 1, 1]) :
    ClassLeaf (StatedSU 4 8 F) z₀ := by
  have _ := ht
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h2 : CharP F 2 := charP_of_card_eq_prime_pow (p := 2) (f := 6) (by rw [hF]; norm_num)
  have : CharP F 2 := h2
  have hcard : Nat.card F = (2 ^ 3) ^ 2 := by rw [Nat.card_eq_fintype_card, hF]; norm_num
  let σ : F ≃+* F := CFSG.LieType.BorelTits.unitaryInvolution F 2 3
  have hσ : IsUnitaryInvolution σ :=
    isUnitaryInvolution_unitaryInvolution (p := 2) (f := 3) hcard
  have hSU : StatedSU 4 8 F = SUid σ 4 :=
    (SUid_eq_statedSU (p := 2) (f := 3) hcard 4).symm
  intro z hzH hzo X hXH hzX hXc hXperf
  have hzSU : z ∈ SUid σ 4 := hSU ▸ hzH
  have hω3 : ω ^ 3 = 1 := k328r6c_omega_pow_three hω
  have hωne : ω ≠ 1 := k328r6c_omega_ne_one hω
  have hω2_3 : (ω ^ 2) ^ 3 = 1 := by
    rw [← pow_mul, show 2 * 3 = 3 * 2 by norm_num, pow_mul, hω3, one_pow]
  have hω2ne : ω ^ 2 ≠ 1 := by
    intro h
    apply hωne
    calc ω = ω * ω ^ 2 := by rw [h, mul_one]
      _ = ω ^ 3 := by ring
      _ = 1 := hω3
  have hωinv : ω⁻¹ = ω ^ 2 := by
    have hm : ω * ω ^ 2 = 1 := by rw [← pow_succ', hω3]
    exact (eq_inv_of_mul_eq_one_right hm).symm
  have hωinvne : ω⁻¹ ≠ 1 := by rw [hωinv]; exact hω2ne
  let Z : (Fin 4 → F) →ₗ[F] (Fin 4 → F) := Matrix.toLin' (z : Matrix (Fin 4) (Fin 4) F)
  have hzo3 : z ^ 3 = 1 := by rw [← hzo]; exact pow_orderOf_eq_one z
  have hZ3 : Z ^ 3 = 1 := by
    have hm : ((z : Matrix (Fin 4) (Fin 4) F)) ^ 3 = 1 := by
      rw [← Units.val_pow_eq_pow_val, hzo3, Units.val_one]
    rw [show Z ^ 3 = Matrix.toLin' (((z : Matrix (Fin 4) (Fin 4) F)) ^ 3) from by
      rw [Matrix.toLin'_pow]]
    rw [hm, Matrix.toLin'_one]
    rfl
  have hz_ne_one : z ≠ 1 := by
    intro h
    rw [h] at hzo
    norm_num at hzo
  let V1 : Submodule F (Fin 4 → F) := LinearMap.ker (Z - 1)
  let Vω : Submodule F (Fin 4 → F) := LinearMap.ker (Z - ω • 1)
  let Vω2 : Submodule F (Fin 4 → F) := LinearMap.ker (Z - ω ^ 2 • 1)
  have hfin : Module.finrank F (Fin 4 → F) = 4 := Module.finrank_fin_fun F
  have hsum : Module.finrank F V1 + Module.finrank F Vω + Module.finrank F Vω2 = 4 :=
    k328r6c_eigenspace_finrank_sum ω hω Z hZ3
  have h3ω : 3 ∣ Module.finrank F Vω :=
    k328r6c_three_dvd_finrank_eigenspace hω3 hωne hzX hXc hXperf
  have h3ω2 : 3 ∣ Module.finrank F Vω2 :=
    k328r6c_three_dvd_finrank_eigenspace hω2_3 hω2ne hzX hXc hXperf
  have hV1_ne_top : V1 ≠ ⊤ := by
    have h := k328r6c_ker_sub_one_ne_top hz_ne_one
    simpa [V1, Z] using h
  have hnω_le : Module.finrank F Vω ≤ 4 := by
    have h := Submodule.finrank_le Vω
    rwa [hfin] at h
  have hnω2_le : Module.finrank F Vω2 ≤ 4 := by
    have h := Submodule.finrank_le Vω2
    rwa [hfin] at h
  have hn1_ne : Module.finrank F V1 ≠ 4 := by
    intro h
    apply hV1_ne_top
    exact Submodule.eq_top_of_finrank_eq (by rw [h, hfin])
  obtain ⟨k, hk⟩ := h3ω
  obtain ⟨l, hl⟩ := h3ω2
  have hcase : (Module.finrank F Vω = 3 ∧ Module.finrank F Vω2 = 0) ∨
      (Module.finrank F Vω = 0 ∧ Module.finrank F Vω2 = 3) := by omega
  have hn1 : Module.finrank F V1 = 1 := by omega
  have htop := k328r6c_eigenspace_sup_eq_top ω hω Z hZ3
  rcases hcase with ⟨hωd, hω2d⟩ | ⟨hωd, hω2d⟩
  · have hVω2 : Vω2 = ⊥ := Submodule.finrank_eq_zero.mp hω2d
    have hsup : (⊤ : Submodule F (Fin 4 → F)) = V1 ⊔ Vω := by
      have h := htop
      change (⊤ : Submodule F (Fin 4 → F)) = V1 ⊔ Vω ⊔ Vω2 at h
      rw [hVω2, sup_bot_eq] at h
      exact h
    obtain ⟨v, hvnorm, hvfix⟩ :=
      k328r6c_norm_one_fixed hσ hzSU hωne (by simpa [V1, Z] using hn1) hsup
    obtain ⟨g, hgSU, hgconj⟩ :=
      k328r6c_conj_diag hσ hωne hzSU hvnorm hvfix (by simpa [Vω, Z] using hωd)
    refine ⟨g, hSU ▸ hgSU, Or.inl ?_⟩
    apply Units.ext
    rw [hgconj, hz]
  · have hVω : Vω = ⊥ := Submodule.finrank_eq_zero.mp hωd
    have hsup : (⊤ : Submodule F (Fin 4 → F)) = V1 ⊔ Vω2 := by
      have h := htop
      change (⊤ : Submodule F (Fin 4 → F)) = V1 ⊔ Vω ⊔ Vω2 at h
      rw [hVω, sup_bot_eq] at h
      exact h
    obtain ⟨v, hvnorm, hvfix⟩ :=
      k328r6c_norm_one_fixed hσ hzSU hω2ne
        (by simpa [V1, Z] using hn1) hsup
    obtain ⟨g, hgSU, hgconj⟩ :=
      k328r6c_conj_diag hσ hω2ne hzSU hvnorm hvfix
        (by simpa [Vω2, Z] using hω2d)
    refine ⟨g, hSU ▸ hgSU, Or.inr ?_⟩
    have hz0inv : ((z₀⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) =
        Matrix.diagonal ![ω ^ 2, ω ^ 2, ω ^ 2, 1] := by
      rw [Matrix.GeneralLinearGroup.coe_inv]
      apply Matrix.inv_eq_right_inv
      rw [hz, Matrix.diagonal_mul_diagonal]
      have hm : ω * ω ^ 2 = 1 := by rw [← pow_succ', hω3]
      ext i j
      fin_cases i <;> fin_cases j <;> simp [hm]
    apply Units.ext
    rw [hgconj, hz0inv]

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.K328

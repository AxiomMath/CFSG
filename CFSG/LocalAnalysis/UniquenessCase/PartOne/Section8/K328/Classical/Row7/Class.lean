module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.K328.Rows
import CFSG.LinearAlgebra.CubeRootBlock
import CFSG.ClassicalGroups.Symplectic.StandardForm
import CFSG.ClassicalInvolution.Models.SymplecticPairs.Basic
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.K328.Classical.Frame

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.K328

open CFSG.Open
open CFSG.ClassicalGroups.Symplectic
open CFSG.ClassicalInvolution.Models.SymplecticPairs (ofSymplecticMat)
open Matrix
open LinearMap (BilinForm)

private theorem k328r7c_perfect_hom_eq_one {G : Type*} [Group G] [Group.IsPerfect G]
    {A : Type*} [CommGroup A] (f : G →* A) : f = 1 := by
  have : Group.IsPerfect f.range := Group.IsPerfect.range f
  have : IsMulCommutative f.range := isMulCommutative_iff.mpr fun a b =>
    Subtype.ext (by simp only [Subgroup.coe_mul]; exact mul_comm _ _)
  have : Subsingleton f.range := Group.IsPerfect.subsingleton_of_isMulCommutative
  ext x
  exact congrArg Subtype.val
    (Subsingleton.elim (⟨f x, MonoidHom.mem_range.mpr ⟨x, rfl⟩⟩ : f.range)
      ⟨1, MonoidHom.mem_range.mpr ⟨1, f.map_one⟩⟩)

private theorem k328r7c_no_cube_root (F : Type) [Field F] [Fintype F] [DecidableEq F] (hF : Fintype.card F = 8) (t : F)
    (h : t ^ 2 + t + 1 = 0) : False := by
  have : CharP F 2 := charP_of_card_eq_prime_pow (p := 2) (f := 3) hF
  have h3 : (3 : F) ≠ 0 := by
    intro hz
    have hdvd : 2 ∣ 3 := (CharP.cast_eq_zero_iff F 2 3).mp hz
    norm_num at hdvd
  have ht0 : t ≠ 0 := by
    intro ht
    rw [ht] at h
    norm_num at h
  have hroot : ((Units.mk0 t ht0 : Fˣ) : F) ^ 2 + (Units.mk0 t ht0 : F) + 1 = 0 := by
    simpa using h
  have := (CFSG.LinearAlgebra.exists_unit_sq_add_self_add_one_iff (K := F) h3).mp
    ⟨Units.mk0 t ht0, hroot⟩
  rw [Nat.card_eq_fintype_card, hF] at this
  norm_num at this

private theorem k328r7c_anisotropic (F : Type) [Field F] [Fintype F] [DecidableEq F] (hF : Fintype.card F = 8) (x y : F)
    (h : x ^ 2 + 1 * x * y + y ^ 2 = 0) : x = 0 ∧ y = 0 := by
  by_cases hy : y = 0
  · subst hy
    have hx : x ^ 2 = 0 := by simpa using h
    exact ⟨sq_eq_zero_iff.mp hx, rfl⟩
  · have ht : (x / y) ^ 2 + x / y + 1 = 0 := by
      field_simp
      linear_combination h
    exact absurd (k328r7c_no_cube_root F hF (x / y) ht) (by simp)

private theorem k328r7c_fact (F : Type) [Field F] [Fintype F] [DecidableEq F] (hF : Fintype.card F = 8) :
    Fact (∀ r : F, r ^ 2 ≠ 1 + 1 * r) := by
  have : CharP F 2 := charP_of_card_eq_prime_pow (p := 2) (f := 3) hF
  refine ⟨fun r hr => ?_⟩
  have h2 : (2 : F) = 0 := CharP.cast_eq_zero F 2
  have hq : r ^ 2 + 1 * r * 1 + 1 ^ 2 = 0 := by
    have hr' : r ^ 2 = r + 1 := by
      have := hr
      rw [one_mul, add_comm] at this
      exact this
    rw [hr', mul_one, one_pow]
    linear_combination (r + 1) * h2
  obtain ⟨-, h1⟩ := k328r7c_anisotropic F hF r 1 hq
  exact one_ne_zero h1

private abbrev k328r7c_V (F : Type) : Type := Fin 3 ⊕ Fin 3 → F

private noncomputable def k328r7c_fOf (F : Type) [Field F] [Fintype F] [DecidableEq F] (z : GL (Fin 3 ⊕ Fin 3) F) :
    Module.End F (k328r7c_V F) :=
  (Matrix.GeneralLinearGroup.toLin z : Module.End F (k328r7c_V F))

private theorem k328r7c_fOf_mul (F : Type) [Field F] [Fintype F] [DecidableEq F] (x y : GL (Fin 3 ⊕ Fin 3) F) :
    k328r7c_fOf F (x * y) = k328r7c_fOf F x * k328r7c_fOf F y := by
  simp only [k328r7c_fOf, map_mul]
  rfl

private theorem k328r7c_fOf_comm (F : Type) [Field F] [Fintype F] [DecidableEq F] (x z : GL (Fin 3 ⊕ Fin 3) F) (hxz : x * z = z * x) :
    k328r7c_fOf F x * k328r7c_fOf F z = k328r7c_fOf F z * k328r7c_fOf F x := by
  have h := congrArg (k328r7c_fOf F) hxz
  rw [k328r7c_fOf_mul, k328r7c_fOf_mul] at h
  exact h

private noncomputable def k328r7c_W (F : Type) [Field F] [Fintype F] [DecidableEq F] (z : GL (Fin 3 ⊕ Fin 3) F) :
    Submodule F (k328r7c_V F) :=
  LinearMap.ker ((k328r7c_fOf F z) ^ 2 + k328r7c_fOf F z + 1)

private noncomputable def k328r7c_restrictSub (F : Type) [Field F] [Fintype F] [DecidableEq F] {W : Submodule F (k328r7c_V F)}
    {f : k328r7c_V F →ₗ[F] k328r7c_V F} (hf : ∀ w ∈ W, f w ∈ W) : W →ₗ[F] W where
  toFun w := ⟨f w, hf w w.2⟩
  map_add' w₁ w₂ := by ext; simp
  map_smul' c w := by ext; simp

private theorem k328r7c_gz_comm (F : Type) [Field F] [Fintype F] [DecidableEq F] (x z : GL (Fin 3 ⊕ Fin 3) F) (hxz : x * z = z * x) :
    ((k328r7c_fOf F z) ^ 2 + k328r7c_fOf F z + 1) * k328r7c_fOf F x =
      k328r7c_fOf F x * ((k328r7c_fOf F z) ^ 2 + k328r7c_fOf F z + 1) := by
  have hxz' := k328r7c_fOf_comm F x z hxz
  have hz2 : (k328r7c_fOf F z) ^ 2 * k328r7c_fOf F x =
      k328r7c_fOf F x * (k328r7c_fOf F z) ^ 2 := by
    rw [pow_two]
    calc (k328r7c_fOf F z * k328r7c_fOf F z) * k328r7c_fOf F x
        = k328r7c_fOf F z * (k328r7c_fOf F z * k328r7c_fOf F x) := by rw [mul_assoc]
      _ = k328r7c_fOf F z * (k328r7c_fOf F x * k328r7c_fOf F z) := by rw [hxz']
      _ = (k328r7c_fOf F z * k328r7c_fOf F x) * k328r7c_fOf F z := by rw [mul_assoc]
      _ = (k328r7c_fOf F x * k328r7c_fOf F z) * k328r7c_fOf F z := by rw [hxz']
      _ = k328r7c_fOf F x * (k328r7c_fOf F z * k328r7c_fOf F z) := by rw [mul_assoc]
  calc ((k328r7c_fOf F z) ^ 2 + k328r7c_fOf F z + 1) * k328r7c_fOf F x
      = (k328r7c_fOf F z) ^ 2 * k328r7c_fOf F x + k328r7c_fOf F z * k328r7c_fOf F x +
          1 * k328r7c_fOf F x := by rw [add_mul, add_mul, one_mul]
    _ = k328r7c_fOf F x * (k328r7c_fOf F z) ^ 2 + k328r7c_fOf F x * k328r7c_fOf F z +
          k328r7c_fOf F x := by rw [hz2, hxz', one_mul]
    _ = k328r7c_fOf F x * ((k328r7c_fOf F z) ^ 2 + k328r7c_fOf F z + 1) := by
          rw [mul_add, mul_add, mul_one]

private noncomputable def k328r7c_fW (F : Type) [Field F] [Fintype F] [DecidableEq F] (z : GL (Fin 3 ⊕ Fin 3) F) :
    k328r7c_W F z →ₗ[F] k328r7c_W F z :=
  k328r7c_restrictSub (F := F) (W := k328r7c_W F z) (f := k328r7c_fOf F z) (by
    intro w hw
    rw [k328r7c_W, LinearMap.mem_ker] at hw ⊢
    rw [← Module.End.mul_apply, k328r7c_gz_comm F z z rfl, Module.End.mul_apply, hw, map_zero])

private theorem k328r7c_fW_rel (F : Type) [Field F] [Fintype F] [DecidableEq F] [CharP F 2] (z : GL (Fin 3 ⊕ Fin 3) F) :
    k328r7c_fW F z * k328r7c_fW F z = 1 + k328r7c_fW F z := by
  apply LinearMap.ext
  intro w
  apply Subtype.ext
  change (k328r7c_fOf F z) ((k328r7c_fOf F z) (w : k328r7c_V F)) =
    (w : k328r7c_V F) + (k328r7c_fOf F z) (w : k328r7c_V F)
  have hw := w.2
  change (w : k328r7c_V F) ∈ LinearMap.ker
    ((k328r7c_fOf F z) ^ 2 + k328r7c_fOf F z + 1) at hw
  rw [LinearMap.mem_ker] at hw
  have h' : (k328r7c_fOf F z) ((k328r7c_fOf F z) (w : k328r7c_V F)) +
      ((k328r7c_fOf F z) (w : k328r7c_V F) + (w : k328r7c_V F)) = 0 := by
    simpa only [pow_two, Module.End.mul_apply, LinearMap.add_apply, Module.End.one_apply,
      add_assoc] using hw
  have : CharP (k328r7c_V F) 2 := inferInstance
  exact (CharTwo.add_eq_zero.mp h').trans (add_comm ((k328r7c_fOf F z) (w : k328r7c_V F))
    (w : k328r7c_V F))

private noncomputable def k328r7c_phi (F : Type) [Field F] [Fintype F] [DecidableEq F] [CharP F 2] (z : GL (Fin 3 ⊕ Fin 3) F) :
    QuadraticAlgebra F 1 1 →ₐ[F] Module.End F (k328r7c_W F z) :=
  QuadraticAlgebra.lift (a := 1) (b := 1) ⟨k328r7c_fW F z, by
    rw [one_smul, one_smul]
    exact k328r7c_fW_rel F z⟩

private theorem k328r7c_phi_omega (F : Type) [Field F] [Fintype F] [DecidableEq F] [CharP F 2] (z : GL (Fin 3 ⊕ Fin 3) F) :
    k328r7c_phi F z QuadraticAlgebra.omega = k328r7c_fW F z := by
  simp [k328r7c_phi, QuadraticAlgebra.lift]

private theorem k328r7c_phi_algebraMap (F : Type) [Field F] [Fintype F] [DecidableEq F] [CharP F 2] (z : GL (Fin 3 ⊕ Fin 3) F) (c : F) :
    k328r7c_phi F z (algebraMap F (QuadraticAlgebra F 1 1) c) =
      c • (1 : k328r7c_W F z →ₗ[F] k328r7c_W F z) := by
  rw [AlgHom.commutes]
  exact Algebra.algebraMap_eq_smul_one c

private noncomputable instance k328r7c_instModuleL (F : Type) [Field F] [Fintype F] [DecidableEq F] [CharP F 2]
    (z : GL (Fin 3 ⊕ Fin 3) F) :
    Module (QuadraticAlgebra F 1 1) (k328r7c_W F z) :=
  Module.compHom (k328r7c_W F z) (k328r7c_phi F z).toRingHom

private theorem k328r7c_hphi (F : Type) [Field F] [Fintype F] [DecidableEq F] [CharP F 2] (z : GL (Fin 3 ⊕ Fin 3) F)
    (l : QuadraticAlgebra F 1 1) :
    k328r7c_phi F z l = l.re • (1 : k328r7c_W F z →ₗ[F] k328r7c_W F z) +
      l.im • k328r7c_fW F z := by
  have hrepr : l = algebraMap F (QuadraticAlgebra F 1 1) l.re +
      l.im • QuadraticAlgebra.omega := by
    ext <;> simp [QuadraticAlgebra.omega]
  conv_lhs => rw [hrepr]
  rw [map_add, map_smul, k328r7c_phi_algebraMap, k328r7c_phi_omega]

private theorem k328r7c_omega_smul (F : Type) [Field F] [Fintype F] [DecidableEq F] [CharP F 2] (z : GL (Fin 3 ⊕ Fin 3) F)
    (w : k328r7c_W F z) :
    (QuadraticAlgebra.omega : QuadraticAlgebra F 1 1) • w = k328r7c_fW F z w := by
  change (k328r7c_phi F z QuadraticAlgebra.omega) w = k328r7c_fW F z w
  rw [k328r7c_phi_omega]

private noncomputable def k328r7c_xEnd (F : Type) [Field F] [Fintype F] [DecidableEq F] (x z : GL (Fin 3 ⊕ Fin 3) F) (hxz : x * z = z * x) :
    k328r7c_W F z →ₗ[F] k328r7c_W F z :=
  k328r7c_restrictSub (F := F) (W := k328r7c_W F z) (f := k328r7c_fOf F x) (by
    intro w hw
    rw [k328r7c_W, LinearMap.mem_ker] at hw ⊢
    rw [← Module.End.mul_apply, k328r7c_gz_comm F x z hxz, Module.End.mul_apply, hw, map_zero])

private theorem k328r7c_xEnd_fW (F : Type) [Field F] [Fintype F] [DecidableEq F] (x z : GL (Fin 3 ⊕ Fin 3) F) (hxz : x * z = z * x) :
    k328r7c_xEnd F x z hxz * k328r7c_fW F z = k328r7c_fW F z * k328r7c_xEnd F x z hxz := by
  apply LinearMap.ext
  intro w
  apply Subtype.ext
  change (k328r7c_fOf F x) ((k328r7c_fOf F z) (w : k328r7c_V F)) =
    (k328r7c_fOf F z) ((k328r7c_fOf F x) (w : k328r7c_V F))
  rw [← Module.End.mul_apply, k328r7c_fOf_comm F x z hxz, Module.End.mul_apply]

private noncomputable def k328r7c_xWmap (F : Type) [Field F] [Fintype F] [DecidableEq F] [CharP F 2] (x z : GL (Fin 3 ⊕ Fin 3) F)
    (hxz : x * z = z * x) :
    k328r7c_W F z →ₗ[QuadraticAlgebra F 1 1] k328r7c_W F z where
  toFun := k328r7c_xEnd F x z hxz
  map_add' a b := by
    apply Subtype.ext
    simp
  map_smul' l w := by
    change k328r7c_xEnd F x z hxz ((k328r7c_phi F z l) w) =
      (k328r7c_phi F z l) (k328r7c_xEnd F x z hxz w)
    rw [k328r7c_hphi]
    simp only [LinearMap.add_apply, LinearMap.smul_apply, Module.End.one_apply]
    rw [map_add, map_smul, map_smul]
    congr 1
    have h := congrArg (fun g : k328r7c_W F z →ₗ[F] k328r7c_W F z => g w)
      (k328r7c_xEnd_fW F x z hxz)
    simp only [Module.End.mul_apply] at h
    rw [h]

private theorem k328r7c_fOf_one (F : Type) [Field F] [Fintype F] [DecidableEq F] : k328r7c_fOf F (1 : GL (Fin 3 ⊕ Fin 3) F) = 1 := by
  simp only [k328r7c_fOf, map_one]
  rfl

private theorem k328r7c_inv_comm (F : Type) [Field F] [Fintype F] [DecidableEq F] (x z : GL (Fin 3 ⊕ Fin 3) F) (hxz : x * z = z * x) :
    x⁻¹ * z = z * x⁻¹ := by
  calc x⁻¹ * z = x⁻¹ * z * x * x⁻¹ := by group
    _ = x⁻¹ * (z * x) * x⁻¹ := by group
    _ = x⁻¹ * (x * z) * x⁻¹ := by rw [← hxz]
    _ = z * x⁻¹ := by group

private theorem k328r7c_xWmap_mul_inv (F : Type) [Field F] [Fintype F] [DecidableEq F] [CharP F 2] (x z : GL (Fin 3 ⊕ Fin 3) F)
    (hxz : x * z = z * x) :
    k328r7c_xWmap F x z hxz * k328r7c_xWmap F x⁻¹ z (k328r7c_inv_comm F x z hxz) = 1 := by
  apply LinearMap.ext
  intro w
  apply Subtype.ext
  change (k328r7c_fOf F x) ((k328r7c_fOf F x⁻¹) (w : k328r7c_V F)) = (w : k328r7c_V F)
  rw [← Module.End.mul_apply, ← k328r7c_fOf_mul, mul_inv_cancel, k328r7c_fOf_one]
  rfl

private theorem k328r7c_xWmap_inv_mul (F : Type) [Field F] [Fintype F] [DecidableEq F] [CharP F 2] (x z : GL (Fin 3 ⊕ Fin 3) F)
    (hxz : x * z = z * x) :
    k328r7c_xWmap F x⁻¹ z (k328r7c_inv_comm F x z hxz) * k328r7c_xWmap F x z hxz = 1 := by
  apply LinearMap.ext
  intro w
  apply Subtype.ext
  change (k328r7c_fOf F x⁻¹) ((k328r7c_fOf F x) (w : k328r7c_V F)) = (w : k328r7c_V F)
  rw [← Module.End.mul_apply, ← k328r7c_fOf_mul, inv_mul_cancel, k328r7c_fOf_one]
  rfl

private noncomputable def k328r7c_xWunit (F : Type) [Field F] [Fintype F] [DecidableEq F] [CharP F 2] (x z : GL (Fin 3 ⊕ Fin 3) F)
    (hxz : x * z = z * x) :
    (k328r7c_W F z →ₗ[QuadraticAlgebra F 1 1] k328r7c_W F z)ˣ where
  val := k328r7c_xWmap F x z hxz
  inv := k328r7c_xWmap F x⁻¹ z (k328r7c_inv_comm F x z hxz)
  val_inv := k328r7c_xWmap_mul_inv F x z hxz
  inv_val := k328r7c_xWmap_inv_mul F x z hxz

private noncomputable def k328r7c_resHom (F : Type) [Field F] [Fintype F] [DecidableEq F] [CharP F 2]
    (X : Subgroup (GL (Fin 3 ⊕ Fin 3) F)) (z : GL (Fin 3 ⊕ Fin 3) F)
    (hXc : X ≤ Subgroup.centralizer ({z} : Set (GL (Fin 3 ⊕ Fin 3) F))) :
    X →* (k328r7c_W F z →ₗ[QuadraticAlgebra F 1 1] k328r7c_W F z)ˣ where
  toFun x := k328r7c_xWunit F (x : GL (Fin 3 ⊕ Fin 3) F) z
    (Subgroup.mem_centralizer_iff.mp (hXc x.2) z (Set.mem_singleton z)).symm
  map_one' := by
    apply Units.ext
    apply LinearMap.ext
    intro w
    apply Subtype.ext
    change (k328r7c_fOf F (1 : GL (Fin 3 ⊕ Fin 3) F)) (w : k328r7c_V F) =
      (w : k328r7c_V F)
    rw [k328r7c_fOf_one]
    rfl
  map_mul' := by
    intro x y
    apply Units.ext
    apply LinearMap.ext
    intro w
    apply Subtype.ext
    change (k328r7c_fOf F ((x : GL (Fin 3 ⊕ Fin 3) F) * (y : GL (Fin 3 ⊕ Fin 3) F)))
        (w : k328r7c_V F) =
      (k328r7c_fOf F (x : GL (Fin 3 ⊕ Fin 3) F))
        ((k328r7c_fOf F (y : GL (Fin 3 ⊕ Fin 3) F)) (w : k328r7c_V F))
    rw [k328r7c_fOf_mul]
    rfl

private noncomputable def k328r7c_detHom (F : Type) [Field F] [Fintype F] [DecidableEq F] [CharP F 2]
    (X : Subgroup (GL (Fin 3 ⊕ Fin 3) F)) (z : GL (Fin 3 ⊕ Fin 3) F)
    (hXc : X ≤ Subgroup.centralizer ({z} : Set (GL (Fin 3 ⊕ Fin 3) F))) :
    X →* (QuadraticAlgebra F 1 1)ˣ :=
  (LinearEquiv.det).comp
    ((LinearMap.GeneralLinearGroup.generalLinearEquiv (QuadraticAlgebra F 1 1) (k328r7c_W F z)).toMonoidHom.comp
      (k328r7c_resHom F X z hXc))

private theorem k328r7c_detHom_eq_one (F : Type) [Field F] [Fintype F] [DecidableEq F] [CharP F 2]
    (X : Subgroup (GL (Fin 3 ⊕ Fin 3) F)) (z : GL (Fin 3 ⊕ Fin 3) F)
    (hXc : X ≤ Subgroup.centralizer ({z} : Set (GL (Fin 3 ⊕ Fin 3) F)))
    (hXperf : ⁅X, X⁆ = X) : k328r7c_detHom F X z hXc = 1 := by
  have : Group.IsPerfect X := Subgroup.isPerfect_iff.mpr hXperf
  exact k328r7c_perfect_hom_eq_one (k328r7c_detHom F X z hXc)

private theorem k328r7c_omega_sq_eq (F : Type) [Field F] [Fintype F] [DecidableEq F] :
    (QuadraticAlgebra.omega : QuadraticAlgebra F 1 1) ^ 2 =
      (1 : QuadraticAlgebra F 1 1) + QuadraticAlgebra.omega := by
  rw [pow_two, QuadraticAlgebra.omega_mul_omega_eq_add]
  simp

private theorem k328r7c_omega_cube (F : Type) [Field F] [Fintype F] [DecidableEq F] [CharP F 2] :
    (QuadraticAlgebra.omega : QuadraticAlgebra F 1 1) ^ 3 = 1 := by
  have h2 : (QuadraticAlgebra.omega : QuadraticAlgebra F 1 1) ^ 2 =
      (1 : QuadraticAlgebra F 1 1) + QuadraticAlgebra.omega := k328r7c_omega_sq_eq F
  have h2c : (2 : QuadraticAlgebra F 1 1) = 0 := by
    ext
    · change (2 : F) = 0
      exact CharP.cast_eq_zero F 2
    · rfl
  calc (QuadraticAlgebra.omega : QuadraticAlgebra F 1 1) ^ 3
      = QuadraticAlgebra.omega * QuadraticAlgebra.omega ^ 2 := by rw [pow_succ']
    _ = QuadraticAlgebra.omega * ((1 : QuadraticAlgebra F 1 1) + QuadraticAlgebra.omega) := by
          rw [h2]
    _ = QuadraticAlgebra.omega + QuadraticAlgebra.omega ^ 2 := by
          rw [mul_add, mul_one, ← pow_two]
    _ = QuadraticAlgebra.omega + ((1 : QuadraticAlgebra F 1 1) + QuadraticAlgebra.omega) := by
          rw [h2]
    _ = 1 := by
        rw [add_comm (1 : QuadraticAlgebra F 1 1) QuadraticAlgebra.omega, ← add_assoc,
          ← two_mul, h2c, zero_mul, zero_add]

private theorem k328r7c_omega_ne_one (F : Type) [Field F] [Fintype F] [DecidableEq F] :
    (QuadraticAlgebra.omega : QuadraticAlgebra F 1 1) ≠ 1 := by
  intro h
  have this := congrArg QuadraticAlgebra.im h
  have h1 : QuadraticAlgebra.im (QuadraticAlgebra.omega : QuadraticAlgebra F 1 1) = 1 := rfl
  have h0 : QuadraticAlgebra.im (1 : QuadraticAlgebra F 1 1) = 0 := rfl
  have hthis : (1 : F) = 0 := by rw [h1, h0] at this; exact this
  exact one_ne_zero hthis

private theorem k328r7c_xWmap_self (F : Type) [Field F] [Fintype F] [DecidableEq F] [CharP F 2] (z : GL (Fin 3 ⊕ Fin 3) F) :
    (k328r7c_xWmap F z z rfl :
        k328r7c_W F z →ₗ[QuadraticAlgebra F 1 1] k328r7c_W F z) =
      (QuadraticAlgebra.omega : QuadraticAlgebra F 1 1) •
        (LinearMap.id : k328r7c_W F z →ₗ[QuadraticAlgebra F 1 1] k328r7c_W F z) := by
  apply LinearMap.ext
  intro w
  show k328r7c_xWmap F z z rfl w =
    (QuadraticAlgebra.omega : QuadraticAlgebra F 1 1) • (w : k328r7c_W F z)
  rw [k328r7c_omega_smul]
  rfl

private theorem k328r7c_omega_pow_finrank_eq_one (F : Type) [Field F] [Fintype F] [DecidableEq F] [CharP F 2] (hF : Fintype.card F = 8)
    (X : Subgroup (GL (Fin 3 ⊕ Fin 3) F)) (z : GL (Fin 3 ⊕ Fin 3) F)
    (hXc : X ≤ Subgroup.centralizer ({z} : Set (GL (Fin 3 ⊕ Fin 3) F)))
    (hXperf : ⁅X, X⁆ = X) (hzX : z ∈ X) :
    (QuadraticAlgebra.omega : QuadraticAlgebra F 1 1) ^
      Module.finrank (QuadraticAlgebra F 1 1) (k328r7c_W F z) = 1 := by
  have : Fact (∀ r : F, r ^ 2 ≠ 1 + 1 * r) := k328r7c_fact F hF
  let : Field (QuadraticAlgebra F 1 1) := inferInstance
  have hdet1 : k328r7c_detHom F X z hXc ⟨z, hzX⟩ = 1 := by
    rw [k328r7c_detHom_eq_one F X z hXc hXperf]
    rfl
  have hz1 : ((k328r7c_detHom F X z hXc ⟨z, hzX⟩ : (QuadraticAlgebra F 1 1)ˣ) :
      QuadraticAlgebra F 1 1) = 1 := by rw [hdet1]; rfl
  have hval : ((k328r7c_detHom F X z hXc ⟨z, hzX⟩ : (QuadraticAlgebra F 1 1)ˣ) :
      QuadraticAlgebra F 1 1) = LinearMap.det (k328r7c_xWmap F z z rfl) := by
    simp only [k328r7c_detHom, MonoidHom.comp_apply, LinearEquiv.coe_det]
    change LinearMap.det (↑((k328r7c_resHom F X z hXc) ⟨z, hzX⟩) :
      k328r7c_W F z →ₗ[QuadraticAlgebra F 1 1] k328r7c_W F z) =
      LinearMap.det (k328r7c_xWmap F z z rfl)
    congr 1
  rw [hval] at hz1
  have hsmul : LinearMap.det ((QuadraticAlgebra.omega : QuadraticAlgebra F 1 1) •
      (LinearMap.id : k328r7c_W F z →ₗ[QuadraticAlgebra F 1 1] k328r7c_W F z)) =
      (QuadraticAlgebra.omega : QuadraticAlgebra F 1 1) ^
        Module.finrank (QuadraticAlgebra F 1 1) (k328r7c_W F z) := by
    rw [LinearMap.det_smul, LinearMap.det_id, mul_one]
  rw [k328r7c_xWmap_self F z, hsmul] at hz1
  exact hz1

private theorem k328r7c_three_dvd_finrank (F : Type) [Field F] [Fintype F] [DecidableEq F] [CharP F 2] (hF : Fintype.card F = 8)
    (X : Subgroup (GL (Fin 3 ⊕ Fin 3) F)) (z : GL (Fin 3 ⊕ Fin 3) F)
    (hXc : X ≤ Subgroup.centralizer ({z} : Set (GL (Fin 3 ⊕ Fin 3) F)))
    (hXperf : ⁅X, X⁆ = X) (hzX : z ∈ X) :
    3 ∣ Module.finrank (QuadraticAlgebra F 1 1) (k328r7c_W F z) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hord : orderOf (QuadraticAlgebra.omega : QuadraticAlgebra F 1 1) = 3 :=
    orderOf_eq_prime (k328r7c_omega_cube F) (k328r7c_omega_ne_one F)
  have h := orderOf_dvd_iff_pow_eq_one.mpr
    (k328r7c_omega_pow_finrank_eq_one F hF X z hXc hXperf hzX)
  rwa [hord] at h

private theorem k328r7c_scalarTower (F : Type) [Field F] [Fintype F] [DecidableEq F] [CharP F 2] (z : GL (Fin 3 ⊕ Fin 3) F) :
    IsScalarTower F (QuadraticAlgebra F 1 1) (k328r7c_W F z) := by
  refine ⟨fun c l w => ?_⟩
  change (k328r7c_phi F z (c • l)) w = c • (k328r7c_phi F z l w)
  have hcl : k328r7c_phi F z (c • l) = c • k328r7c_phi F z l := by
    rw [show c • l = algebraMap F (QuadraticAlgebra F 1 1) c * l from Algebra.smul_def c l]
    rw [map_mul, k328r7c_phi_algebraMap]
    rfl
  rw [hcl]
  rfl

private theorem k328r7c_finrank_eq (F : Type) [Field F] [Fintype F] [DecidableEq F] [CharP F 2] (hF : Fintype.card F = 8)
    (z : GL (Fin 3 ⊕ Fin 3) F) :
    Module.finrank F (k328r7c_W F z) =
      2 * Module.finrank (QuadraticAlgebra F 1 1) (k328r7c_W F z) := by
  have : Fact (∀ r : F, r ^ 2 ≠ 1 + 1 * r) := k328r7c_fact F hF
  let : Field (QuadraticAlgebra F 1 1) := inferInstance
  have := k328r7c_scalarTower F z
  rw [← Module.finrank_mul_finrank F (QuadraticAlgebra F 1 1) (k328r7c_W F z),
    QuadraticAlgebra.finrank_eq_two]

private theorem k328r7c_finrank_le_six (F : Type) [Field F] [Fintype F] [DecidableEq F] [CharP F 2] (z : GL (Fin 3 ⊕ Fin 3) F) :
    Module.finrank F (k328r7c_W F z) ≤ 6 := by
  have h := Submodule.finrank_le (k328r7c_W F z)
  have hV : Module.finrank F (k328r7c_V F) = 6 := by
    change Module.finrank F (Fin 3 ⊕ Fin 3 → F) = 6
    simp
  rwa [hV] at h

private theorem k328r7c_fOf_injective (F : Type) [Field F] [Fintype F] [DecidableEq F] : Function.Injective (k328r7c_fOf F) := by
  intro a b h
  exact Matrix.GeneralLinearGroup.toLin.injective (Units.ext (by simpa [k328r7c_fOf] using h))

private theorem k328r7c_fOf_pow (F : Type) [Field F] [Fintype F] [DecidableEq F] (z : GL (Fin 3 ⊕ Fin 3) F) (n : ℕ) :
    k328r7c_fOf F (z ^ n) = (k328r7c_fOf F z) ^ n := by
  simp only [k328r7c_fOf]
  rw [map_pow, Units.val_pow_eq_pow_val]

private theorem k328r7c_W_ne_bot (F : Type) [Field F] [Fintype F] [DecidableEq F] [CharP F 2] (z : GL (Fin 3 ⊕ Fin 3) F)
    (hzord : orderOf z = 3) : k328r7c_W F z ≠ ⊥ := by
  intro hbot
  have hz3 : z ^ 3 = 1 := by simpa [hzord] using pow_orderOf_eq_one z
  have hf3 : (k328r7c_fOf F z) ^ 3 = 1 := by
    rw [← k328r7c_fOf_pow, hz3, k328r7c_fOf_one]
  let g : Module.End F (k328r7c_V F) := (k328r7c_fOf F z) ^ 2 + k328r7c_fOf F z + 1
  have hgker : LinearMap.ker g = ⊥ := by
    change LinearMap.ker ((k328r7c_fOf F z) ^ 2 + k328r7c_fOf F z + 1) = ⊥
    rw [← hbot]
    rfl
  have hpoly : ((k328r7c_fOf F z) - 1) * g = 0 := by
    have h1 : ((k328r7c_fOf F z) - 1) * g = (k328r7c_fOf F z) ^ 3 - 1 := by
      dsimp only [g]
      rw [sub_mul, one_mul]
      have hmul : (k328r7c_fOf F z) * ((k328r7c_fOf F z) ^ 2 + k328r7c_fOf F z + 1) =
          (k328r7c_fOf F z) ^ 3 + (k328r7c_fOf F z) ^ 2 + k328r7c_fOf F z := by
        calc (k328r7c_fOf F z) * ((k328r7c_fOf F z) ^ 2 + k328r7c_fOf F z + 1)
            = (k328r7c_fOf F z) * (k328r7c_fOf F z) ^ 2 +
              (k328r7c_fOf F z) * (k328r7c_fOf F z) + k328r7c_fOf F z := by
              rw [mul_add, mul_add, mul_one]
          _ = (k328r7c_fOf F z) ^ 3 + (k328r7c_fOf F z) ^ 2 + k328r7c_fOf F z := by
              rw [show (k328r7c_fOf F z) * (k328r7c_fOf F z) ^ 2 = (k328r7c_fOf F z) ^ 3
                    from (pow_succ' (k328r7c_fOf F z) 2).symm,
                  show (k328r7c_fOf F z) * (k328r7c_fOf F z) = (k328r7c_fOf F z) ^ 2
                    from (pow_two (k328r7c_fOf F z)).symm]
      rw [hmul]
      abel
    rw [h1, hf3, sub_self]
  have hinj : Function.Injective g := by
    rw [← LinearMap.ker_eq_bot]
    exact hgker
  have hsurj : Function.Surjective g := by
    have : Finite (k328r7c_V F) := inferInstance
    exact Finite.injective_iff_surjective.mp hinj
  have hfeq : k328r7c_fOf F z = 1 := by
    apply LinearMap.ext
    intro w
    obtain ⟨v, rfl⟩ := hsurj w
    have h0 : ((k328r7c_fOf F z) - 1) (g v) = 0 := by
      rw [← Module.End.mul_apply, hpoly, LinearMap.zero_apply]
    have h0' : (k328r7c_fOf F z) (g v) - g v = 0 := by
      simpa only [LinearMap.sub_apply, Module.End.one_apply, LinearMap.zero_apply] using h0
    exact sub_eq_zero.mp h0'
  have hz1 : z = 1 := k328r7c_fOf_injective F (by rw [hfeq, k328r7c_fOf_one])
  rw [hz1, orderOf_one] at hzord
  norm_num at hzord

private theorem k328r7c_W_eq_top (F : Type) [Field F] [Fintype F] [DecidableEq F] [CharP F 2] (hF : Fintype.card F = 8)
    (X : Subgroup (GL (Fin 3 ⊕ Fin 3) F)) (z : GL (Fin 3 ⊕ Fin 3) F)
    (hXc : X ≤ Subgroup.centralizer ({z} : Set (GL (Fin 3 ⊕ Fin 3) F)))
    (hXperf : ⁅X, X⁆ = X) (hzX : z ∈ X) (hzord : orderOf z = 3) :
    k328r7c_W F z = ⊤ := by
  have hdvd : 3 ∣ Module.finrank (QuadraticAlgebra F 1 1) (k328r7c_W F z) :=
    k328r7c_three_dvd_finrank F hF X z hXc hXperf hzX
  have hfr := k328r7c_finrank_eq F hF z
  have hle := k328r7c_finrank_le_six F z
  have hne := k328r7c_W_ne_bot F z hzord
  have hm_ne_zero : Module.finrank (QuadraticAlgebra F 1 1) (k328r7c_W F z) ≠ 0 := by
    intro h0
    have hfin0 : Module.finrank F (k328r7c_W F z) = 0 := by rw [hfr, h0, mul_zero]
    have : Subsingleton (k328r7c_W F z) := Module.finrank_zero_iff.mp hfin0
    exact hne (Submodule.subsingleton_iff_eq_bot.mp ‹Subsingleton (k328r7c_W F z)›)
  have hmpos : 0 < Module.finrank (QuadraticAlgebra F 1 1) (k328r7c_W F z) :=
    Nat.pos_of_ne_zero hm_ne_zero
  have hmle : Module.finrank (QuadraticAlgebra F 1 1) (k328r7c_W F z) ≤ 3 := by
    have := hfr ▸ hle
    omega
  have hm : Module.finrank (QuadraticAlgebra F 1 1) (k328r7c_W F z) = 3 := by
    obtain ⟨k, hk⟩ := hdvd
    omega
  have hV : Module.finrank F (k328r7c_V F) = 6 := by
    change Module.finrank F (Fin 3 ⊕ Fin 3 → F) = 6
    simp
  have : Module.finrank F (k328r7c_W F z) = Module.finrank F (k328r7c_V F) := by
    rw [hfr, hm, hV]
  exact Submodule.eq_top_of_finrank_eq this

private theorem k328r7c_fW_zero (F : Type) [Field F] [Fintype F] [DecidableEq F] [CharP F 2] (hF : Fintype.card F = 8)
    (X : Subgroup (GL (Fin 3 ⊕ Fin 3) F)) (z : GL (Fin 3 ⊕ Fin 3) F)
    (hXc : X ≤ Subgroup.centralizer ({z} : Set (GL (Fin 3 ⊕ Fin 3) F)))
    (hXperf : ⁅X, X⁆ = X) (hzX : z ∈ X) (hzord : orderOf z = 3) :
    (k328r7c_fOf F z) ^ 2 + k328r7c_fOf F z + 1 = 0 := by
  have htop := k328r7c_W_eq_top F hF X z hXc hXperf hzX hzord
  have hker : LinearMap.ker ((k328r7c_fOf F z) ^ 2 + k328r7c_fOf F z + 1) = ⊤ := by
    rw [← htop]; rfl
  exact LinearMap.ker_eq_top.mp hker

private theorem k328r7c_fOf_apply (F : Type) [Field F] [Fintype F] [DecidableEq F] (z : GL (Fin 3 ⊕ Fin 3) F) (x : k328r7c_V F) :
    k328r7c_fOf F z x = (z : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) F) *ᵥ x := by
  rw [k328r7c_fOf, Matrix.GeneralLinearGroup.toLin_apply, Matrix.mulVecLin_apply]

private theorem k328r7c_frame_data (F : Type) [Field F] [Fintype F] [DecidableEq F] [CharP F 2] (hF : Fintype.card F = 8)
    (X : Subgroup (GL (Fin 3 ⊕ Fin 3) F)) (z : GL (Fin 3 ⊕ Fin 3) F)
    (hXc : X ≤ Subgroup.centralizer ({z} : Set (GL (Fin 3 ⊕ Fin 3) F)))
    (hXperf : ⁅X, X⁆ = X) (hzX : z ∈ X) (hzord : orderOf z = 3)
    (hzH : z ∈ StatedSp 3 F) :
    ∃ v : Fin 3 → k328r7c_V F,
      LinearIndependent F (Sum.elim v (fun i => k328r7c_fOf F z (v i))) ∧
      (∀ i j, spForm 3 F (v i) (k328r7c_fOf F z (v j)) = if i = j then 1 else 0) ∧
      (∀ i j, spForm 3 F (v i) (v j) = 0) := by
  let B : BilinForm F (k328r7c_V F) := spForm 3 F
  have hAlt : B.IsAlt := spForm_isAlt
  have hBnd : B.Nondegenerate := spForm_nondegenerate
  have hBleft : ∀ x, (∀ y, B x y = 0) → x = 0 := fun x hx =>
    hBnd.2 x (fun y => hAlt.isRefl x y (hx y))
  have hf0 : (k328r7c_fOf F z) ^ 2 + k328r7c_fOf F z + 1 = 0 :=
    k328r7c_fW_zero F hF X z hXc hXperf hzX hzord
  have hz3 : ∀ x, k328r7c_fOf F z (k328r7c_fOf F z x) + k328r7c_fOf F z x + x = 0 := by
    intro x
    have h := congrArg (fun g : Module.End F (k328r7c_V F) => g x) hf0
    simpa only [LinearMap.add_apply, Module.End.one_apply, LinearMap.zero_apply, pow_two,
      Module.End.mul_apply] using h
  have hfB : ∀ x y, B (k328r7c_fOf F z x) (k328r7c_fOf F z y) = B x y := by
    intro x y
    change spForm 3 F (k328r7c_fOf F z x) (k328r7c_fOf F z y) = spForm 3 F x y
    rw [k328r7c_fOf_apply F z x, k328r7c_fOf_apply F z y]
    exact (CFSG.ClassicalGroups.Symplectic.mem_statedSp_iff_forall z).mp hzH x y
  obtain ⟨k, v, hk2, hlin, horth, hv⟩ :=
    k328_isometry_frame B hBleft hAlt.self_eq_zero (k328r7c_fOf F z) hfB hz3
  have hfr : Module.finrank F (k328r7c_V F) = 6 := by
    change Module.finrank F (Fin 3 ⊕ Fin 3 → F) = 6
    simp
  have hk : k = 3 := by omega
  subst hk
  exact ⟨v, hlin, horth, hv⟩

private theorem k328r7c_isometry (F : Type) [Field F] [Fintype F] [DecidableEq F] [CharP F 2] (z : GL (Fin 3 ⊕ Fin 3) F)
    (hzH : z ∈ StatedSp 3 F) :
    ∀ x y, spForm 3 F (k328r7c_fOf F z x) (k328r7c_fOf F z y) = spForm 3 F x y := by
  intro x y
  rw [k328r7c_fOf_apply F z x, k328r7c_fOf_apply F z y]
  exact (CFSG.ClassicalGroups.Symplectic.mem_statedSp_iff_forall z).mp hzH x y

private theorem k328r7c_spForm_single (F : Type) [Field F] [Fintype F] [DecidableEq F] (c d : Fin 3 ⊕ Fin 3) :
    spForm 3 F (Pi.single c 1) (Pi.single d 1) = spJ 3 F c d := by
  rw [spForm_apply, Matrix.mulVec_single_one, dotProduct]
  rw [Finset.sum_eq_single c]
  · simp [Matrix.col_apply, Pi.single_eq_same]
  · intro b _ hb
    simp [Pi.single_eq_of_ne hb]
  · intro h
    exact absurd (Finset.mem_univ c) h

private theorem k328r7c_conj (F : Type) [Field F] [Fintype F] [DecidableEq F] [CharP F 2] (hF : Fintype.card F = 8)
    (X : Subgroup (GL (Fin 3 ⊕ Fin 3) F)) (z z₀ : GL (Fin 3 ⊕ Fin 3) F)
    (hz₀ : (z₀ : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) F) = rhoL F 0 1)
    (hXc : X ≤ Subgroup.centralizer ({z} : Set (GL (Fin 3 ⊕ Fin 3) F)))
    (hXperf : ⁅X, X⁆ = X) (hzX : z ∈ X) (hzord : orderOf z = 3)
    (hzH : z ∈ StatedSp 3 F) :
    ∃ g ∈ StatedSp 3 F, g * z * g⁻¹ = z₀ := by
  obtain ⟨v, hlin, horth, hv⟩ := k328r7c_frame_data F hF X z hXc hXperf hzX hzord hzH
  have : CharP (k328r7c_V F) 2 := inferInstance
  have hf0 : (k328r7c_fOf F z) ^ 2 + k328r7c_fOf F z + 1 = 0 :=
    k328r7c_fW_zero F hF X z hXc hXperf hzX hzord
  have hz3 : ∀ x, k328r7c_fOf F z (k328r7c_fOf F z x) + k328r7c_fOf F z x + x = 0 := by
    intro x
    have h := congrArg (fun g : Module.End F (k328r7c_V F) => g x) hf0
    simpa only [LinearMap.add_apply, Module.End.one_apply, LinearMap.zero_apply, pow_two,
      Module.End.mul_apply] using h
  have hfB := k328r7c_isometry F z hzH
  have hzj : ∀ j, v j = k328r7c_fOf F z (k328r7c_fOf F z (v j)) + k328r7c_fOf F z (v j) :=
    fun j => (CharTwo.add_eq_zero.mp (hz3 (v j))).symm
  have hzv : ∀ i j, spForm 3 F (k328r7c_fOf F z (v i)) (v j) = if i = j then 1 else 0 := by
    intro i j
    rw [hzj j, map_add, hfB (v i) (k328r7c_fOf F z (v j)), hfB (v i) (v j), hv i j, add_zero]
    exact horth i j
  have hzz : ∀ i j, spForm 3 F (k328r7c_fOf F z (v i)) (k328r7c_fOf F z (v j)) = 0 := by
    intro i j
    rw [hfB (v i) (v j), hv i j]
  let img : (Fin 3 ⊕ Fin 3) → (Fin 3 ⊕ Fin 3) → F := Sum.elim v (fun i => k328r7c_fOf F z (v i))
  let M : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) F := ofColumns F img
  have hMcol : M.col = img := by
    funext c
    ext r
    rw [Matrix.col_apply]
    rfl
  have hlin' : LinearIndependent F M.col := by rw [hMcol]; exact hlin
  have hunit : IsUnit M := (Matrix.linearIndependent_cols_iff_isUnit).mp hlin'
  have hdet : M.det ≠ 0 := (Matrix.isUnit_iff_isUnit_det (A := M)).mp hunit |>.ne_zero
  let g₀ : GL (Fin 3 ⊕ Fin 3) F := Matrix.GeneralLinearGroup.mkOfDetNeZero M hdet
  have hg₀coe : (g₀ : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) F) = M := rfl
  have hspJ : ∀ c d : Fin 3 ⊕ Fin 3, spJ 3 F c d = spForm 3 F (img c) (img d) := by
    intro c d
    rcases c with i | i <;> rcases d with j | j
    · simp only [img, Sum.elim_inl]
      rw [hv i j]
      simp [spJ, Matrix.fromBlocks]
    · simp only [img, Sum.elim_inl, Sum.elim_inr]
      rw [horth i j]
      simp [spJ, Matrix.fromBlocks, Matrix.one_apply]
    · simp only [img, Sum.elim_inl, Sum.elim_inr]
      rw [hzv i j]
      simp [spJ, Matrix.fromBlocks, Matrix.one_apply, CharTwo.neg_eq]
    · simp only [img, Sum.elim_inr]
      rw [hzz i j]
      simp [spJ, Matrix.fromBlocks]
  have hform : (spForm 3 F).comp (Matrix.toLin' M) (Matrix.toLin' M) = spForm 3 F := by
    apply LinearMap.BilinForm.ext_basis (Pi.basisFun F (Fin 3 ⊕ Fin 3))
    intro i j
    rw [LinearMap.BilinForm.comp_apply, Matrix.toLin'_apply, Matrix.toLin'_apply,
      Pi.basisFun_apply, Pi.basisFun_apply, Matrix.mulVec_single_one, Matrix.mulVec_single_one,
      hMcol, k328r7c_spForm_single]
    exact (hspJ i j).symm
  have hMsp : g₀ ∈ StatedSp 3 F := by
    rw [CFSG.ClassicalGroups.Symplectic.mem_statedSp_iff_forall]
    intro x y
    rw [hg₀coe]
    have h := congrArg (fun B : BilinForm F (k328r7c_V F) => B x y) hform
    simpa only [LinearMap.BilinForm.comp_apply, Matrix.toLin'_apply] using h
  have hzsq : ∀ x : k328r7c_V F,
      ((z : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) F) *
          (z : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) F)) *ᵥ x =
      (z : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) F) *ᵥ x + x := by
    intro x
    have h := hz3 x
    rw [k328r7c_fOf_apply F z (k328r7c_fOf F z x), k328r7c_fOf_apply F z x] at h
    have h' : ((z : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) F) *ᵥ
          ((z : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) F) *ᵥ x)) +
        ((z : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) F) *ᵥ x + x) = 0 := by
      simpa only [add_assoc] using h
    have hz := CharTwo.add_eq_zero.mp h'
    rwa [Matrix.mulVec_mulVec] at hz
  have hz0col_inl : ∀ i : Fin 3,
      (z₀ : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) F).col (Sum.inl i) =
        Pi.single (Sum.inr i) 1 := by
    intro i
    rw [hz₀]
    ext r
    rcases r with j | j <;> fin_cases i <;> fin_cases j <;>
      simp [rhoL, Matrix.fromBlocks, Matrix.col_apply]
  have hz0col_inr : ∀ i : Fin 3,
      (z₀ : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) F).col (Sum.inr i) =
        Pi.single (Sum.inl i) 1 + Pi.single (Sum.inr i) 1 := by
    intro i
    rw [hz₀]
    ext r
    rcases r with j | j <;> fin_cases i <;> fin_cases j <;>
      simp [rhoL, Matrix.fromBlocks, Matrix.col_apply]
  have hzM : (z : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) F) * M =
      M * (z₀ : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) F) := by
    apply Matrix.ext
    intro r c
    have hcol : ((z : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) F) * M).col c =
        (M * (z₀ : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) F)).col c := by
      rw [Matrix.col_mul_eq_mulVec_col, Matrix.col_mul_eq_mulVec_col, hMcol]
      rcases c with i | i
      · simp only [img, Sum.elim_inl]
        rw [hz0col_inl i, Matrix.mulVec_single_one, hMcol]
        simp only [img, Sum.elim_inr]
        rw [k328r7c_fOf_apply F z (v i)]
      · simp only [img, Sum.elim_inr]
        rw [hz0col_inr i, Matrix.mulVec_add, Matrix.mulVec_single_one, Matrix.mulVec_single_one,
          hMcol]
        simp only [img, Sum.elim_inl, Sum.elim_inr]
        rw [k328r7c_fOf_apply F z (v i), Matrix.mulVec_mulVec, hzsq (v i)]
        exact add_comm _ _
    exact (Matrix.col_apply _ c r).symm.trans
      ((congrFun hcol r).trans (Matrix.col_apply _ c r))
  have hzMgl : z * g₀ = g₀ * z₀ := by
    apply Units.ext
    simpa only [Units.val_mul, hg₀coe] using hzM
  refine ⟨g₀⁻¹, inv_mem hMsp, ?_⟩
  show g₀⁻¹ * z * g₀ = z₀
  calc g₀⁻¹ * z * g₀ = g₀⁻¹ * (z * g₀) := by group
    _ = g₀⁻¹ * (g₀ * z₀) := by rw [hzMgl]
    _ = z₀ := by group

theorem row7_class (F : Type) [Field F] [Fintype F] [DecidableEq F]
    (hF : Fintype.card F = 8) (z₀ t₀ : GL (Fin 3 ⊕ Fin 3) F)
    (hz : (z₀ : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) F) = rhoL F 0 1)
    (ht : (t₀ : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) F) =
      rhoL F (Matrix.diagonal ![0, 1, 1]) (Matrix.diagonal ![1, 1, 0])) :
    ClassLeaf (StatedSp 3 F) z₀ := by
  have _ht := ht
  intro z hzH hzord X hXH hzX hXc hXperf
  have : CharP F 2 := charP_of_card_eq_prime_pow (p := 2) (f := 3) hF
  obtain ⟨g, hgH, hg⟩ := k328r7c_conj F hF X z z₀ hz hXc hXperf hzX hzord (hXH hzX)
  exact ⟨g, hgH, Or.inl hg⟩

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.K328

module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.K328.Rows
public import CFSG.LinearAlgebra.CubeRootBlock
public import CFSG.RankThree.PartOne.S11d.OrthDicksonOmega
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.K328.Classical.Frame
public import CFSG.ClassicalGroups.Orthogonal.OmegaMinus8ThreeLocalType
public import CFSG.ClassicalInvolution.RouteD.TWYPlane
public import CFSG.ClassicalInvolution.RouteD.TWYType

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.K328

open CFSG.Open
open CFSG.LieType.Universal.Spin
open CFSG.ClassicalGroups.Orthogonal
open TauCeti.QuadraticMap
open Module QuadraticMap
open Polynomial
open CFSG.GroupTheory.WeirSylow

namespace K328R8L2

private theorem k328r8c_l2_perfect_hom_eq_one {G : Type*} [Group G] [Group.IsPerfect G]
    {A : Type*} [CommGroup A] (f : G →* A) : f = 1 := by
  have : Group.IsPerfect f.range := Group.IsPerfect.range f
  have : IsMulCommutative f.range := isMulCommutative_iff.mpr fun a b =>
    Subtype.ext (by simp only [Subgroup.coe_mul]; exact mul_comm _ _)
  have : Subsingleton f.range := Group.IsPerfect.subsingleton_of_isMulCommutative
  ext x
  exact congrArg Subtype.val
    (Subsingleton.elim (⟨f x, MonoidHom.mem_range.mpr ⟨x, rfl⟩⟩ : f.range)
      ⟨1, MonoidHom.mem_range.mpr ⟨1, f.map_one⟩⟩)

private theorem k328r8c_l2_no_cube_root (F : Type) [Field F] [Fintype F]
    (hF : Fintype.card F = 8) (t : F) (h : t ^ 2 + t + 1 = 0) : False := by
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

private theorem k328r8c_l2_anisotropic (F : Type) [Field F] [Fintype F]
    (hF : Fintype.card F = 8) (x y : F) (h : x ^ 2 + 1 * x * y + y ^ 2 = 0) :
    x = 0 ∧ y = 0 := by
  by_cases hy : y = 0
  · subst hy
    have hx : x ^ 2 = 0 := by simpa using h
    exact ⟨sq_eq_zero_iff.mp hx, rfl⟩
  · have ht : (x / y) ^ 2 + x / y + 1 = 0 := by
      field_simp
      linear_combination h
    exact absurd (k328r8c_l2_no_cube_root F hF (x / y) ht) (by simp)

private theorem k328r8c_l2_fact (F : Type) [Field F] [Fintype F] (hF : Fintype.card F = 8) :
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
  obtain ⟨-, h1⟩ := k328r8c_l2_anisotropic F hF r 1 hq
  exact one_ne_zero h1

private abbrev k328r8c_l2_V (F : Type) : Type := Fin 3 ⊕ Fin 3 ⊕ Fin 2 → F

private noncomputable def k328r8c_l2_fOf (F : Type) [Field F]
    (z : GL (Fin 3 ⊕ Fin 3 ⊕ Fin 2) F) : Module.End F (k328r8c_l2_V F) :=
  (Matrix.GeneralLinearGroup.toLin z : Module.End F (k328r8c_l2_V F))

private theorem k328r8c_l2_fOf_mul (F : Type) [Field F] (x y : GL (Fin 3 ⊕ Fin 3 ⊕ Fin 2) F) :
    k328r8c_l2_fOf F (x * y) = k328r8c_l2_fOf F x * k328r8c_l2_fOf F y := by
  simp only [k328r8c_l2_fOf, map_mul]
  rfl

private theorem k328r8c_l2_fOf_comm (F : Type) [Field F]
    (x z : GL (Fin 3 ⊕ Fin 3 ⊕ Fin 2) F) (hxz : x * z = z * x) :
    k328r8c_l2_fOf F x * k328r8c_l2_fOf F z = k328r8c_l2_fOf F z * k328r8c_l2_fOf F x := by
  have h := congrArg (k328r8c_l2_fOf F) hxz
  rw [k328r8c_l2_fOf_mul, k328r8c_l2_fOf_mul] at h
  exact h

private noncomputable def k328r8c_l2_W (F : Type) [Field F]
    (z : GL (Fin 3 ⊕ Fin 3 ⊕ Fin 2) F) : Submodule F (k328r8c_l2_V F) :=
  LinearMap.ker ((k328r8c_l2_fOf F z) ^ 2 + k328r8c_l2_fOf F z + 1)

private noncomputable def k328r8c_l2_restrictSub (F : Type) [Field F]
    {W : Submodule F (k328r8c_l2_V F)}
    {f : k328r8c_l2_V F →ₗ[F] k328r8c_l2_V F} (hf : ∀ w ∈ W, f w ∈ W) : W →ₗ[F] W where
  toFun w := ⟨f w, hf w w.2⟩
  map_add' w₁ w₂ := by ext; simp
  map_smul' c w := by ext; simp

private theorem k328r8c_l2_gz_comm (F : Type) [Field F]
    (x z : GL (Fin 3 ⊕ Fin 3 ⊕ Fin 2) F) (hxz : x * z = z * x) :
    ((k328r8c_l2_fOf F z) ^ 2 + k328r8c_l2_fOf F z + 1) * k328r8c_l2_fOf F x =
      k328r8c_l2_fOf F x * ((k328r8c_l2_fOf F z) ^ 2 + k328r8c_l2_fOf F z + 1) := by
  have hxz' := k328r8c_l2_fOf_comm F x z hxz
  have hz2 : (k328r8c_l2_fOf F z) ^ 2 * k328r8c_l2_fOf F x =
      k328r8c_l2_fOf F x * (k328r8c_l2_fOf F z) ^ 2 := by
    rw [pow_two]
    calc (k328r8c_l2_fOf F z * k328r8c_l2_fOf F z) * k328r8c_l2_fOf F x
        = k328r8c_l2_fOf F z * (k328r8c_l2_fOf F z * k328r8c_l2_fOf F x) := by rw [mul_assoc]
      _ = k328r8c_l2_fOf F z * (k328r8c_l2_fOf F x * k328r8c_l2_fOf F z) := by rw [hxz']
      _ = (k328r8c_l2_fOf F z * k328r8c_l2_fOf F x) * k328r8c_l2_fOf F z := by rw [mul_assoc]
      _ = (k328r8c_l2_fOf F x * k328r8c_l2_fOf F z) * k328r8c_l2_fOf F z := by rw [hxz']
      _ = k328r8c_l2_fOf F x * (k328r8c_l2_fOf F z * k328r8c_l2_fOf F z) := by rw [mul_assoc]
  calc ((k328r8c_l2_fOf F z) ^ 2 + k328r8c_l2_fOf F z + 1) * k328r8c_l2_fOf F x
      = (k328r8c_l2_fOf F z) ^ 2 * k328r8c_l2_fOf F x + k328r8c_l2_fOf F z * k328r8c_l2_fOf F x +
          1 * k328r8c_l2_fOf F x := by rw [add_mul, add_mul, one_mul]
    _ = k328r8c_l2_fOf F x * (k328r8c_l2_fOf F z) ^ 2 + k328r8c_l2_fOf F x * k328r8c_l2_fOf F z +
          k328r8c_l2_fOf F x := by rw [hz2, hxz', one_mul]
    _ = k328r8c_l2_fOf F x * ((k328r8c_l2_fOf F z) ^ 2 + k328r8c_l2_fOf F z + 1) := by
          rw [mul_add, mul_add, mul_one]

private noncomputable def k328r8c_l2_fW (F : Type) [Field F]
    (z : GL (Fin 3 ⊕ Fin 3 ⊕ Fin 2) F) : k328r8c_l2_W F z →ₗ[F] k328r8c_l2_W F z :=
  k328r8c_l2_restrictSub (F := F) (W := k328r8c_l2_W F z) (f := k328r8c_l2_fOf F z) (by
    intro w hw
    rw [k328r8c_l2_W, LinearMap.mem_ker] at hw ⊢
    rw [← Module.End.mul_apply, k328r8c_l2_gz_comm F z z rfl, Module.End.mul_apply, hw, map_zero])

private theorem k328r8c_l2_fW_rel (F : Type) [Field F] [CharP F 2]
    (z : GL (Fin 3 ⊕ Fin 3 ⊕ Fin 2) F) :
    k328r8c_l2_fW F z * k328r8c_l2_fW F z = 1 + k328r8c_l2_fW F z := by
  apply LinearMap.ext
  intro w
  apply Subtype.ext
  change (k328r8c_l2_fOf F z) ((k328r8c_l2_fOf F z) (w : k328r8c_l2_V F)) =
    (w : k328r8c_l2_V F) + (k328r8c_l2_fOf F z) (w : k328r8c_l2_V F)
  have hw := w.2
  change (w : k328r8c_l2_V F) ∈ LinearMap.ker
    ((k328r8c_l2_fOf F z) ^ 2 + k328r8c_l2_fOf F z + 1) at hw
  rw [LinearMap.mem_ker] at hw
  have h' : (k328r8c_l2_fOf F z) ((k328r8c_l2_fOf F z) (w : k328r8c_l2_V F)) +
      ((k328r8c_l2_fOf F z) (w : k328r8c_l2_V F) + (w : k328r8c_l2_V F)) = 0 := by
    simpa only [pow_two, Module.End.mul_apply, LinearMap.add_apply, Module.End.one_apply,
      add_assoc] using hw
  have : CharP (k328r8c_l2_V F) 2 := inferInstance
  exact (CharTwo.add_eq_zero.mp h').trans (add_comm ((k328r8c_l2_fOf F z) (w : k328r8c_l2_V F))
    (w : k328r8c_l2_V F))

private noncomputable def k328r8c_l2_phi (F : Type) [Field F] [CharP F 2]
    (z : GL (Fin 3 ⊕ Fin 3 ⊕ Fin 2) F) :
    QuadraticAlgebra F 1 1 →ₐ[F] Module.End F (k328r8c_l2_W F z) :=
  QuadraticAlgebra.lift (a := 1) (b := 1) ⟨k328r8c_l2_fW F z, by
    rw [one_smul, one_smul]
    exact k328r8c_l2_fW_rel F z⟩

private theorem k328r8c_l2_phi_omega (F : Type) [Field F] [CharP F 2]
    (z : GL (Fin 3 ⊕ Fin 3 ⊕ Fin 2) F) :
    k328r8c_l2_phi F z QuadraticAlgebra.omega = k328r8c_l2_fW F z := by
  simp [k328r8c_l2_phi, QuadraticAlgebra.lift]

private theorem k328r8c_l2_phi_algebraMap (F : Type) [Field F] [CharP F 2]
    (z : GL (Fin 3 ⊕ Fin 3 ⊕ Fin 2) F) (c : F) :
    k328r8c_l2_phi F z (algebraMap F (QuadraticAlgebra F 1 1) c) =
      c • (1 : k328r8c_l2_W F z →ₗ[F] k328r8c_l2_W F z) := by
  rw [AlgHom.commutes]
  exact Algebra.algebraMap_eq_smul_one c

private noncomputable instance k328r8c_l2_instModuleL (F : Type) [Field F] [CharP F 2]
    (z : GL (Fin 3 ⊕ Fin 3 ⊕ Fin 2) F) :
    Module (QuadraticAlgebra F 1 1) (k328r8c_l2_W F z) :=
  Module.compHom (k328r8c_l2_W F z) (k328r8c_l2_phi F z).toRingHom

private theorem k328r8c_l2_hphi (F : Type) [Field F] [CharP F 2]
    (z : GL (Fin 3 ⊕ Fin 3 ⊕ Fin 2) F) (l : QuadraticAlgebra F 1 1) :
    k328r8c_l2_phi F z l = l.re • (1 : k328r8c_l2_W F z →ₗ[F] k328r8c_l2_W F z) +
      l.im • k328r8c_l2_fW F z := by
  have hrepr : l = algebraMap F (QuadraticAlgebra F 1 1) l.re +
      l.im • QuadraticAlgebra.omega := by
    ext <;> simp [QuadraticAlgebra.omega]
  conv_lhs => rw [hrepr]
  rw [map_add, map_smul, k328r8c_l2_phi_algebraMap, k328r8c_l2_phi_omega]

private theorem k328r8c_l2_omega_smul (F : Type) [Field F] [CharP F 2]
    (z : GL (Fin 3 ⊕ Fin 3 ⊕ Fin 2) F) (w : k328r8c_l2_W F z) :
    (QuadraticAlgebra.omega : QuadraticAlgebra F 1 1) • w = k328r8c_l2_fW F z w := by
  change (k328r8c_l2_phi F z QuadraticAlgebra.omega) w = k328r8c_l2_fW F z w
  rw [k328r8c_l2_phi_omega]

private noncomputable def k328r8c_l2_xEnd (F : Type) [Field F]
    (x z : GL (Fin 3 ⊕ Fin 3 ⊕ Fin 2) F) (hxz : x * z = z * x) :
    k328r8c_l2_W F z →ₗ[F] k328r8c_l2_W F z :=
  k328r8c_l2_restrictSub (F := F) (W := k328r8c_l2_W F z) (f := k328r8c_l2_fOf F x) (by
    intro w hw
    rw [k328r8c_l2_W, LinearMap.mem_ker] at hw ⊢
    rw [← Module.End.mul_apply, k328r8c_l2_gz_comm F x z hxz, Module.End.mul_apply, hw, map_zero])

private theorem k328r8c_l2_xEnd_fW (F : Type) [Field F]
    (x z : GL (Fin 3 ⊕ Fin 3 ⊕ Fin 2) F) (hxz : x * z = z * x) :
    k328r8c_l2_xEnd F x z hxz * k328r8c_l2_fW F z =
      k328r8c_l2_fW F z * k328r8c_l2_xEnd F x z hxz := by
  apply LinearMap.ext
  intro w
  apply Subtype.ext
  change (k328r8c_l2_fOf F x) ((k328r8c_l2_fOf F z) (w : k328r8c_l2_V F)) =
    (k328r8c_l2_fOf F z) ((k328r8c_l2_fOf F x) (w : k328r8c_l2_V F))
  rw [← Module.End.mul_apply, k328r8c_l2_fOf_comm F x z hxz, Module.End.mul_apply]

private noncomputable def k328r8c_l2_xWmap (F : Type) [Field F] [CharP F 2]
    (x z : GL (Fin 3 ⊕ Fin 3 ⊕ Fin 2) F) (hxz : x * z = z * x) :
    k328r8c_l2_W F z →ₗ[QuadraticAlgebra F 1 1] k328r8c_l2_W F z where
  toFun := k328r8c_l2_xEnd F x z hxz
  map_add' a b := by
    apply Subtype.ext
    simp
  map_smul' l w := by
    change k328r8c_l2_xEnd F x z hxz ((k328r8c_l2_phi F z l) w) =
      (k328r8c_l2_phi F z l) (k328r8c_l2_xEnd F x z hxz w)
    rw [k328r8c_l2_hphi]
    simp only [LinearMap.add_apply, LinearMap.smul_apply, Module.End.one_apply]
    rw [map_add, map_smul, map_smul]
    congr 1
    have h := congrArg (fun g : k328r8c_l2_W F z →ₗ[F] k328r8c_l2_W F z => g w)
      (k328r8c_l2_xEnd_fW F x z hxz)
    simp only [Module.End.mul_apply] at h
    rw [h]

private theorem k328r8c_l2_fOf_one (F : Type) [Field F] :
    k328r8c_l2_fOf F (1 : GL (Fin 3 ⊕ Fin 3 ⊕ Fin 2) F) = 1 := by
  simp only [k328r8c_l2_fOf, map_one]
  rfl

private theorem k328r8c_l2_inv_comm (F : Type) [Field F]
    (x z : GL (Fin 3 ⊕ Fin 3 ⊕ Fin 2) F) (hxz : x * z = z * x) :
    x⁻¹ * z = z * x⁻¹ := by
  calc x⁻¹ * z = x⁻¹ * z * x * x⁻¹ := by group
    _ = x⁻¹ * (z * x) * x⁻¹ := by group
    _ = x⁻¹ * (x * z) * x⁻¹ := by rw [← hxz]
    _ = z * x⁻¹ := by group

private theorem k328r8c_l2_xWmap_mul_inv (F : Type) [Field F] [CharP F 2]
    (x z : GL (Fin 3 ⊕ Fin 3 ⊕ Fin 2) F) (hxz : x * z = z * x) :
    k328r8c_l2_xWmap F x z hxz * k328r8c_l2_xWmap F x⁻¹ z (k328r8c_l2_inv_comm F x z hxz) = 1 := by
  apply LinearMap.ext
  intro w
  apply Subtype.ext
  change (k328r8c_l2_fOf F x) ((k328r8c_l2_fOf F x⁻¹) (w : k328r8c_l2_V F)) = (w : k328r8c_l2_V F)
  rw [← Module.End.mul_apply, ← k328r8c_l2_fOf_mul, mul_inv_cancel, k328r8c_l2_fOf_one]
  rfl

private theorem k328r8c_l2_xWmap_inv_mul (F : Type) [Field F] [CharP F 2]
    (x z : GL (Fin 3 ⊕ Fin 3 ⊕ Fin 2) F) (hxz : x * z = z * x) :
    k328r8c_l2_xWmap F x⁻¹ z (k328r8c_l2_inv_comm F x z hxz) * k328r8c_l2_xWmap F x z hxz = 1 := by
  apply LinearMap.ext
  intro w
  apply Subtype.ext
  change (k328r8c_l2_fOf F x⁻¹) ((k328r8c_l2_fOf F x) (w : k328r8c_l2_V F)) = (w : k328r8c_l2_V F)
  rw [← Module.End.mul_apply, ← k328r8c_l2_fOf_mul, inv_mul_cancel, k328r8c_l2_fOf_one]
  rfl

private noncomputable def k328r8c_l2_xWunit (F : Type) [Field F] [CharP F 2]
    (x z : GL (Fin 3 ⊕ Fin 3 ⊕ Fin 2) F) (hxz : x * z = z * x) :
    (k328r8c_l2_W F z →ₗ[QuadraticAlgebra F 1 1] k328r8c_l2_W F z)ˣ where
  val := k328r8c_l2_xWmap F x z hxz
  inv := k328r8c_l2_xWmap F x⁻¹ z (k328r8c_l2_inv_comm F x z hxz)
  val_inv := k328r8c_l2_xWmap_mul_inv F x z hxz
  inv_val := k328r8c_l2_xWmap_inv_mul F x z hxz

private noncomputable def k328r8c_l2_resHom (F : Type) [Field F] [CharP F 2]
    (X : Subgroup (GL (Fin 3 ⊕ Fin 3 ⊕ Fin 2) F)) (z : GL (Fin 3 ⊕ Fin 3 ⊕ Fin 2) F)
    (hXc : X ≤ Subgroup.centralizer ({z} : Set (GL (Fin 3 ⊕ Fin 3 ⊕ Fin 2) F))) :
    X →* (k328r8c_l2_W F z →ₗ[QuadraticAlgebra F 1 1] k328r8c_l2_W F z)ˣ where
  toFun x := k328r8c_l2_xWunit F (x : GL (Fin 3 ⊕ Fin 3 ⊕ Fin 2) F) z
    (Subgroup.mem_centralizer_iff.mp (hXc x.2) z (Set.mem_singleton z)).symm
  map_one' := by
    apply Units.ext
    apply LinearMap.ext
    intro w
    apply Subtype.ext
    change (k328r8c_l2_fOf F (1 : GL (Fin 3 ⊕ Fin 3 ⊕ Fin 2) F)) (w : k328r8c_l2_V F) =
      (w : k328r8c_l2_V F)
    rw [k328r8c_l2_fOf_one]
    rfl
  map_mul' := by
    intro x y
    apply Units.ext
    apply LinearMap.ext
    intro w
    apply Subtype.ext
    change (k328r8c_l2_fOf F
        ((x : GL (Fin 3 ⊕ Fin 3 ⊕ Fin 2) F) * (y : GL (Fin 3 ⊕ Fin 3 ⊕ Fin 2) F)))
        (w : k328r8c_l2_V F) =
      (k328r8c_l2_fOf F (x : GL (Fin 3 ⊕ Fin 3 ⊕ Fin 2) F))
        ((k328r8c_l2_fOf F (y : GL (Fin 3 ⊕ Fin 3 ⊕ Fin 2) F)) (w : k328r8c_l2_V F))
    rw [k328r8c_l2_fOf_mul]
    rfl

private noncomputable def k328r8c_l2_detHom (F : Type) [Field F] [CharP F 2]
    (X : Subgroup (GL (Fin 3 ⊕ Fin 3 ⊕ Fin 2) F)) (z : GL (Fin 3 ⊕ Fin 3 ⊕ Fin 2) F)
    (hXc : X ≤ Subgroup.centralizer ({z} : Set (GL (Fin 3 ⊕ Fin 3 ⊕ Fin 2) F))) :
    X →* (QuadraticAlgebra F 1 1)ˣ :=
  (LinearEquiv.det).comp
    ((LinearMap.GeneralLinearGroup.generalLinearEquiv (QuadraticAlgebra F 1 1)
      (k328r8c_l2_W F z)).toMonoidHom.comp
      (k328r8c_l2_resHom F X z hXc))

private theorem k328r8c_l2_detHom_eq_one (F : Type) [Field F] [CharP F 2]
    (X : Subgroup (GL (Fin 3 ⊕ Fin 3 ⊕ Fin 2) F)) (z : GL (Fin 3 ⊕ Fin 3 ⊕ Fin 2) F)
    (hXc : X ≤ Subgroup.centralizer ({z} : Set (GL (Fin 3 ⊕ Fin 3 ⊕ Fin 2) F)))
    (hXperf : ⁅X, X⁆ = X) : k328r8c_l2_detHom F X z hXc = 1 := by
  have : Group.IsPerfect X := Subgroup.isPerfect_iff.mpr hXperf
  exact k328r8c_l2_perfect_hom_eq_one (k328r8c_l2_detHom F X z hXc)

private theorem k328r8c_l2_omega_sq_eq (F : Type) [Field F] :
    (QuadraticAlgebra.omega : QuadraticAlgebra F 1 1) ^ 2 =
      (1 : QuadraticAlgebra F 1 1) + QuadraticAlgebra.omega := by
  rw [pow_two, QuadraticAlgebra.omega_mul_omega_eq_add]
  simp

private theorem k328r8c_l2_omega_cube (F : Type) [Field F] [CharP F 2] :
    (QuadraticAlgebra.omega : QuadraticAlgebra F 1 1) ^ 3 = 1 := by
  have h2 : (QuadraticAlgebra.omega : QuadraticAlgebra F 1 1) ^ 2 =
      (1 : QuadraticAlgebra F 1 1) + QuadraticAlgebra.omega := k328r8c_l2_omega_sq_eq F
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

private theorem k328r8c_l2_omega_ne_one (F : Type) [Field F] :
    (QuadraticAlgebra.omega : QuadraticAlgebra F 1 1) ≠ 1 := by
  intro h
  have this := congrArg QuadraticAlgebra.im h
  have h1 : QuadraticAlgebra.im (QuadraticAlgebra.omega : QuadraticAlgebra F 1 1) = 1 := rfl
  have h0 : QuadraticAlgebra.im (1 : QuadraticAlgebra F 1 1) = 0 := rfl
  have hthis : (1 : F) = 0 := by rw [h1, h0] at this; exact this
  exact one_ne_zero hthis

private theorem k328r8c_l2_xWmap_self (F : Type) [Field F] [CharP F 2]
    (z : GL (Fin 3 ⊕ Fin 3 ⊕ Fin 2) F) :
    (k328r8c_l2_xWmap F z z rfl :
        k328r8c_l2_W F z →ₗ[QuadraticAlgebra F 1 1] k328r8c_l2_W F z) =
      (QuadraticAlgebra.omega : QuadraticAlgebra F 1 1) •
        (LinearMap.id : k328r8c_l2_W F z →ₗ[QuadraticAlgebra F 1 1] k328r8c_l2_W F z) := by
  apply LinearMap.ext
  intro w
  show k328r8c_l2_xWmap F z z rfl w =
    (QuadraticAlgebra.omega : QuadraticAlgebra F 1 1) • (w : k328r8c_l2_W F z)
  rw [k328r8c_l2_omega_smul]
  rfl

private theorem k328r8c_l2_omega_pow_finrank_eq_one (F : Type) [Field F] [Fintype F]
    [CharP F 2] (hF : Fintype.card F = 8)
    (X : Subgroup (GL (Fin 3 ⊕ Fin 3 ⊕ Fin 2) F)) (z : GL (Fin 3 ⊕ Fin 3 ⊕ Fin 2) F)
    (hXc : X ≤ Subgroup.centralizer ({z} : Set (GL (Fin 3 ⊕ Fin 3 ⊕ Fin 2) F)))
    (hXperf : ⁅X, X⁆ = X) (hzX : z ∈ X) :
    (QuadraticAlgebra.omega : QuadraticAlgebra F 1 1) ^
      Module.finrank (QuadraticAlgebra F 1 1) (k328r8c_l2_W F z) = 1 := by
  have : Fact (∀ r : F, r ^ 2 ≠ 1 + 1 * r) := k328r8c_l2_fact F hF
  let : Field (QuadraticAlgebra F 1 1) := inferInstance
  have hdet1 : k328r8c_l2_detHom F X z hXc ⟨z, hzX⟩ = 1 := by
    rw [k328r8c_l2_detHom_eq_one F X z hXc hXperf]
    rfl
  have hz1 : ((k328r8c_l2_detHom F X z hXc ⟨z, hzX⟩ : (QuadraticAlgebra F 1 1)ˣ) :
      QuadraticAlgebra F 1 1) = 1 := by rw [hdet1]; rfl
  have hval : ((k328r8c_l2_detHom F X z hXc ⟨z, hzX⟩ : (QuadraticAlgebra F 1 1)ˣ) :
      QuadraticAlgebra F 1 1) = LinearMap.det (k328r8c_l2_xWmap F z z rfl) := by
    simp only [k328r8c_l2_detHom, MonoidHom.comp_apply, LinearEquiv.coe_det]
    change LinearMap.det (↑((k328r8c_l2_resHom F X z hXc) ⟨z, hzX⟩) :
      k328r8c_l2_W F z →ₗ[QuadraticAlgebra F 1 1] k328r8c_l2_W F z) =
      LinearMap.det (k328r8c_l2_xWmap F z z rfl)
    congr 1
  rw [hval] at hz1
  have hsmul : LinearMap.det ((QuadraticAlgebra.omega : QuadraticAlgebra F 1 1) •
      (LinearMap.id : k328r8c_l2_W F z →ₗ[QuadraticAlgebra F 1 1] k328r8c_l2_W F z)) =
      (QuadraticAlgebra.omega : QuadraticAlgebra F 1 1) ^
        Module.finrank (QuadraticAlgebra F 1 1) (k328r8c_l2_W F z) := by
    rw [LinearMap.det_smul, LinearMap.det_id, mul_one]
  rw [k328r8c_l2_xWmap_self F z, hsmul] at hz1
  exact hz1

private theorem k328r8c_l2_three_dvd_finrank (F : Type) [Field F] [Fintype F] [CharP F 2]
    (hF : Fintype.card F = 8)
    (X : Subgroup (GL (Fin 3 ⊕ Fin 3 ⊕ Fin 2) F)) (z : GL (Fin 3 ⊕ Fin 3 ⊕ Fin 2) F)
    (hXc : X ≤ Subgroup.centralizer ({z} : Set (GL (Fin 3 ⊕ Fin 3 ⊕ Fin 2) F)))
    (hXperf : ⁅X, X⁆ = X) (hzX : z ∈ X) :
    3 ∣ Module.finrank (QuadraticAlgebra F 1 1) (k328r8c_l2_W F z) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hord : orderOf (QuadraticAlgebra.omega : QuadraticAlgebra F 1 1) = 3 :=
    orderOf_eq_prime (k328r8c_l2_omega_cube F) (k328r8c_l2_omega_ne_one F)
  have h := orderOf_dvd_iff_pow_eq_one.mpr
    (k328r8c_l2_omega_pow_finrank_eq_one F hF X z hXc hXperf hzX)
  rwa [hord] at h

private theorem k328r8c_l2_scalarTower (F : Type) [Field F] [CharP F 2]
    (z : GL (Fin 3 ⊕ Fin 3 ⊕ Fin 2) F) :
    IsScalarTower F (QuadraticAlgebra F 1 1) (k328r8c_l2_W F z) := by
  refine ⟨fun c l w => ?_⟩
  change (k328r8c_l2_phi F z (c • l)) w = c • (k328r8c_l2_phi F z l w)
  have hcl : k328r8c_l2_phi F z (c • l) = c • k328r8c_l2_phi F z l := by
    rw [show c • l = algebraMap F (QuadraticAlgebra F 1 1) c * l from Algebra.smul_def c l]
    rw [map_mul, k328r8c_l2_phi_algebraMap]
    rfl
  rw [hcl]
  rfl

private theorem k328r8c_l2_finrank_eq (F : Type) [Field F] [Fintype F] [CharP F 2]
    (hF : Fintype.card F = 8) (z : GL (Fin 3 ⊕ Fin 3 ⊕ Fin 2) F) :
    Module.finrank F (k328r8c_l2_W F z) =
      2 * Module.finrank (QuadraticAlgebra F 1 1) (k328r8c_l2_W F z) := by
  have : Fact (∀ r : F, r ^ 2 ≠ 1 + 1 * r) := k328r8c_l2_fact F hF
  let : Field (QuadraticAlgebra F 1 1) := inferInstance
  have := k328r8c_l2_scalarTower F z
  rw [← Module.finrank_mul_finrank F (QuadraticAlgebra F 1 1) (k328r8c_l2_W F z),
    QuadraticAlgebra.finrank_eq_two]

private theorem k328r8c_l2_finrank_le_eight (F : Type) [Field F] [CharP F 2]
    (z : GL (Fin 3 ⊕ Fin 3 ⊕ Fin 2) F) :
    Module.finrank F (k328r8c_l2_W F z) ≤ 8 := by
  have h := Submodule.finrank_le (k328r8c_l2_W F z)
  have hV : Module.finrank F (k328r8c_l2_V F) = 8 := by
    change Module.finrank F (Fin 3 ⊕ Fin 3 ⊕ Fin 2 → F) = 8
    rw [Module.finrank_fintype_fun_eq_card]
    simp [Fintype.card_sum, Fintype.card_fin]
  rwa [hV] at h

private theorem k328r8c_l2_fOf_injective (F : Type) [Field F] :
    Function.Injective (k328r8c_l2_fOf F) := by
  intro a b h
  exact Matrix.GeneralLinearGroup.toLin.injective (Units.ext (by simpa [k328r8c_l2_fOf] using h))

private theorem k328r8c_l2_fOf_pow (F : Type) [Field F]
    (z : GL (Fin 3 ⊕ Fin 3 ⊕ Fin 2) F) (n : ℕ) :
    k328r8c_l2_fOf F (z ^ n) = (k328r8c_l2_fOf F z) ^ n := by
  simp only [k328r8c_l2_fOf]
  rw [map_pow, Units.val_pow_eq_pow_val]

private theorem k328r8c_l2_W_ne_bot (F : Type) [Field F] [Fintype F] [CharP F 2]
    (z : GL (Fin 3 ⊕ Fin 3 ⊕ Fin 2) F) (hzord : orderOf z = 3) : k328r8c_l2_W F z ≠ ⊥ := by
  intro hbot
  have hz3 : z ^ 3 = 1 := by simpa [hzord] using pow_orderOf_eq_one z
  have hf3 : (k328r8c_l2_fOf F z) ^ 3 = 1 := by
    rw [← k328r8c_l2_fOf_pow, hz3, k328r8c_l2_fOf_one]
  let g : Module.End F (k328r8c_l2_V F) := (k328r8c_l2_fOf F z) ^ 2 + k328r8c_l2_fOf F z + 1
  have hgker : LinearMap.ker g = ⊥ := by
    change LinearMap.ker ((k328r8c_l2_fOf F z) ^ 2 + k328r8c_l2_fOf F z + 1) = ⊥
    rw [← hbot]
    rfl
  have hpoly : ((k328r8c_l2_fOf F z) - 1) * g = 0 := by
    have h1 : ((k328r8c_l2_fOf F z) - 1) * g = (k328r8c_l2_fOf F z) ^ 3 - 1 := by
      dsimp only [g]
      rw [sub_mul, one_mul]
      have hmul : (k328r8c_l2_fOf F z) * ((k328r8c_l2_fOf F z) ^ 2 + k328r8c_l2_fOf F z + 1) =
          (k328r8c_l2_fOf F z) ^ 3 + (k328r8c_l2_fOf F z) ^ 2 + k328r8c_l2_fOf F z := by
        calc (k328r8c_l2_fOf F z) * ((k328r8c_l2_fOf F z) ^ 2 + k328r8c_l2_fOf F z + 1)
            = (k328r8c_l2_fOf F z) * (k328r8c_l2_fOf F z) ^ 2 +
              (k328r8c_l2_fOf F z) * (k328r8c_l2_fOf F z) + k328r8c_l2_fOf F z := by
              rw [mul_add, mul_add, mul_one]
          _ = (k328r8c_l2_fOf F z) ^ 3 + (k328r8c_l2_fOf F z) ^ 2 + k328r8c_l2_fOf F z := by
              rw [show (k328r8c_l2_fOf F z) * (k328r8c_l2_fOf F z) ^ 2 = (k328r8c_l2_fOf F z) ^ 3
                    from (pow_succ' (k328r8c_l2_fOf F z) 2).symm,
                  show (k328r8c_l2_fOf F z) * (k328r8c_l2_fOf F z) = (k328r8c_l2_fOf F z) ^ 2
                    from (pow_two (k328r8c_l2_fOf F z)).symm]
      rw [hmul]
      abel
    rw [h1, hf3, sub_self]
  have hinj : Function.Injective g := by
    rw [← LinearMap.ker_eq_bot]
    exact hgker
  have hsurj : Function.Surjective g := by
    have : Finite (k328r8c_l2_V F) := inferInstance
    exact Finite.injective_iff_surjective.mp hinj
  have hfeq : k328r8c_l2_fOf F z = 1 := by
    apply LinearMap.ext
    intro w
    obtain ⟨v, rfl⟩ := hsurj w
    have h0 : ((k328r8c_l2_fOf F z) - 1) (g v) = 0 := by
      rw [← Module.End.mul_apply, hpoly, LinearMap.zero_apply]
    have h0' : (k328r8c_l2_fOf F z) (g v) - g v = 0 := by
      simpa only [LinearMap.sub_apply, Module.End.one_apply, LinearMap.zero_apply] using h0
    exact sub_eq_zero.mp h0'
  have hz1 : z = 1 := k328r8c_l2_fOf_injective F (by rw [hfeq, k328r8c_l2_fOf_one])
  rw [hz1, orderOf_one] at hzord
  norm_num at hzord

end K328R8L2

private theorem k328r8c_z0_isom
    {F : Type} [Field F] [Fintype F] [DecidableEq F]
    (hF : Fintype.card F = 8) (b c : F)
    (hbc : ∀ s : F, s ^ 2 + b * s + c ≠ 0) (α : F) (hα : α ^ 2 + α = 1 + c / b ^ 2)
    (z₀ : GL (Fin 3 ⊕ Fin 3 ⊕ Fin 2) F)
    (hz₀ : (z₀ : Matrix _ _ F) = ofColumns F
      (Sum.elim ![bv F (Sum.inl 0) + bv F (Sum.inr (Sum.inl 1)),
                  bv F (Sum.inr (Sum.inl 0)) + bv F (Sum.inl 1), bv F (Sum.inl 2)]
        (Sum.elim ![bv F (Sum.inl 1), bv F (Sum.inl 0), bv F (Sum.inr (Sum.inl 2))]
          ![α • bv F (Sum.inr (Sum.inr 0)) + b⁻¹ • bv F (Sum.inr (Sum.inr 1)),
            (c / b) • bv F (Sum.inr (Sum.inr 0)) + (α + 1) • bv F (Sum.inr (Sum.inr 1))]))) :
    toLinEquiv _ _ z₀ ∈ orthogonalGroup (quadMinus 4 F b c) := by
  have : CharP F 2 :=
    charP_of_card_eq_prime_pow (show Fintype.card F = 2 ^ 3 by rw [hF]; norm_num)
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  have hb : b ≠ 0 := by
    intro hb0
    obtain ⟨s, hs⟩ := FiniteField.isSquare_of_char_two (ringChar.eq F 2) c
    refine hbc s ?_
    rw [hb0, zero_mul, add_zero, hs]
    linear_combination (s ^ 2) * h2
  have hαsub : α ^ 2 = 1 + c / b ^ 2 + α := by
    linear_combination hα - α * h2
  rw [TauCeti.QuadraticMap.mem_orthogonalGroup_iff]
  intro v
  rw [toLinEquiv_apply, hz₀]
  rw [quadMinus_apply, quadMinus_apply]
  simp only [ofColumns, Matrix.of_apply, Matrix.mulVec, dotProduct, bv,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons, Pi.single_apply, Pi.add_apply, Pi.smul_apply,
    smul_eq_mul, Sum.elim_inl, Sum.elim_inr, Fintype.sum_sum_type, Fin.sum_univ_three,
    Fin.sum_univ_two, Fin.isValue, reduceIte, Fin.reduceEq, Nat.reduceSub,
    Sum.inl.injEq, Sum.inr.injEq, Sum.inl_ne_inr, Sum.inr_ne_inl, div_eq_mul_inv]
  field_simp
  ring_nf
  rw [hαsub]
  field_simp
  ring_nf
  have h3 : (3 : F) = 1 := by linear_combination h2
  have h4 : (4 : F) = 0 := by linear_combination 2 * h2
  simp only [h2, h3, h4, mul_zero, mul_one]
  ring_nf

private theorem k328r8c_isCompl_fix_move {F : Type} [Field F] {V : Type} [AddCommGroup V]
    [Module F V] [CharP F 2] {Z : Module.End F V} (hZ3 : Z ^ 3 = 1) :
    IsCompl (LinearMap.ker (Z - 1)) (LinearMap.ker (Z ^ 2 + Z + 1)) := by
  have hcop : IsCoprime (X - 1 : F[X]) (X ^ 2 + X + 1) := by
    refine ⟨-X, 1, ?_⟩
    have h2 : (2 : F[X]) = 0 := CharTwo.two_eq_zero
    linear_combination (X : F[X]) * h2
  refine ⟨?_, ?_⟩
  · simpa only [map_sub, map_pow, aeval_X, map_one, map_add] using
      Polynomial.disjoint_ker_aeval_of_isCoprime Z hcop
  · rw [codisjoint_iff]
    have h := Polynomial.sup_ker_aeval_eq_ker_aeval_mul_of_coprime Z hcop
    simp only [map_sub, map_pow, aeval_X, map_one, map_add] at h
    rw [h]
    have hpq : (X - 1 : F[X]) * (X ^ 2 + X + 1) = X ^ 3 - 1 := by ring
    rw [hpq]
    simp [hZ3]

private theorem k328r8c_finrank_fix_eq_two
    {F : Type} [Field F] [Fintype F]
    (hF : Fintype.card F = 8) (b c : F)
    (_hbc : ∀ s : F, s ^ 2 + b * s + c ≠ 0) (α : F) (_hα : α ^ 2 + α = 1 + c / b ^ 2)
    {z : GL (Fin 3 ⊕ Fin 3 ⊕ Fin 2) F} (hz3 : orderOf z = 3)
    {X : Subgroup (GL (Fin 3 ⊕ Fin 3 ⊕ Fin 2) F)} (hzX : z ∈ X)
    (hXC : X ≤ Subgroup.centralizer {z}) (hperf : ⁅X, X⁆ = X) :
    Module.finrank F (LinearMap.ker (K328R8L2.k328r8c_l2_fOf F z - 1)) = 2 := by
  have : CharP F 2 :=
    charP_of_card_eq_prime_pow (show Fintype.card F = 2 ^ 3 by rw [hF]; norm_num)
  have : Fact (∀ r : F, r ^ 2 ≠ 1 + 1 * r) := K328R8L2.k328r8c_l2_fact F hF
  let : Field (QuadraticAlgebra F 1 1) := inferInstance
  have hz3' : z ^ 3 = 1 := by simpa [hz3] using pow_orderOf_eq_one z
  have hZ3 : (K328R8L2.k328r8c_l2_fOf F z) ^ 3 = 1 := by
    rw [← K328R8L2.k328r8c_l2_fOf_pow, hz3', K328R8L2.k328r8c_l2_fOf_one]
  have hcompl := k328r8c_isCompl_fix_move (V := Fin 3 ⊕ Fin 3 ⊕ Fin 2 → F)
    (Z := K328R8L2.k328r8c_l2_fOf F z) hZ3
  have hdvd := K328R8L2.k328r8c_l2_three_dvd_finrank F hF X z hXC hperf hzX
  have hfr := K328R8L2.k328r8c_l2_finrank_eq F hF z
  have hle := K328R8L2.k328r8c_l2_finrank_le_eight (z := z)
  have hne := K328R8L2.k328r8c_l2_W_ne_bot F z hz3
  have hdpos : 0 < Module.finrank (QuadraticAlgebra F 1 1) (K328R8L2.k328r8c_l2_W F z) := by
    by_contra h
    have h0 : Module.finrank (QuadraticAlgebra F 1 1) (K328R8L2.k328r8c_l2_W F z) = 0 := by
      omega
    have hf0 : Module.finrank F (K328R8L2.k328r8c_l2_W F z) = 0 := by rw [hfr, h0, mul_zero]
    have : Subsingleton (K328R8L2.k328r8c_l2_W F z) := Module.finrank_zero_iff.mp hf0
    exact hne (Submodule.subsingleton_iff_eq_bot.mp inferInstance)
  have hdle : Module.finrank (QuadraticAlgebra F 1 1) (K328R8L2.k328r8c_l2_W F z) ≤ 4 := by
    have := hfr ▸ hle
    omega
  have hd3 : Module.finrank (QuadraticAlgebra F 1 1) (K328R8L2.k328r8c_l2_W F z) = 3 := by
    obtain ⟨k, hk⟩ := hdvd
    omega
  have hW6 : Module.finrank F (LinearMap.ker (K328R8L2.k328r8c_l2_fOf F z ^ 2 +
      K328R8L2.k328r8c_l2_fOf F z + 1)) = 6 := by
    change Module.finrank F (K328R8L2.k328r8c_l2_W F z) = 6
    rw [hfr, hd3]
  have hV : Module.finrank F (Fin 3 ⊕ Fin 3 ⊕ Fin 2 → F) = 8 := by
    rw [Module.finrank_fintype_fun_eq_card]
    simp [Fintype.card_sum, Fintype.card_fin]
  have hsum : Module.finrank F (LinearMap.ker (K328R8L2.k328r8c_l2_fOf F z - 1)) +
      Module.finrank F (LinearMap.ker (K328R8L2.k328r8c_l2_fOf F z ^ 2 +
        K328R8L2.k328r8c_l2_fOf F z + 1)) = 8 := by
    have h := Submodule.finrank_add_eq_of_isCompl hcompl
    rwa [hV] at h
  rw [hW6] at hsum
  omega

private theorem k328r8c_dickson {K V : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] [CharP K 2] {Q : QuadraticForm K V}
    (hQ : (polarBilin Q).Nondegenerate)
    (hT : ∃ T : Submodule K V, finrank K T = 3 ∧ ∀ x ∈ T, Q x = 0)
    {g : V ≃ₗ[K] V} (hg : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q) {a : V} (ha : Q a ≠ 0) :
    g ∈ CFSG.RankThree.Classical2.orthDerived Q ∨
      g * CFSG.ClassicalGroups.Orthogonal.reflect Q a ∈
        CFSG.RankThree.Classical2.orthDerived Q := by
  let _ : Invertible (Q a) := invertibleOfNonzero ha
  have hr := TauCeti.QuadraticMap.reflection_mem_orthogonalGroup Q a
  have hmul := CFSG.RankThree.OrthogonalInvolutions.natCast_finrank_commSpace_mul hQ hg hr
  rw [CFSG.RankThree.OrthogonalInvolutions.finrank_commSpace_reflection hQ a, Nat.cast_one] at hmul
  rw [CFSG.ClassicalGroups.Orthogonal.reflect_eq_reflection]
  have hΩ := CFSG.RankThree.PartOne.FieldFix.omegaGroup_le_orthDerived hQ hT
  by_cases hev : Even (finrank K (CFSG.RankThree.OrthogonalInvolutions.commSpace g))
  · exact Or.inl (hΩ ⟨hg, hev⟩)
  · refine Or.inr (hΩ ⟨mul_mem hg hr, ?_⟩)
    rw [← ZMod.natCast_eq_zero_iff_even, hmul, ← Nat.cast_one, ← Nat.cast_add,
      ZMod.natCast_eq_zero_iff_even, Nat.even_add_one]
    exact hev

private theorem k328r8c_l2_fW_sq {F : Type} [Field F] [CharP F 2]
    (z : GL (Fin 3 ⊕ Fin 3 ⊕ Fin 2) F) (x : K328R8L2.k328r8c_l2_W F z) :
    K328R8L2.k328r8c_l2_fW F z (K328R8L2.k328r8c_l2_fW F z x) =
      x + K328R8L2.k328r8c_l2_fW F z x := by
  have h := DFunLike.congr_fun (K328R8L2.k328r8c_l2_fW_rel F z) x
  simpa only [Module.End.mul_apply, LinearMap.add_apply, Module.End.one_apply] using h

private theorem k328r8c_l2_fW_coe {F : Type} [Field F] [CharP F 2]
    (z : GL (Fin 3 ⊕ Fin 3 ⊕ Fin 2) F) (w : K328R8L2.k328r8c_l2_W F z) :
    ((K328R8L2.k328r8c_l2_fW F z w : K328R8L2.k328r8c_l2_W F z) :
      Fin 3 ⊕ Fin 3 ⊕ Fin 2 → F) = toLinEquiv _ _ z (w : Fin 3 ⊕ Fin 3 ⊕ Fin 2 → F) := by
  rfl

private theorem k328r8c_mem_orth {F : Type} [Field F] (b c : F)
    {g : GL (Fin 3 ⊕ Fin 3 ⊕ Fin 2) F}
    (hg : g ∈ StatedOmega (StatedQuadMinus 4 F b c)) :
    toLinEquiv (Fin 3 ⊕ Fin 3 ⊕ Fin 2) F g ∈ orthogonalGroup (quadMinus 4 F b c) := by
  rw [statedOmega_eq_comap (coe_quadMinus 4 F b c), Subgroup.mem_comap] at hg
  refine (Subgroup.commutator_le.2 fun x hx y hy => ?_) hg
  rw [commutatorElement_def]
  exact mul_mem (mul_mem (mul_mem hx hy) (inv_mem hx)) (inv_mem hy)

private theorem k328r8c_l2_polar_fW_fW {F : Type} [Field F] [CharP F 2] (b c : F)
    (z : GL (Fin 3 ⊕ Fin 3 ⊕ Fin 2) F)
    (hz : toLinEquiv (Fin 3 ⊕ Fin 3 ⊕ Fin 2) F z ∈ orthogonalGroup (quadMinus 4 F b c))
    (x y : K328R8L2.k328r8c_l2_W F z) :
    polar (quadMinus 4 F b c)
        ((K328R8L2.k328r8c_l2_fW F z x : K328R8L2.k328r8c_l2_W F z) :
          Fin 3 ⊕ Fin 3 ⊕ Fin 2 → F)
        ((K328R8L2.k328r8c_l2_fW F z y : K328R8L2.k328r8c_l2_W F z) :
          Fin 3 ⊕ Fin 3 ⊕ Fin 2 → F) =
      polar (quadMinus 4 F b c) (x : Fin 3 ⊕ Fin 3 ⊕ Fin 2 → F)
        (y : Fin 3 ⊕ Fin 3 ⊕ Fin 2 → F) := by
  change polar (quadMinus 4 F b c)
      (toLinEquiv (Fin 3 ⊕ Fin 3 ⊕ Fin 2) F z (x : Fin 3 ⊕ Fin 3 ⊕ Fin 2 → F))
      (toLinEquiv (Fin 3 ⊕ Fin 3 ⊕ Fin 2) F z (y : Fin 3 ⊕ Fin 3 ⊕ Fin 2 → F)) =
    polar (quadMinus 4 F b c) (x : Fin 3 ⊕ Fin 3 ⊕ Fin 2 → F)
      (y : Fin 3 ⊕ Fin 3 ⊕ Fin 2 → F)
  exact polar_map_of_mem hz (x : Fin 3 ⊕ Fin 3 ⊕ Fin 2 → F)
    (y : Fin 3 ⊕ Fin 3 ⊕ Fin 2 → F)

private theorem k328r8c_polar_fix_W {F : Type} [Field F] [CharP F 2] (b c : F)
    (z : GL (Fin 3 ⊕ Fin 3 ⊕ Fin 2) F)
    (hz : toLinEquiv (Fin 3 ⊕ Fin 3 ⊕ Fin 2) F z ∈ orthogonalGroup (quadMinus 4 F b c))
    {cc : Fin 3 ⊕ Fin 3 ⊕ Fin 2 → F}
    (hc : cc ∈ LinearMap.ker (K328R8L2.k328r8c_l2_fOf F z - 1))
    {m : K328R8L2.k328r8c_l2_W F z} :
    polar (quadMinus 4 F b c) cc (m : Fin 3 ⊕ Fin 3 ⊕ Fin 2 → F) = 0 := by
  have hc1 : K328R8L2.k328r8c_l2_fOf F z cc = cc := by
    have := sub_eq_zero.mp (show (K328R8L2.k328r8c_l2_fOf F z - 1) cc = 0 from hc)
    simpa using this
  have hm : K328R8L2.k328r8c_l2_fOf F z (K328R8L2.k328r8c_l2_fOf F z
      (m : Fin 3 ⊕ Fin 3 ⊕ Fin 2 → F)) + K328R8L2.k328r8c_l2_fOf F z
        (m : Fin 3 ⊕ Fin 3 ⊕ Fin 2 → F) + (m : Fin 3 ⊕ Fin 3 ⊕ Fin 2 → F) = 0 := by
    have h := m.2
    change (m : Fin 3 ⊕ Fin 3 ⊕ Fin 2 → F) ∈ LinearMap.ker
      (K328R8L2.k328r8c_l2_fOf F z ^ 2 + K328R8L2.k328r8c_l2_fOf F z + 1) at h
    rw [LinearMap.mem_ker] at h
    simpa only [pow_two, Module.End.mul_apply, LinearMap.add_apply,
      Module.End.one_apply] using h
  have hm' : (m : Fin 3 ⊕ Fin 3 ⊕ Fin 2 → F) =
      (K328R8L2.k328r8c_l2_fOf F z - 1)
        (K328R8L2.k328r8c_l2_fOf F z (m : Fin 3 ⊕ Fin 3 ⊕ Fin 2 → F)) := by
    rw [LinearMap.sub_apply, Module.End.one_apply, sub_eq_add_neg, CharTwo.neg_eq]
    have h2 : (K328R8L2.k328r8c_l2_fOf F z (K328R8L2.k328r8c_l2_fOf F z
        (m : Fin 3 ⊕ Fin 3 ⊕ Fin 2 → F)) + K328R8L2.k328r8c_l2_fOf F z
          (m : Fin 3 ⊕ Fin 3 ⊕ Fin 2 → F)) + (m : Fin 3 ⊕ Fin 3 ⊕ Fin 2 → F) = 0 := hm
    exact ((eq_neg_of_add_eq_zero_left h2).trans (CharTwo.neg_eq _)).symm
  have hzB : ∀ x y : Fin 3 ⊕ Fin 3 ⊕ Fin 2 → F,
      polar (quadMinus 4 F b c) (K328R8L2.k328r8c_l2_fOf F z x)
        (K328R8L2.k328r8c_l2_fOf F z y) = polar (quadMinus 4 F b c) x y := by
    intro x y
    change polar (quadMinus 4 F b c)
        (toLinEquiv (Fin 3 ⊕ Fin 3 ⊕ Fin 2) F z x)
        (toLinEquiv (Fin 3 ⊕ Fin 3 ⊕ Fin 2) F z y) = polar (quadMinus 4 F b c) x y
    exact polar_map_of_mem hz x y
  rw [hm']
  have hkey : polar (quadMinus 4 F b c) cc
      (K328R8L2.k328r8c_l2_fOf F z (K328R8L2.k328r8c_l2_fOf F z
        (m : Fin 3 ⊕ Fin 3 ⊕ Fin 2 → F))) =
      polar (quadMinus 4 F b c) cc
        (K328R8L2.k328r8c_l2_fOf F z (m : Fin 3 ⊕ Fin 3 ⊕ Fin 2 → F)) := by
    nth_rewrite 1 [← hc1]
    exact hzB cc (K328R8L2.k328r8c_l2_fOf F z (m : Fin 3 ⊕ Fin 3 ⊕ Fin 2 → F))
  rw [LinearMap.sub_apply, Module.End.one_apply, polar_sub_right, hkey, sub_self]

private theorem k328r8c_polarNondegOn_W {F : Type} [Field F] [Fintype F] [CharP F 2] (b c : F)
    (hbc : ∀ s : F, s ^ 2 + b * s + c ≠ 0)
    (z : GL (Fin 3 ⊕ Fin 3 ⊕ Fin 2) F)
    (hz : toLinEquiv (Fin 3 ⊕ Fin 3 ⊕ Fin 2) F z ∈ orthogonalGroup (quadMinus 4 F b c))
    (hz3 : z ^ 3 = 1) :
    PolarNondegOn (quadMinus 4 F b c) (K328R8L2.k328r8c_l2_W F z) := by
  have hnd := nondegenerate_polarBilin_quadMinus_of_finite (n := 4) F hbc
  have hZ3 : (K328R8L2.k328r8c_l2_fOf F z) ^ 3 = 1 := by
    have h := K328R8L2.k328r8c_l2_fOf_pow F z 3
    rw [hz3, K328R8L2.k328r8c_l2_fOf_one] at h
    exact h.symm
  have hcompl := k328r8c_isCompl_fix_move (V := Fin 3 ⊕ Fin 3 ⊕ Fin 2 → F)
    (Z := K328R8L2.k328r8c_l2_fOf F z) hZ3
  intro w hw hwperp
  apply hnd.1 w
  intro v
  have hv : v ∈ LinearMap.ker (K328R8L2.k328r8c_l2_fOf F z - 1) ⊔
      K328R8L2.k328r8c_l2_W F z := by
    change v ∈ LinearMap.ker (K328R8L2.k328r8c_l2_fOf F z - 1) ⊔
      LinearMap.ker (K328R8L2.k328r8c_l2_fOf F z ^ 2 + K328R8L2.k328r8c_l2_fOf F z + 1)
    rw [hcompl.sup_eq_top]
    exact Submodule.mem_top
  obtain ⟨cc, hc, m, hm, rfl⟩ := Submodule.mem_sup.1 hv
  change polar (quadMinus 4 F b c) w (cc + m) = 0
  have h1 : polar (quadMinus 4 F b c) w cc = 0 := by
    rw [polar_comm]
    exact k328r8c_polar_fix_W b c z hz hc (m := ⟨w, hw⟩)
  have h2 : polar (quadMinus 4 F b c) w m = 0 := hwperp m hm
  rw [polar_add_right, h1, h2, add_zero]

private theorem k328r8c_Q_eq_polar {F : Type} [Field F] [CharP F 2] (b c : F)
    (z : GL (Fin 3 ⊕ Fin 3 ⊕ Fin 2) F)
    (hz : toLinEquiv (Fin 3 ⊕ Fin 3 ⊕ Fin 2) F z ∈ orthogonalGroup (quadMinus 4 F b c))
    (w : K328R8L2.k328r8c_l2_W F z) :
    quadMinus 4 F b c (w : Fin 3 ⊕ Fin 3 ⊕ Fin 2 → F) =
      polar (quadMinus 4 F b c) (w : Fin 3 ⊕ Fin 3 ⊕ Fin 2 → F)
        ((K328R8L2.k328r8c_l2_fW F z w : K328R8L2.k328r8c_l2_W F z) :
          Fin 3 ⊕ Fin 3 ⊕ Fin 2 → F) := by
  have hz2 : ((K328R8L2.k328r8c_l2_fW F z (K328R8L2.k328r8c_l2_fW F z w) :
        K328R8L2.k328r8c_l2_W F z) : Fin 3 ⊕ Fin 3 ⊕ Fin 2 → F) =
      (w : Fin 3 ⊕ Fin 3 ⊕ Fin 2 → F) +
        ((K328R8L2.k328r8c_l2_fW F z w : K328R8L2.k328r8c_l2_W F z) :
          Fin 3 ⊕ Fin 3 ⊕ Fin 2 → F) := by
    rw [← Submodule.coe_add, ← k328r8c_l2_fW_sq (z := z) w]
  have h1 : ((K328R8L2.k328r8c_l2_fW F z w : K328R8L2.k328r8c_l2_W F z) :
        Fin 3 ⊕ Fin 3 ⊕ Fin 2 → F) =
      toLinEquiv (Fin 3 ⊕ Fin 3 ⊕ Fin 2) F z (w : Fin 3 ⊕ Fin 3 ⊕ Fin 2 → F) :=
    k328r8c_l2_fW_coe z w
  have h2 : ((K328R8L2.k328r8c_l2_fW F z (K328R8L2.k328r8c_l2_fW F z w) :
        K328R8L2.k328r8c_l2_W F z) : Fin 3 ⊕ Fin 3 ⊕ Fin 2 → F) =
      toLinEquiv (Fin 3 ⊕ Fin 3 ⊕ Fin 2) F z
        ((K328R8L2.k328r8c_l2_fW F z w : K328R8L2.k328r8c_l2_W F z) :
          Fin 3 ⊕ Fin 3 ⊕ Fin 2 → F) :=
    k328r8c_l2_fW_coe z (K328R8L2.k328r8c_l2_fW F z w)
  have hQ : quadMinus 4 F b c (w : Fin 3 ⊕ Fin 3 ⊕ Fin 2 → F) =
      quadMinus 4 F b c ((w : Fin 3 ⊕ Fin 3 ⊕ Fin 2 → F) +
        ((K328R8L2.k328r8c_l2_fW F z w : K328R8L2.k328r8c_l2_W F z) :
          Fin 3 ⊕ Fin 3 ⊕ Fin 2 → F)) := by
    rw [← hz2, h2, h1]
    exact (((map_of_mem hz
      ((K328R8L2.k328r8c_l2_fW F z w : K328R8L2.k328r8c_l2_W F z) :
        Fin 3 ⊕ Fin 3 ⊕ Fin 2 → F)).trans
      (map_of_mem hz (w : Fin 3 ⊕ Fin 3 ⊕ Fin 2 → F)))).symm
  have hpolar : polar (quadMinus 4 F b c) (w : Fin 3 ⊕ Fin 3 ⊕ Fin 2 → F)
      ((K328R8L2.k328r8c_l2_fW F z w : K328R8L2.k328r8c_l2_W F z) :
        Fin 3 ⊕ Fin 3 ⊕ Fin 2 → F) =
      quadMinus 4 F b c (w : Fin 3 ⊕ Fin 3 ⊕ Fin 2 → F) := by
    have h := hQ
    rw [QuadraticMap.map_add (quadMinus 4 F b c) (w : Fin 3 ⊕ Fin 3 ⊕ Fin 2 → F)
      ((K328R8L2.k328r8c_l2_fW F z w : K328R8L2.k328r8c_l2_W F z) :
        Fin 3 ⊕ Fin 3 ⊕ Fin 2 → F)] at h
    rw [h1, map_of_mem hz (w : Fin 3 ⊕ Fin 3 ⊕ Fin 2 → F)] at h
    have h2v : quadMinus 4 F b c (w : Fin 3 ⊕ Fin 3 ⊕ Fin 2 → F) +
        quadMinus 4 F b c (w : Fin 3 ⊕ Fin 3 ⊕ Fin 2 → F) = 0 := by
      rw [← two_smul F (quadMinus 4 F b c (w : Fin 3 ⊕ Fin 3 ⊕ Fin 2 → F)),
        CharTwo.two_eq_zero, zero_smul]
    rw [h2v, zero_add] at h
    exact h.symm
  exact hpolar.symm

private noncomputable def k328r8c_B {F : Type} [Field F] (b c : F)
    (z : GL (Fin 3 ⊕ Fin 3 ⊕ Fin 2) F) :
    LinearMap.BilinForm F (K328R8L2.k328r8c_l2_W F z) :=
  LinearMap.mk₂ F (fun x y : K328R8L2.k328r8c_l2_W F z =>
      polar (quadMinus 4 F b c) (x : Fin 3 ⊕ Fin 3 ⊕ Fin 2 → F)
        (y : Fin 3 ⊕ Fin 3 ⊕ Fin 2 → F))
    (fun x y zz => by
      simp only [Submodule.coe_add, polar_add_left])
    (fun a x y => by
      rw [Submodule.coe_smul, polar_smul_left_eq, smul_eq_mul])
    (fun x y zz => by
      simp only [Submodule.coe_add, polar_add_right])
    (fun a x y => by
      rw [Submodule.coe_smul, polar_smul_right_eq, smul_eq_mul])

private theorem k328r8c_frame_W {F : Type} [Field F] [Fintype F] [CharP F 2] (b c : F)
    (hF : Fintype.card F = 8) (hbc : ∀ s : F, s ^ 2 + b * s + c ≠ 0)
    (z : GL (Fin 3 ⊕ Fin 3 ⊕ Fin 2) F)
    (hz : toLinEquiv (Fin 3 ⊕ Fin 3 ⊕ Fin 2) F z ∈ orthogonalGroup (quadMinus 4 F b c))
    (hz3 : z ^ 3 = 1)
    (hWfr : Module.finrank F (K328R8L2.k328r8c_l2_W F z) = 6) :
    ∃ v : Fin 3 → K328R8L2.k328r8c_l2_W F z,
      LinearIndependent F (Sum.elim v (fun i => K328R8L2.k328r8c_l2_fW F z (v i))) ∧
      (∀ i, quadMinus 4 F b c (v i : Fin 3 ⊕ Fin 3 ⊕ Fin 2 → F) = 1) ∧
      (∀ i j, polar (quadMinus 4 F b c) (v i : Fin 3 ⊕ Fin 3 ⊕ Fin 2 → F)
        ((K328R8L2.k328r8c_l2_fW F z (v j) : K328R8L2.k328r8c_l2_W F z) :
          Fin 3 ⊕ Fin 3 ⊕ Fin 2 → F) = if i = j then 1 else 0) ∧
      (∀ i j, polar (quadMinus 4 F b c) (v i : Fin 3 ⊕ Fin 3 ⊕ Fin 2 → F)
        (v j : Fin 3 ⊕ Fin 3 ⊕ Fin 2 → F) = 0) := by
  have : CharP F 2 :=
    charP_of_card_eq_prime_pow (show Fintype.card F = 2 ^ 3 by rw [hF]; norm_num)
  have : FiniteDimensional F (K328R8L2.k328r8c_l2_W F z) := inferInstance
  have hWnd := k328r8c_polarNondegOn_W b c hbc z hz hz3
  have hB : ∀ x : K328R8L2.k328r8c_l2_W F z,
      (∀ y : K328R8L2.k328r8c_l2_W F z, k328r8c_B b c z x y = 0) → x = 0 := by
    intro x hx
    exact Subtype.ext (hWnd x x.2 (fun y hy => hx ⟨y, hy⟩))
  have halt : ∀ x : K328R8L2.k328r8c_l2_W F z, k328r8c_B b c z x x = 0 := by
    intro x
    change polar (quadMinus 4 F b c) (x : Fin 3 ⊕ Fin 3 ⊕ Fin 2 → F)
      (x : Fin 3 ⊕ Fin 3 ⊕ Fin 2 → F) = 0
    rw [polar_self_eq_two_mul, CharTwo.two_eq_zero, zero_mul]
  have hzB : ∀ x y : K328R8L2.k328r8c_l2_W F z,
      k328r8c_B b c z (K328R8L2.k328r8c_l2_fW F z x) (K328R8L2.k328r8c_l2_fW F z y) =
      k328r8c_B b c z x y := by
    intro x y
    exact k328r8c_l2_polar_fW_fW b c z hz x y
  have hz3B : ∀ x : K328R8L2.k328r8c_l2_W F z,
      K328R8L2.k328r8c_l2_fW F z (K328R8L2.k328r8c_l2_fW F z x) +
        K328R8L2.k328r8c_l2_fW F z x + x = 0 := by
    intro x
    have hx2 : x + x = 0 := by
      apply Subtype.ext
      funext i
      simpa using CharTwo.add_self_eq_zero ((x : Fin 3 ⊕ Fin 3 ⊕ Fin 2 → F) i)
    have hf2 : K328R8L2.k328r8c_l2_fW F z x + K328R8L2.k328r8c_l2_fW F z x = 0 := by
      apply Subtype.ext
      funext i
      simpa using CharTwo.add_self_eq_zero
        (((K328R8L2.k328r8c_l2_fW F z x : K328R8L2.k328r8c_l2_W F z) :
          Fin 3 ⊕ Fin 3 ⊕ Fin 2 → F) i)
    calc K328R8L2.k328r8c_l2_fW F z (K328R8L2.k328r8c_l2_fW F z x) +
          K328R8L2.k328r8c_l2_fW F z x + x
        = (x + K328R8L2.k328r8c_l2_fW F z x) + K328R8L2.k328r8c_l2_fW F z x + x := by
          rw [k328r8c_l2_fW_sq (z := z) x]
      _ = (x + x) + (K328R8L2.k328r8c_l2_fW F z x + K328R8L2.k328r8c_l2_fW F z x) := by
          abel
      _ = 0 := by rw [hx2, hf2, add_zero]
  obtain ⟨k, v, hk, hli, hpair, hvv⟩ := k328_isometry_frame
    (k328r8c_B b c z) hB halt (K328R8L2.k328r8c_l2_fW F z) hzB hz3B
  have hk3 : k = 3 := by
    have : 2 * k = 6 := by rw [hk, hWfr]
    omega
  subst hk3
  refine ⟨v, hli, ?_, ?_, ?_⟩
  · intro i
    rw [k328r8c_Q_eq_polar b c z hz (v i)]
    simpa only [k328r8c_B, LinearMap.mk₂_apply, if_true] using hpair i i
  · intro i j
    simpa only [k328r8c_B, LinearMap.mk₂_apply] using hpair i j
  · intro i j
    simpa only [k328r8c_B, LinearMap.mk₂_apply] using hvv i j

private theorem k328r8c_quad_eq_of_basis {F : Type} [Field F] {V : Type} [AddCommGroup V]
    [Module F V] {ι : Type} [Fintype ι] [DecidableEq ι]
    {Q₁ Q₂ : QuadraticMap F V F} (b : Basis ι F V)
    (h1 : ∀ i, Q₁ (b i) = Q₂ (b i))
    (h2 : ∀ i j, polar Q₁ (b i) (b j) = polar Q₂ (b i) (b j)) : Q₁ = Q₂ := by
  set D : QuadraticMap F V F := Q₁ - Q₂ with hD
  have hDapp : ∀ x, D x = Q₁ x - Q₂ x := fun x => by
    simp [hD]
  have hpolarDef : ∀ x y, polar D x y = polar Q₁ x y - polar Q₂ x y := fun x y => by
    simp only [polar, hDapp]
    abel
  have hpolar : ∀ x y, polar D x y = 0 := by
    intro x y
    change (polarBilin D) x y = 0
    rw [← b.sum_repr x, ← b.sum_repr y]
    simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [Finset.smul_sum]
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [polarBilin_apply_apply, hpolarDef, h2 j i, sub_self]
    simp
  have hadd : ∀ x y, D (x + y) = D x + D y := fun x y => by
    rw [QuadraticMap.map_add D, hpolar x y, add_zero]
  let Dh : V →+ F :=
    { toFun := D, map_zero' := QuadraticMap.map_zero D, map_add' := hadd }
  have hDh : ∀ x, Dh x = D x := fun x => rfl
  have hD0 : ∀ x, D x = 0 := by
    intro x
    have hx : x = ∑ i, b.repr x i • b i := (b.sum_repr x).symm
    rw [← hDh, hx, map_sum]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [hDh, QuadraticMap.map_smul, hDapp, h1 i, sub_self, smul_zero]
  ext x
  have := hD0 x
  rw [hDapp, sub_eq_zero] at this
  exact this

private noncomputable abbrev k328r8c4_rotForm (F : Type) [Field F] : QuadraticForm F (F × F) :=
  CFSG.ClassicalGroups.Orthogonal.OmegaMinus8ThreeLocal.rotForm F

private def k328r8c4_gfam (F : Type) [Field F] : Fin 3 ⊕ Fin 3 → (Fin 3 → F × F) :=
  Sum.elim (fun i : Fin 3 => (Pi.single i (1, 0) : Fin 3 → F × F))
    (fun i : Fin 3 => Pi.single i (0, 1))

private theorem k328r8c4_gfam_linearIndependent (F : Type) [Field F] :
    LinearIndependent F (k328r8c4_gfam F) := by
  rw [Fintype.linearIndependent_iff]
  intro a ha i
  rcases i with i | i
  · have hsum := congrFun ha i
    rw [Finset.sum_apply, Fintype.sum_sum_type] at hsum
    simp only [k328r8c4_gfam, Sum.elim_inl, Sum.elim_inr, Pi.smul_apply] at hsum
    have h1 : (∑ x : Fin 3, a (Sum.inl x) • (Pi.single x (1, 0) : Fin 3 → F × F) i) =
        a (Sum.inl i) • ((1, 0) : F × F) := by
      rw [Finset.sum_eq_single i]
      · simp
      · intro k _ hk
        rw [Pi.single_eq_of_ne (M := fun _ => F × F) hk.symm ((1, 0) : F × F), smul_zero]
      · intro h; exact absurd (Finset.mem_univ i) h
    have h2 : (∑ x : Fin 3, a (Sum.inr x) • (Pi.single x (0, 1) : Fin 3 → F × F) i) =
        a (Sum.inr i) • ((0, 1) : F × F) := by
      rw [Finset.sum_eq_single i]
      · simp
      · intro k _ hk
        rw [Pi.single_eq_of_ne (M := fun _ => F × F) hk.symm ((0, 1) : F × F), smul_zero]
      · intro h; exact absurd (Finset.mem_univ i) h
    rw [h1, h2] at hsum
    simpa using congrArg Prod.fst hsum
  · have hsum := congrFun ha i
    rw [Finset.sum_apply, Fintype.sum_sum_type] at hsum
    simp only [k328r8c4_gfam, Sum.elim_inl, Sum.elim_inr, Pi.smul_apply] at hsum
    have h1 : (∑ x : Fin 3, a (Sum.inl x) • (Pi.single x (1, 0) : Fin 3 → F × F) i) =
        a (Sum.inl i) • ((1, 0) : F × F) := by
      rw [Finset.sum_eq_single i]
      · simp
      · intro k _ hk
        rw [Pi.single_eq_of_ne (M := fun _ => F × F) hk.symm ((1, 0) : F × F), smul_zero]
      · intro h; exact absurd (Finset.mem_univ i) h
    have h2 : (∑ x : Fin 3, a (Sum.inr x) • (Pi.single x (0, 1) : Fin 3 → F × F) i) =
        a (Sum.inr i) • ((0, 1) : F × F) := by
      rw [Finset.sum_eq_single i]
      · simp
      · intro k _ hk
        rw [Pi.single_eq_of_ne (M := fun _ => F × F) hk.symm ((0, 1) : F × F), smul_zero]
      · intro h; exact absurd (Finset.mem_univ i) h
    rw [h1, h2] at hsum
    simpa using congrArg Prod.snd hsum

private theorem k328r8c4_polar_pi_rotForm_single (F : Type) [Field F]
    (i j : Fin 3) (a b : F × F) :
    polar (QuadraticMap.pi (fun _ : Fin 3 => k328r8c4_rotForm F)) (Pi.single i a) (Pi.single j b) =
      if i = j then polar (k328r8c4_rotForm F) a b else 0 := by
  rw [QuadraticMap.Ring.polar_pi]
  by_cases h : i = j
  · subst h
    rw [Finset.sum_eq_single i]
    · simp
    · intro k _ hk; simp [Pi.single_eq_of_ne hk]
    · intro hk; exact absurd (Finset.mem_univ i) hk
  · rw [Finset.sum_eq_zero]
    · simp [h]
    · intro k _
      by_cases hki : k = i
      · subst hki; simp [Pi.single_eq_of_ne h]
      · simp [Pi.single_eq_of_ne hki]

private theorem k328r8c4_polar_rotForm_apply (F : Type) [Field F] [CharP F 2] (p q : F × F) :
    polar (k328r8c4_rotForm F) p q = p.1 * q.2 + q.1 * p.2 := by
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  rw [QuadraticMap.polar,
    show k328r8c4_rotForm F = CFSG.ClassicalGroups.Orthogonal.OmegaMinus8ThreeLocal.rotForm F
      from rfl,
    CFSG.ClassicalGroups.Orthogonal.OmegaMinus8ThreeLocal.rotForm, binForm_apply, binForm_apply,
    binForm_apply]
  simp only [Prod.fst_add, Prod.snd_add]
  linear_combination (p.1 * q.1 + p.2 * q.2 - p.1 * q.2 - q.1 * p.2) * h2

private theorem k328r8c4_polar_rotForm_std (F : Type) [Field F] [CharP F 2] :
    polar (k328r8c4_rotForm F) ((1, 0) : F × F) ((1, 0) : F × F) = 0 ∧
    polar (k328r8c4_rotForm F) ((0, 1) : F × F) ((0, 1) : F × F) = 0 ∧
    polar (k328r8c4_rotForm F) ((1, 0) : F × F) ((0, 1) : F × F) = 1 ∧
    polar (k328r8c4_rotForm F) ((0, 1) : F × F) ((1, 0) : F × F) = 1 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> rw [k328r8c4_polar_rotForm_apply] <;> ring

private theorem k328r8c4_rotForm_one_zero (F : Type) [Field F] :
    k328r8c4_rotForm F ((1, 0) : F × F) = 1 := by
  rw [show k328r8c4_rotForm F = CFSG.ClassicalGroups.Orthogonal.OmegaMinus8ThreeLocal.rotForm F
      from rfl,
    CFSG.ClassicalGroups.Orthogonal.OmegaMinus8ThreeLocal.rotForm_apply]
  ring

private theorem k328r8c4_rotForm_zero_one (F : Type) [Field F] :
    k328r8c4_rotForm F ((0, 1) : F × F) = 1 := by
  rw [show k328r8c4_rotForm F = CFSG.ClassicalGroups.Orthogonal.OmegaMinus8ThreeLocal.rotForm F
      from rfl,
    CFSG.ClassicalGroups.Orthogonal.OmegaMinus8ThreeLocal.rotForm_apply]
  ring

private theorem k328r8c4_polar_comp {F V W : Type} [Field F] [AddCommGroup V] [Module F V]
    [AddCommGroup W] [Module F W] (Q : QuadraticForm F W) (f : V →ₗ[F] W) (x y : V) :
    polar (Q.comp f) x y = polar Q (f x) (f y) := by
  simp only [QuadraticMap.polar, QuadraticMap.comp_apply, map_add]

private theorem k328r8c4_not_isPlusType_pi_rotForm (F : Type) [Field F] [Fintype F]
    (hF : Fintype.card F = 8) :
    ¬ IsPlusType (QuadraticMap.pi (fun _ : Fin 3 => k328r8c4_rotForm F)) := by
  have hcharP : CharP F 2 := charP_of_card_eq_prime_pow (p := 2) (f := 3) (by rw [hF]; norm_num)
  have h3 : (3 : F) ≠ 0 := by
    intro hz
    have hdvd : 2 ∣ 3 := (CharP.cast_eq_zero_iff F 2 3).mp hz
    norm_num at hdvd
  have hnotsplit : ¬ CFSG.ClassicalGroups.Orthogonal.OmegaMinus8ThreeLocal.IsSplit F := by
    rw [CFSG.ClassicalGroups.Orthogonal.OmegaMinus8ThreeLocal.isSplit_iff_card_mod_three h3,
      Nat.card_eq_fintype_card, hF]
    norm_num
  have hrot : ¬ IsPlusType (k328r8c4_rotForm F) := by
    rw [show IsPlusType (k328r8c4_rotForm F) ↔
        IsPlusType (CFSG.ClassicalGroups.Orthogonal.OmegaMinus8ThreeLocal.rotForm F) from
      Iff.rfl]
    rw [CFSG.ClassicalGroups.Orthogonal.OmegaMinus8ThreeLocal.isPlusType_rotForm_iff h3]
    exact hnotsplit
  intro h
  have hdim : Module.finrank F (F × F) = 2 * 1 := by
    rw [Module.finrank_prod, Module.finrank_self]
  exact hrot ((CFSG.ClassicalGroups.Orthogonal.OmegaMinus8ThreeLocal.isPlusType_pi_fin_three_iff
    (CFSG.ClassicalGroups.Orthogonal.OmegaMinus8ThreeLocal.nondegenerate_polarBilin_rotForm h3)
    (by norm_num) hdim).mp h)

private theorem k328r8c4_frame_polar_eq
    (F : Type) [Field F] [Fintype F] [DecidableEq F] [CharP F 2]
    {Wmv : Type} [AddCommGroup Wmv] [Module F Wmv]
    (Qw : QuadraticForm F Wmv) (v : Fin 3 → Wmv) (σ : Wmv → Wmv)
    (b : Basis (Fin 3 ⊕ Fin 3) F Wmv)
    (hb1 : ∀ i, b (Sum.inl i) = v i) (hb2 : ∀ i, b (Sum.inr i) = σ (v i))
    (φ : (Fin 3 → F × F) ≃ₗ[F] Wmv)
    (hsymm1 : ∀ i, (φ.symm : Wmv →ₗ[F] (Fin 3 → F × F)) (v i) =
      (Pi.single i (1, 0) : Fin 3 → F × F))
    (hsymm2 : ∀ i, (φ.symm : Wmv →ₗ[F] (Fin 3 → F × F)) (σ (v i)) =
      (Pi.single i (0, 1) : Fin 3 → F × F))
    (Q₂ : QuadraticForm F Wmv)
    (hQ₂ : Q₂ = (QuadraticMap.pi (fun _ : Fin 3 => k328r8c4_rotForm F)).comp
      (φ.symm : Wmv →ₗ[F] (Fin 3 → F × F)))
    (hvv : ∀ i j, polar Qw (v i) (v j) = 0)
    (hvz : ∀ i j, polar Qw (v i) (σ (v j)) = if i = j then 1 else 0)
    (hzz : ∀ i j, polar Qw (σ (v i)) (σ (v j)) = 0) :
    ∀ j k, polar Qw (b j) (b k) = polar Q₂ (b j) (b k) := by
  intro j k
  rw [hQ₂, k328r8c4_polar_comp]
  rcases j with i | i <;> rcases k with j' | j'
  · rw [hb1 i, hb1 j', hsymm1 i, hsymm1 j', k328r8c4_polar_pi_rotForm_single, hvv,
      show polar (k328r8c4_rotForm F) ((1, 0) : F × F) ((1, 0) : F × F) = 0 from
        (k328r8c4_polar_rotForm_std F).1]
    by_cases h : i = j' <;> simp [h]
  · rw [hb1 i, hb2 j', hsymm1 i, hsymm2 j', k328r8c4_polar_pi_rotForm_single, hvz,
      show polar (k328r8c4_rotForm F) ((1, 0) : F × F) ((0, 1) : F × F) = 1 from
        (k328r8c4_polar_rotForm_std F).2.2.1]
  · rw [hb2 i, hb1 j', hsymm2 i, hsymm1 j', k328r8c4_polar_pi_rotForm_single,
      show polar (k328r8c4_rotForm F) ((0, 1) : F × F) ((1, 0) : F × F) = 1 from
        (k328r8c4_polar_rotForm_std F).2.2.2,
      show polar Qw (σ (v i)) (v j') = (if i = j' then 1 else 0) from by
        rw [polar_comm, hvz j' i]
        by_cases h : i = j'
        · subst h; simp
        · have h' : j' ≠ i := fun hh => h hh.symm
          simp [h, h']]
  · rw [hb2 i, hb2 j', hsymm2 i, hsymm2 j', k328r8c4_polar_pi_rotForm_single, hzz,
      show polar (k328r8c4_rotForm F) ((0, 1) : F × F) ((0, 1) : F × F) = 0 from
        (k328r8c4_polar_rotForm_std F).2.1]
    by_cases h : i = j' <;> simp [h]

private theorem k328r8c4_not_isPlusType_of_frame
    (F : Type) [Field F] [Fintype F] [DecidableEq F] [CharP F 2] (hF : Fintype.card F = 8)
    {Wmv : Type} [AddCommGroup Wmv] [Module F Wmv] [FiniteDimensional F Wmv]
    (Qw : QuadraticForm F Wmv) (v : Fin 3 → Wmv) (σ : Wmv → Wmv)
    (hli : LinearIndependent F (Sum.elim v (fun i => σ (v i))))
    (hWfr : Module.finrank F Wmv = 6)
    (hQv : ∀ i, Qw (v i) = 1) (hQzv : ∀ i, Qw (σ (v i)) = 1)
    (hvv : ∀ i j, polar Qw (v i) (v j) = 0)
    (hvz : ∀ i j, polar Qw (v i) (σ (v j)) = if i = j then 1 else 0)
    (hzz : ∀ i j, polar Qw (σ (v i)) (σ (v j)) = 0) :
    ¬ IsPlusType Qw := by
  have hgfam := k328r8c4_gfam_linearIndependent F
  let g : Basis (Fin 3 ⊕ Fin 3) F (Fin 3 → F × F) :=
    basisOfLinearIndependentOfCardEqFinrank hgfam (by
      rw [Fintype.card_sum, Fintype.card_fin]
      simp [Module.finrank_pi_fintype, Module.finrank_prod, Module.finrank_self])
  have hgcoe : ⇑g = k328r8c4_gfam F := coe_basisOfLinearIndependentOfCardEqFinrank _ _
  let b : Basis (Fin 3 ⊕ Fin 3) F Wmv :=
    basisOfLinearIndependentOfCardEqFinrank hli (by
      rw [Fintype.card_sum, Fintype.card_fin, hWfr])
  have hbcoe : ⇑b = Sum.elim v (fun i => σ (v i)) :=
    coe_basisOfLinearIndependentOfCardEqFinrank _ _
  have hb1 : ∀ i, b (Sum.inl i) = v i := fun i => by rw [hbcoe]; rfl
  have hb2 : ∀ i, b (Sum.inr i) = σ (v i) := fun i => by rw [hbcoe]; rfl
  let φ : (Fin 3 → F × F) ≃ₗ[F] Wmv := g.equiv b (Equiv.refl _)
  have hφg : ∀ j, φ (g j) = b j := fun j => by simp [φ]
  have hφ1 : ∀ i, φ (Pi.single i (1, 0) : Fin 3 → F × F) = v i := by
    intro i
    have h1 : g (Sum.inl i) = (Pi.single i (1, 0) : Fin 3 → F × F) := by rw [hgcoe]; rfl
    rw [← h1, ← hb1 i, hφg]
  have hφ2 : ∀ i, φ (Pi.single i (0, 1) : Fin 3 → F × F) = σ (v i) := by
    intro i
    have h1 : g (Sum.inr i) = (Pi.single i (0, 1) : Fin 3 → F × F) := by rw [hgcoe]; rfl
    rw [← h1, ← hb2 i, hφg]
  have hsymm1 : ∀ i, φ.symm (v i) = (Pi.single i (1, 0) : Fin 3 → F × F) := fun i =>
    (φ.symm_apply_eq).mpr (hφ1 i).symm
  have hsymm2 : ∀ i, φ.symm (σ (v i)) = (Pi.single i (0, 1) : Fin 3 → F × F) := fun i =>
    (φ.symm_apply_eq).mpr (hφ2 i).symm
  let Q₂ : QuadraticForm F Wmv :=
    (QuadraticMap.pi (fun _ : Fin 3 => k328r8c4_rotForm F)).comp
      (φ.symm : Wmv →ₗ[F] (Fin 3 → F × F))
  have hQ : Qw = Q₂ := by
    refine k328r8c_quad_eq_of_basis (F := F) (V := Wmv) b ?_ ?_
    · intro j
      rcases j with i | i
      · rw [hb1 i, show Q₂ (v i) =
            (QuadraticMap.pi (fun _ : Fin 3 => k328r8c4_rotForm F)) (φ.symm (v i)) from rfl,
          hsymm1 i, QuadraticMap.pi_apply_single, k328r8c4_rotForm_one_zero, hQv i]
      · rw [hb2 i, show Q₂ (σ (v i)) =
            (QuadraticMap.pi (fun _ : Fin 3 => k328r8c4_rotForm F)) (φ.symm (σ (v i))) from rfl,
          hsymm2 i, QuadraticMap.pi_apply_single, k328r8c4_rotForm_zero_one, hQzv i]
    · exact k328r8c4_frame_polar_eq F Qw v σ b hb1 hb2 φ hsymm1 hsymm2 Q₂ rfl hvv hvz hzz
  intro hplus
  have hrot := k328r8c4_not_isPlusType_pi_rotForm F hF
  have hiso : (QuadraticMap.pi (fun _ : Fin 3 => k328r8c4_rotForm F)).IsometryEquiv Qw :=
    { toLinearEquiv := φ
      map_app' := fun p => by
        rw [hQ]
        show (QuadraticMap.pi (fun _ : Fin 3 => k328r8c4_rotForm F)) (φ.symm (φ p)) =
          (QuadraticMap.pi (fun _ : Fin 3 => k328r8c4_rotForm F)) p
        rw [LinearEquiv.symm_apply_apply] }
  exact hrot ((isPlusType_congr hiso).mpr hplus)

private theorem k328r8c4_not_isPlusType_W (F : Type) [Field F] [Fintype F] [DecidableEq F]
    (b c : F) (hF : Fintype.card F = 8)
    (hbc : ∀ s : F, s ^ 2 + b * s + c ≠ 0)
    (z : GL (Fin 3 ⊕ Fin 3 ⊕ Fin 2) F)
    (hz : toLinEquiv (Fin 3 ⊕ Fin 3 ⊕ Fin 2) F z ∈ orthogonalGroup (quadMinus 4 F b c))
    (hz3 : z ^ 3 = 1)
    (hWfr : Module.finrank F (K328R8L2.k328r8c_l2_W F z) = 6) :
    ¬ IsPlusType ((quadMinus 4 F b c).restrict (K328R8L2.k328r8c_l2_W F z)) := by
  have hcharP : CharP F 2 := charP_of_card_eq_prime_pow (p := 2) (f := 3) (by rw [hF]; norm_num)
  obtain ⟨v, hli, hQv, hpair, hvv⟩ := k328r8c_frame_W b c hF hbc z hz hz3 hWfr
  refine k328r8c4_not_isPlusType_of_frame F hF
    ((quadMinus 4 F b c).restrict (K328R8L2.k328r8c_l2_W F z)) v
    (K328R8L2.k328r8c_l2_fW F z) hli hWfr ?_ ?_ ?_ ?_ ?_
  · intro i; exact hQv i
  · intro i
    change quadMinus 4 F b c
      ((K328R8L2.k328r8c_l2_fW F z (v i) : K328R8L2.k328r8c_l2_W F z) :
        Fin 3 ⊕ Fin 3 ⊕ Fin 2 → F) = 1
    rw [k328r8c_l2_fW_coe, map_of_mem hz, hQv i]
  · intro i j; exact hvv i j
  · intro i j
    change polar (quadMinus 4 F b c) ((v i : K328R8L2.k328r8c_l2_W F z) :
        Fin 3 ⊕ Fin 3 ⊕ Fin 2 → F)
      ((K328R8L2.k328r8c_l2_fW F z (v j) : K328R8L2.k328r8c_l2_W F z) :
        Fin 3 ⊕ Fin 3 ⊕ Fin 2 → F) = _
    exact hpair i j
  · intro i j
    change polar (quadMinus 4 F b c)
      ((K328R8L2.k328r8c_l2_fW F z (v i) : K328R8L2.k328r8c_l2_W F z) :
        Fin 3 ⊕ Fin 3 ⊕ Fin 2 → F)
      ((K328R8L2.k328r8c_l2_fW F z (v j) : K328R8L2.k328r8c_l2_W F z) :
        Fin 3 ⊕ Fin 3 ⊕ Fin 2 → F) = 0
    rw [k328r8c_l2_fW_coe, k328r8c_l2_fW_coe, polar_map_of_mem hz, hvv i j]

private theorem k328r8c_fix_isPlusType {F : Type} [Field F] [Fintype F] [DecidableEq F]
    (b c : F) (hF : Fintype.card F = 8)
    (hbc : ∀ s : F, s ^ 2 + b * s + c ≠ 0)
    (z : GL (Fin 3 ⊕ Fin 3 ⊕ Fin 2) F)
    (hz : toLinEquiv (Fin 3 ⊕ Fin 3 ⊕ Fin 2) F z ∈ orthogonalGroup (quadMinus 4 F b c))
    (hz3 : z ^ 3 = 1)
    (hFix : Module.finrank F (LinearMap.ker (K328R8L2.k328r8c_l2_fOf F z - 1)) = 2) :
    IsPlusType ((quadMinus 4 F b c).restrict
      (LinearMap.ker (K328R8L2.k328r8c_l2_fOf F z - 1))) := by
  have hcharP : CharP F 2 := charP_of_card_eq_prime_pow (p := 2) (f := 3) (by rw [hF]; norm_num)
  have hZ3 : (K328R8L2.k328r8c_l2_fOf F z) ^ 3 = 1 := by
    rw [← K328R8L2.k328r8c_l2_fOf_pow, hz3, K328R8L2.k328r8c_l2_fOf_one]
  have hcompl := k328r8c_isCompl_fix_move (V := Fin 3 ⊕ Fin 3 ⊕ Fin 2 → F)
    (Z := K328R8L2.k328r8c_l2_fOf F z) hZ3
  have hV : Module.finrank F (Fin 3 ⊕ Fin 3 ⊕ Fin 2 → F) = 8 := by
    rw [Module.finrank_fintype_fun_eq_card]
    simp [Fintype.card_sum, Fintype.card_fin]
  have hWfr : Module.finrank F (K328R8L2.k328r8c_l2_W F z) = 6 := by
    have h := Submodule.finrank_add_eq_of_isCompl hcompl
    rw [hFix, hV] at h
    change 2 + Module.finrank F (K328R8L2.k328r8c_l2_W F z) = 8 at h
    omega
  have hWnp := k328r8c4_not_isPlusType_W F b c hF hbc z hz hz3 hWfr
  have hnd := nondegenerate_polarBilin_quadMinus_of_finite (n := 4) F hbc
  have hFixnd : PolarNondegOn (quadMinus 4 F b c)
      (LinearMap.ker (K328R8L2.k328r8c_l2_fOf F z - 1)) := by
    intro x hx hxperp
    apply eq_zero_of_polar_eq_zero hnd
    intro y
    obtain ⟨a, w, rfl⟩ := CFSG.LocalAnalysis.ComponentInitial.exists_add_of_isCompl hcompl y
    rw [polar_add_right, hxperp a a.2,
      k328r8c_polar_fix_W b c z hz hx (m := w), add_zero]
  have hWnd := k328r8c_polarNondegOn_W b c hbc z hz hz3
  have horth : ∀ x ∈ LinearMap.ker (K328R8L2.k328r8c_l2_fOf F z - 1),
      ∀ y ∈ K328R8L2.k328r8c_l2_W F z, polar (quadMinus 4 F b c) x y = 0 :=
    fun x hx y hy => k328r8c_polar_fix_W b c z hz hx (m := ⟨y, hy⟩)
  have hiff := CFSG.ClassicalInvolution.RouteD.TWY.isPlusType_iff_of_isCompl hcompl horth
    hFixnd hWnd (a := 1) (b := 3) (by norm_num) (by norm_num) hFix hWfr
  have hQnp : ¬ IsPlusType (quadMinus 4 F b c) :=
    not_isPlusType_quadMinus (n := 4) (by norm_num) hbc
  rw [hiff] at hQnp
  by_contra hFixnp
  exact hQnp ⟨fun h => absurd h hFixnp, fun h => absurd h hWnp⟩

private theorem k328r8c5_li_pair {F : Type} [Field F] [CharP F 2] {V : Type} [AddCommGroup V]
    [Module F V] {Q : QuadraticForm F V} {e f : V}
    (he : Q e = 0) (hf : Q f = 0) (hef : polar Q e f = 1) :
    LinearIndependent F ![e, f] := by
  rw [LinearIndependent.pair_iff]
  intro a b hab
  have he0 : polar Q e e = 0 := polar_self_eq_zero he
  have hf0 : polar Q f f = 0 := polar_self_eq_zero hf
  constructor
  · have h := congrArg (fun v => polar Q v f) hab
    rw [polar_add_left, polar_smul_left_eq, polar_smul_left_eq, hef, hf0, mul_one, mul_zero,
      add_zero, polar_zero_left] at h
    exact h
  · have h := congrArg (fun v => polar Q v e) hab
    rw [polar_add_left, polar_smul_left_eq, polar_smul_left_eq, polar_comm Q f e, hef, he0,
      mul_one, mul_zero, zero_add, polar_zero_left] at h
    exact h

private theorem k328r8c5_hypPair_fix {F : Type} [Field F] [Fintype F] [CharP F 2] (b c : F)
    (hbc : ∀ s : F, s ^ 2 + b * s + c ≠ 0)
    (z : GL (Fin 3 ⊕ Fin 3 ⊕ Fin 2) F)
    (hz : toLinEquiv (Fin 3 ⊕ Fin 3 ⊕ Fin 2) F z ∈ orthogonalGroup (quadMinus 4 F b c))
    (hz3 : z ^ 3 = 1)
    (hFix : Module.finrank F (LinearMap.ker (K328R8L2.k328r8c_l2_fOf F z - 1)) = 2)
    (hplus : IsPlusType ((quadMinus 4 F b c).restrict
      (LinearMap.ker (K328R8L2.k328r8c_l2_fOf F z - 1)))) :
    ∃ P : HypPair (quadMinus 4 F b c),
      P.e ∈ LinearMap.ker (K328R8L2.k328r8c_l2_fOf F z - 1) ∧
      P.f ∈ LinearMap.ker (K328R8L2.k328r8c_l2_fOf F z - 1) := by
  obtain ⟨e, heFix, he0, hQe⟩ :=
    (CFSG.ClassicalInvolution.RouteD.TWY.isPlusType_restrict_iff_of_finrank_two
      (Q := quadMinus 4 F b c) (W := LinearMap.ker (K328R8L2.k328r8c_l2_fOf F z - 1))
      hFix).mp hplus
  have hZ3 : (K328R8L2.k328r8c_l2_fOf F z) ^ 3 = 1 := by
    rw [← K328R8L2.k328r8c_l2_fOf_pow, hz3, K328R8L2.k328r8c_l2_fOf_one]
  have hcompl := k328r8c_isCompl_fix_move (V := Fin 3 ⊕ Fin 3 ⊕ Fin 2 → F)
    (Z := K328R8L2.k328r8c_l2_fOf F z) hZ3
  have hnd : (polarBilin (quadMinus 4 F b c)).Nondegenerate :=
    nondegenerate_polarBilin_quadMinus_of_finite (n := 4) F hbc
  obtain ⟨h0, hh0⟩ := exists_polar_ne_zero hnd he0
  let pe := Submodule.prodEquivOfIsCompl
    (LinearMap.ker (K328R8L2.k328r8c_l2_fOf F z - 1))
    (K328R8L2.k328r8c_l2_W F z) hcompl
  let hFix0 : LinearMap.ker (K328R8L2.k328r8c_l2_fOf F z - 1) := (pe.symm h0).1
  let hW0 : K328R8L2.k328r8c_l2_W F z := (pe.symm h0).2
  have h0eq : h0 = (hFix0 : Fin 3 ⊕ Fin 3 ⊕ Fin 2 → F) +
      (hW0 : Fin 3 ⊕ Fin 3 ⊕ Fin 2 → F) := by
    conv_lhs => rw [← pe.apply_symm_apply h0]
    exact rfl
  have hperp : polar (quadMinus 4 F b c) e
      (hW0 : Fin 3 ⊕ Fin 3 ⊕ Fin 2 → F) = 0 :=
    k328r8c_polar_fix_W b c z hz heFix (m := hW0)
  have hc : polar (quadMinus 4 F b c) e (hFix0 : Fin 3 ⊕ Fin 3 ⊕ Fin 2 → F) =
      polar (quadMinus 4 F b c) e h0 := by
    conv_rhs => rw [h0eq]
    rw [polar_add_right, hperp, add_zero]
  have hcne : polar (quadMinus 4 F b c) e (hFix0 : Fin 3 ⊕ Fin 3 ⊕ Fin 2 → F) ≠ 0 := by
    rw [hc]; exact hh0
  let hh : Fin 3 ⊕ Fin 3 ⊕ Fin 2 → F :=
    (polar (quadMinus 4 F b c) e (hFix0 : Fin 3 ⊕ Fin 3 ⊕ Fin 2 → F))⁻¹ • (hFix0 : _)
  have hhh : polar (quadMinus 4 F b c) e hh = 1 := by
    dsimp only [hh]
    rw [polar_smul_right_eq, inv_mul_cancel₀ hcne]
  have hhFix : hh ∈ LinearMap.ker (K328R8L2.k328r8c_l2_fOf F z - 1) :=
    Submodule.smul_mem _ _ hFix0.2
  refine ⟨HypPair.ofPolarEqOne hQe hhh, ?_, ?_⟩
  · rw [HypPair.ofPolarEqOne_e]; exact heFix
  · rw [HypPair.ofPolarEqOne_f]
    exact Submodule.sub_mem _ hhFix (Submodule.smul_mem _ _ heFix)

private theorem k328r8c5_finrank_W {F : Type} [Field F] [CharP F 2]
    (z : GL (Fin 3 ⊕ Fin 3 ⊕ Fin 2) F) (hz3 : z ^ 3 = 1)
    (hFix : Module.finrank F (LinearMap.ker (K328R8L2.k328r8c_l2_fOf F z - 1)) = 2) :
    Module.finrank F (K328R8L2.k328r8c_l2_W F z) = 6 := by
  have hZ3 : (K328R8L2.k328r8c_l2_fOf F z) ^ 3 = 1 := by
    rw [← K328R8L2.k328r8c_l2_fOf_pow, hz3, K328R8L2.k328r8c_l2_fOf_one]
  have hcompl := k328r8c_isCompl_fix_move (V := Fin 3 ⊕ Fin 3 ⊕ Fin 2 → F)
    (Z := K328R8L2.k328r8c_l2_fOf F z) hZ3
  have hV : Module.finrank F (Fin 3 ⊕ Fin 3 ⊕ Fin 2 → F) = 8 := by
    rw [Module.finrank_fintype_fun_eq_card]
    simp [Fintype.card_sum, Fintype.card_fin]
  have h := Submodule.finrank_add_eq_of_isCompl hcompl
  rw [hFix, hV] at h
  change Module.finrank F (LinearMap.ker (K328R8L2.k328r8c_l2_fOf F z ^ 2 +
    K328R8L2.k328r8c_l2_fOf F z + 1)) = 6
  exact add_left_cancel (h.trans (show (2 : ℕ) + 6 = 8 by norm_num).symm)

private theorem k328r8c5_basis_pair {F : Type} [Field F] [CharP F 2] {V : Type} [AddCommGroup V]
    [Module F V] {Q : QuadraticForm F V} {A : Submodule F V}
    (P : HypPair Q) (hPe : P.e ∈ A) (hPf : P.f ∈ A)
    (hA : Module.finrank F A = 2) :
    ∃ b : Basis (Fin 2) F A, b 0 = ⟨P.e, hPe⟩ ∧ b 1 = ⟨P.f, hPf⟩ := by
  have hli : LinearIndependent F (![⟨P.e, hPe⟩, ⟨P.f, hPf⟩] : Fin 2 → A) := by
    refine k328r8c5_li_pair (Q := Q.restrict A) ?_ ?_ ?_
    · simpa using P.Q_e
    · simpa using P.Q_f
    · simpa [polar_restrict] using P.polar_ef
  refine ⟨basisOfLinearIndependentOfCardEqFinrank hli (by
    rw [Fintype.card_fin, hA]), ?_, ?_⟩ <;>
    rw [coe_basisOfLinearIndependentOfCardEqFinrank] <;> simp

private theorem k328r8c5_basis_frame {F : Type} [Field F] [CharP F 2] {V : Type} [AddCommGroup V]
    [Module F V] {W : Submodule F V}
    (hW : Module.finrank F W = 6) (f : W →ₗ[F] W) (v : Fin 3 → W)
    (hvli : LinearIndependent F (Sum.elim v (fun i => f (v i)))) :
    ∃ b : Basis (Fin 3 ⊕ Fin 3) F W, (∀ i, b (Sum.inl i) = v i) ∧
      (∀ i, b (Sum.inr i) = f (v i)) := by
  refine ⟨basisOfLinearIndependentOfCardEqFinrank hvli (by
      rw [Fintype.card_sum, Fintype.card_fin, hW]), ?_, ?_⟩ <;>
    intro i <;> rw [coe_basisOfLinearIndependentOfCardEqFinrank] <;> simp

private theorem k328r8c5_polar_comp {F : Type} [Field F] {V' W : Type*} [AddCommGroup V']
    [Module F V'] [AddCommGroup W] [Module F W] {Q : QuadraticForm F W} (g : V' →ₗ[F] W)
    (x y : V') :
    polar (Q.comp g) x y = polar Q (g x) (g y) := by
  simp only [polar, QuadraticMap.comp_apply, map_add]

private theorem k328r8c5_gFix {F : Type} [Field F] {V : Type} [AddCommGroup V] [Module F V]
    [CharP F 2] {Q : QuadraticForm F V}
    {A B : Submodule F V} (P P' : HypPair Q)
    (hPe : P.e ∈ A) (hPf : P.f ∈ A) (hP'e : P'.e ∈ B) (hP'f : P'.f ∈ B)
    (hA : Module.finrank F A = 2) (hB : Module.finrank F B = 2) :
    ∃ g : A ≃ₗ[F] B, (∀ x, Q (g x) = Q x) ∧
      g ⟨P.e, hPe⟩ = ⟨P'.e, hP'e⟩ ∧ g ⟨P.f, hPf⟩ = ⟨P'.f, hP'f⟩ := by
  obtain ⟨b, hb0, hb1⟩ := k328r8c5_basis_pair P hPe hPf hA
  obtain ⟨b', hb'0, hb'1⟩ := k328r8c5_basis_pair P' hP'e hP'f hB
  have hval : ∀ i, (b.equiv b' (Equiv.refl (Fin 2))) (b i) = b' i :=
    fun i => by simp
  refine ⟨b.equiv b' (Equiv.refl (Fin 2)), ?_, ?_, ?_⟩
  · have hEq : (Q.restrict B).comp (b.equiv b' (Equiv.refl (Fin 2))).toLinearMap =
        Q.restrict A := by
      refine k328r8c_quad_eq_of_basis b ?_ ?_
      · intro i
        change (Q.restrict B) ((b.equiv b' (Equiv.refl (Fin 2))) (b i)) = (Q.restrict A) (b i)
        rw [hval i, restrict_apply, restrict_apply]
        fin_cases i <;> simp [hb'0, hb'1, hb0, hb1, P.Q_e, P.Q_f, P'.Q_e, P'.Q_f]
      · intro i j
        rw [k328r8c5_polar_comp]
        change polar (Q.restrict B) ((b.equiv b' (Equiv.refl (Fin 2))) (b i))
            ((b.equiv b' (Equiv.refl (Fin 2))) (b j)) =
          polar (Q.restrict A) (b i) (b j)
        rw [hval i, hval j, polar_restrict, polar_restrict]
        fin_cases i <;> fin_cases j <;>
          simp [hb'0, hb'1, hb0, hb1, HypPair.polar_fe, P.polar_ef, P'.polar_ef,
            CharTwo.two_eq_zero]
    intro x
    have := congrArg (fun Q' => Q' x) hEq
    simpa [QuadraticMap.comp_apply, restrict_apply] using this
  · rw [← hb0, ← hb'0]
    exact hval 0
  · rw [← hb1, ← hb'1]
    exact hval 1

private theorem k328r8c5_gW {F : Type} [Field F] {V : Type} [AddCommGroup V] [Module F V]
    [CharP F 2] {Q : QuadraticForm F V}
    {A B : Submodule F V} (fA : A →ₗ[F] A) (fB : B →ₗ[F] B)
    (v : Fin 3 → A) (v' : Fin 3 → B)
    (hvli : LinearIndependent F (Sum.elim v (fun i => fA (v i))))
    (hvli' : LinearIndependent F (Sum.elim v' (fun i => fB (v' i))))
    (hA : Module.finrank F A = 6) (hB : Module.finrank F B = 6)
    (hQv : ∀ i, Q (v i) = 1) (hQv' : ∀ i, Q (v' i) = 1)
    (hQfv : ∀ i, Q (fA (v i)) = 1) (hQfv' : ∀ i, Q (fB (v' i)) = 1)
    (hp : ∀ i j, polar Q (v i) (fA (v j)) = if i = j then 1 else 0)
    (hp' : ∀ i j, polar Q (v' i) (fB (v' j)) = if i = j then 1 else 0)
    (hvv : ∀ i j, polar Q (v i) (v j) = 0)
    (hvv' : ∀ i j, polar Q (v' i) (v' j) = 0)
    (hff : ∀ i j, polar Q (fA (v i)) (fA (v j)) = 0)
    (hff' : ∀ i j, polar Q (fB (v' i)) (fB (v' j)) = 0)
    (hfA2 : ∀ x, fA (fA x) = x + fA x) (hfB2 : ∀ x, fB (fB x) = x + fB x) :
    ∃ g : A ≃ₗ[F] B, (∀ x, Q (g x) = Q x) ∧
      (∀ i, g (v i) = v' i) ∧ (∀ i, g (fA (v i)) = fB (v' i)) ∧
      (∀ x, g (fA x) = fB (g x)) := by
  obtain ⟨b, hb, hbf⟩ := k328r8c5_basis_frame hA fA v hvli
  obtain ⟨b', hb', hb'f⟩ := k328r8c5_basis_frame hB fB v' hvli'
  have hval : ∀ p, (b.equiv b' (Equiv.refl (Fin 3 ⊕ Fin 3))) (b p) = b' p :=
    fun p => by simp
  refine ⟨b.equiv b' (Equiv.refl (Fin 3 ⊕ Fin 3)), ?_, ?_, ?_, ?_⟩
  · have hEq : (Q.restrict B).comp
        (b.equiv b' (Equiv.refl (Fin 3 ⊕ Fin 3))).toLinearMap = Q.restrict A := by
      refine k328r8c_quad_eq_of_basis b ?_ ?_
      · intro p
        change (Q.restrict B) ((b.equiv b' (Equiv.refl (Fin 3 ⊕ Fin 3))) (b p)) =
          (Q.restrict A) (b p)
        rw [hval p, restrict_apply, restrict_apply]
        rcases p with i | i <;> simp [hb, hb', hbf, hb'f, hQv, hQv', hQfv, hQfv']
      · intro p q
        rw [k328r8c5_polar_comp]
        change polar (Q.restrict B) ((b.equiv b' (Equiv.refl (Fin 3 ⊕ Fin 3))) (b p))
            ((b.equiv b' (Equiv.refl (Fin 3 ⊕ Fin 3))) (b q)) =
          polar (Q.restrict A) (b p) (b q)
        rw [hval p, hval q, polar_restrict, polar_restrict]
        rcases p with i | i <;> rcases q with j | j
        · simp [hb, hb', hvv, hvv']
        · simp [hb, hb', hbf, hb'f, hp, hp']
        · rw [hb'f i, hb' j, hbf i, hb j, polar_comm Q (fB (v' i)),
            polar_comm Q (fA (v i)), hp' j i, hp j i]
        · simp [hbf, hb'f, hff, hff']
    intro x
    have := congrArg (fun Q' => Q' x) hEq
    simpa [QuadraticMap.comp_apply, restrict_apply] using this
  · intro i
    rw [← hb i, ← hb' i]
    exact hval (Sum.inl i)
  · intro i
    rw [← hbf i, ← hb'f i]
    exact hval (Sum.inr i)
  · have hmap : (b.equiv b' (Equiv.refl (Fin 3 ⊕ Fin 3))).toLinearMap.comp fA =
        fB.comp (b.equiv b' (Equiv.refl (Fin 3 ⊕ Fin 3))).toLinearMap := by
      refine b.ext fun p => ?_
      rcases p with i | i
      · show (b.equiv b' (Equiv.refl (Fin 3 ⊕ Fin 3))) (fA (b (Sum.inl i))) =
          fB ((b.equiv b' (Equiv.refl (Fin 3 ⊕ Fin 3))) (b (Sum.inl i)))
        rw [hb i, ← hbf i, hval (Sum.inr i), ← hb i, hval (Sum.inl i), hb' i, hb'f i]
      · show (b.equiv b' (Equiv.refl (Fin 3 ⊕ Fin 3))) (fA (b (Sum.inr i))) =
          fB ((b.equiv b' (Equiv.refl (Fin 3 ⊕ Fin 3))) (b (Sum.inr i)))
        rw [hbf i, hfA2 (v i), map_add]
        have h1 : (b.equiv b' (Equiv.refl (Fin 3 ⊕ Fin 3))) (v i) = v' i := by
          rw [← hb i, hval (Sum.inl i), hb' i]
        have h2 : (b.equiv b' (Equiv.refl (Fin 3 ⊕ Fin 3))) (fA (v i)) = fB (v' i) := by
          rw [← hbf i, hval (Sum.inr i), hb'f i]
        rw [h1, h2, hfB2 (v' i)]
    intro x
    exact congrFun (congrArg DFunLike.coe hmap) x

private theorem k328r8c5_conclude {F : Type} [Field F] [Fintype F] [CharP F 2] (b c : F)
    (hbc : ∀ s : F, s ^ 2 + b * s + c ≠ 0)
    {z z' g₁ : GL (Fin 3 ⊕ Fin 3 ⊕ Fin 2) F}
    (hzO : toLinEquiv (Fin 3 ⊕ Fin 3 ⊕ Fin 2) F z ∈ orthogonalGroup (quadMinus 4 F b c))
    (hg₁O : toLinEquiv (Fin 3 ⊕ Fin 3 ⊕ Fin 2) F g₁ ∈ orthogonalGroup (quadMinus 4 F b c))
    {a : Fin 3 ⊕ Fin 3 ⊕ Fin 2 → F}
    (hafix : a ∈ LinearMap.ker (K328R8L2.k328r8c_l2_fOf F z - 1))
    (hQa : quadMinus 4 F b c a = 1)
    (hzg : g₁ * z = z' * g₁) :
    ∃ g ∈ StatedOmega (StatedQuadMinus 4 F b c), g * z * g⁻¹ = z' := by
  obtain ⟨hnd, hT⟩ := regular_quadMinus (n := 4) (b := b) (c := c) (by norm_num) hbc
  have ha0 : quadMinus 4 F b c a ≠ 0 := by rw [hQa]; exact one_ne_zero
  have hza : K328R8L2.k328r8c_l2_fOf F z a = a := by
    have h := hafix
    rw [LinearMap.mem_ker] at h
    exact sub_eq_zero.mp h
  have hcomm : (toLinEquiv (Fin 3 ⊕ Fin 3 ⊕ Fin 2) F z) *
      reflect (quadMinus 4 F b c) a =
      reflect (quadMinus 4 F b c) a * (toLinEquiv (Fin 3 ⊕ Fin 3 ⊕ Fin 2) F z) := by
    have h := reflect_conj hzO a
    have hza' : (toLinEquiv (Fin 3 ⊕ Fin 3 ⊕ Fin 2) F) z a = a := hza
    rw [hza', mul_inv_eq_iff_eq_mul] at h
    exact h
  have hH : ∀ g : GL (Fin 3 ⊕ Fin 3 ⊕ Fin 2) F,
      toLinEquiv (Fin 3 ⊕ Fin 3 ⊕ Fin 2) F g ∈
        CFSG.RankThree.Classical2.orthDerived (quadMinus 4 F b c) →
      g ∈ StatedOmega (StatedQuadMinus 4 F b c) := fun g hg => by
    rw [statedOmega_eq_comap (coe_quadMinus 4 F b c), Subgroup.mem_comap]
    exact hg
  have hgz : g₁ * z * g₁⁻¹ = z' := by
    rw [hzg, mul_assoc, mul_inv_cancel, mul_one]
  rcases k328r8c_dickson hnd hT hg₁O ha0 with h | h
  · exact ⟨g₁, hH g₁ h, hgz⟩
  · set r : GL (Fin 3 ⊕ Fin 3 ⊕ Fin 2) F :=
      (toLinEquiv (Fin 3 ⊕ Fin 3 ⊕ Fin 2) F).symm (reflect (quadMinus 4 F b c) a) with hr
    have hrR : toLinEquiv (Fin 3 ⊕ Fin 3 ⊕ Fin 2) F r = reflect (quadMinus 4 F b c) a :=
      (toLinEquiv (Fin 3 ⊕ Fin 3 ⊕ Fin 2) F).apply_symm_apply _
    have hrcomm : r * z = z * r := (toLinEquiv (Fin 3 ⊕ Fin 3 ⊕ Fin 2) F).injective (by
      rw [map_mul, map_mul, hrR]
      exact hcomm.symm)
    have hgr : g₁ * r ∈ StatedOmega (StatedQuadMinus 4 F b c) :=
      hH _ (by rw [map_mul, hrR]; exact h)
    refine ⟨g₁ * r, hgr, ?_⟩
    calc (g₁ * r) * z * (g₁ * r)⁻¹ = g₁ * (r * z * r⁻¹) * g₁⁻¹ := by group
      _ = g₁ * z * g₁⁻¹ := by
          rw [show r * z * r⁻¹ = z from by rw [hrcomm, mul_assoc, mul_inv_cancel, mul_one]]
      _ = z' := hgz

private theorem k328r8c5_two_mul_eq_zero {F : Type} [Field F] [CharP F 2] (x : F) :
    (2 : F) * x = 0 := by
  rw [CharTwo.two_eq_zero, zero_mul]

private theorem k328r8c_conj_GL {F : Type} [Field F] [Fintype F] [DecidableEq F]
    (b c : F) (hF : Fintype.card F = 8)
    (hbc : ∀ s : F, s ^ 2 + b * s + c ≠ 0)
    {z z' : GL (Fin 3 ⊕ Fin 3 ⊕ Fin 2) F}
    (hzO : toLinEquiv (Fin 3 ⊕ Fin 3 ⊕ Fin 2) F z ∈ orthogonalGroup (quadMinus 4 F b c))
    (hz'O : toLinEquiv (Fin 3 ⊕ Fin 3 ⊕ Fin 2) F z' ∈ orthogonalGroup (quadMinus 4 F b c))
    (hz3 : z ^ 3 = 1) (hz'3 : z' ^ 3 = 1)
    (hFix : Module.finrank F (LinearMap.ker (K328R8L2.k328r8c_l2_fOf F z - 1)) = 2)
    (hFix' : Module.finrank F (LinearMap.ker (K328R8L2.k328r8c_l2_fOf F z' - 1)) = 2) :
    ∃ g ∈ StatedOmega (StatedQuadMinus 4 F b c), g * z * g⁻¹ = z' := by
  refine (letI : CharP F 2 :=
    charP_of_card_eq_prime_pow (show Fintype.card F = 2 ^ 3 by rw [hF]; norm_num); ?_)
  have hWfr := k328r8c5_finrank_W z hz3 hFix
  have hWfr' := k328r8c5_finrank_W z' hz'3 hFix'
  obtain ⟨v, hvli, hvQ, hvp, hvv⟩ := k328r8c_frame_W b c hF hbc z hzO hz3 hWfr
  obtain ⟨v', hvli', hvQ', hvp', hvv'⟩ := k328r8c_frame_W b c hF hbc z' hz'O hz'3 hWfr'
  have hplus := k328r8c_fix_isPlusType b c hF hbc z hzO hz3 hFix
  have hplus' := k328r8c_fix_isPlusType b c hF hbc z' hz'O hz'3 hFix'
  obtain ⟨P, hPe, hPf⟩ := k328r8c5_hypPair_fix b c hbc z hzO hz3 hFix hplus
  obtain ⟨P', hP'e, hP'f⟩ := k328r8c5_hypPair_fix b c hbc z' hz'O hz'3 hFix' hplus'
  let Fix : Submodule F (Fin 3 ⊕ Fin 3 ⊕ Fin 2 → F) :=
    LinearMap.ker (K328R8L2.k328r8c_l2_fOf F z - 1)
  let Fix' : Submodule F (Fin 3 ⊕ Fin 3 ⊕ Fin 2 → F) :=
    LinearMap.ker (K328R8L2.k328r8c_l2_fOf F z' - 1)
  let W : Submodule F (Fin 3 ⊕ Fin 3 ⊕ Fin 2 → F) := K328R8L2.k328r8c_l2_W F z
  let W' : Submodule F (Fin 3 ⊕ Fin 3 ⊕ Fin 2 → F) := K328R8L2.k328r8c_l2_W F z'
  have hZ3 : (K328R8L2.k328r8c_l2_fOf F z) ^ 3 = 1 := by
    rw [← K328R8L2.k328r8c_l2_fOf_pow, hz3, K328R8L2.k328r8c_l2_fOf_one]
  have hZ'3 : (K328R8L2.k328r8c_l2_fOf F z') ^ 3 = 1 := by
    rw [← K328R8L2.k328r8c_l2_fOf_pow, hz'3, K328R8L2.k328r8c_l2_fOf_one]
  have hcompl : IsCompl Fix W :=
    k328r8c_isCompl_fix_move (V := Fin 3 ⊕ Fin 3 ⊕ Fin 2 → F)
      (Z := K328R8L2.k328r8c_l2_fOf F z) hZ3
  have hcompl' : IsCompl Fix' W' :=
    k328r8c_isCompl_fix_move (V := Fin 3 ⊕ Fin 3 ⊕ Fin 2 → F)
      (Z := K328R8L2.k328r8c_l2_fOf F z') hZ'3
  have hQfv : ∀ i, quadMinus 4 F b c ((K328R8L2.k328r8c_l2_fW F z) (v i)) = 1 := by
    intro i
    have h1 : quadMinus 4 F b c ((K328R8L2.k328r8c_l2_fW F z) (v i)) =
        polar (quadMinus 4 F b c) (v i) ((K328R8L2.k328r8c_l2_fW F z) (v i)) := by
      rw [k328r8c_Q_eq_polar b c z hzO (K328R8L2.k328r8c_l2_fW F z (v i)),
        k328r8c_l2_fW_sq (z := z) (v i), Submodule.coe_add, polar_add_right,
        polar_self_eq_two_mul, k328r8c5_two_mul_eq_zero, add_zero]
      exact polar_comm (quadMinus 4 F b c) _ _
    rw [h1, hvp i i, if_pos rfl]
  have hQfv' : ∀ i, quadMinus 4 F b c ((K328R8L2.k328r8c_l2_fW F z') (v' i)) = 1 := by
    intro i
    have h1 : quadMinus 4 F b c ((K328R8L2.k328r8c_l2_fW F z') (v' i)) =
        polar (quadMinus 4 F b c) (v' i) ((K328R8L2.k328r8c_l2_fW F z') (v' i)) := by
      rw [k328r8c_Q_eq_polar b c z' hz'O (K328R8L2.k328r8c_l2_fW F z' (v' i)),
        k328r8c_l2_fW_sq (z := z') (v' i), Submodule.coe_add, polar_add_right,
        polar_self_eq_two_mul, k328r8c5_two_mul_eq_zero, add_zero]
      exact polar_comm (quadMinus 4 F b c) _ _
    rw [h1, hvp' i i, if_pos rfl]
  have hff : ∀ i j, polar (quadMinus 4 F b c)
      ((K328R8L2.k328r8c_l2_fW F z) (v i)) ((K328R8L2.k328r8c_l2_fW F z) (v j)) = 0 :=
    fun i j => by rw [k328r8c_l2_polar_fW_fW b c z hzO (v i) (v j), hvv i j]
  have hff' : ∀ i j, polar (quadMinus 4 F b c)
      ((K328R8L2.k328r8c_l2_fW F z') (v' i)) ((K328R8L2.k328r8c_l2_fW F z') (v' j)) = 0 :=
    fun i j => by rw [k328r8c_l2_polar_fW_fW b c z' hz'O (v' i) (v' j), hvv' i j]
  obtain ⟨gFix, hgFixQ, hgFixPe, hgFixPf⟩ :=
    k328r8c5_gFix (Q := quadMinus 4 F b c) (A := Fix) (B := Fix') P P'
      hPe hPf hP'e hP'f hFix hFix'
  obtain ⟨gW, hgWQ, hgWv, hgWfv, hgWcomm⟩ :=
    k328r8c5_gW (Q := quadMinus 4 F b c) (A := W) (B := W')
      (K328R8L2.k328r8c_l2_fW F z) (K328R8L2.k328r8c_l2_fW F z')
      v v' hvli hvli' hWfr hWfr' hvQ hvQ' hQfv hQfv' hvp hvp' hvv hvv' hff hff'
      (k328r8c_l2_fW_sq (z := z)) (k328r8c_l2_fW_sq (z := z'))
  let g₀ : (Fin 3 ⊕ Fin 3 ⊕ Fin 2 → F) ≃ₗ[F] (Fin 3 ⊕ Fin 3 ⊕ Fin 2 → F) :=
    (Submodule.prodEquivOfIsCompl Fix W hcompl).symm ≪≫ₗ
      (gFix.prodCongr gW) ≪≫ₗ
      (Submodule.prodEquivOfIsCompl Fix' W' hcompl')
  have hgFixV : ∀ xF : Fix, g₀ (xF : Fin 3 ⊕ Fin 3 ⊕ Fin 2 → F) =
      (gFix xF : Fin 3 ⊕ Fin 3 ⊕ Fin 2 → F) := by
    intro xF
    dsimp only [g₀]
    rw [LinearEquiv.trans_apply, LinearEquiv.trans_apply,
      Submodule.prodEquivOfIsCompl_symm_apply_left Fix W hcompl xF,
      LinearEquiv.prodCongr_apply]
    rw [show gW 0 = 0 from gW.map_zero]
    rw [Submodule.coe_prodEquivOfIsCompl' Fix' W' hcompl' (gFix xF, 0), Submodule.coe_zero,
      add_zero]
  have hgWV : ∀ xW : W, g₀ (xW : Fin 3 ⊕ Fin 3 ⊕ Fin 2 → F) =
      (gW xW : Fin 3 ⊕ Fin 3 ⊕ Fin 2 → F) := by
    intro xW
    dsimp only [g₀]
    rw [LinearEquiv.trans_apply, LinearEquiv.trans_apply,
      Submodule.prodEquivOfIsCompl_symm_apply_right Fix W hcompl xW,
      LinearEquiv.prodCongr_apply]
    rw [show gFix 0 = 0 from gFix.map_zero]
    rw [Submodule.coe_prodEquivOfIsCompl' Fix' W' hcompl' (0, gW xW), Submodule.coe_zero,
      zero_add]
  have hdecomp : ∀ x : Fin 3 ⊕ Fin 3 ⊕ Fin 2 → F,
      x = (((Submodule.prodEquivOfIsCompl Fix W hcompl).symm x).1 :
          Fin 3 ⊕ Fin 3 ⊕ Fin 2 → F) +
        (((Submodule.prodEquivOfIsCompl Fix W hcompl).symm x).2 :
          Fin 3 ⊕ Fin 3 ⊕ Fin 2 → F) := by
    intro x
    conv_lhs => rw [← (Submodule.prodEquivOfIsCompl Fix W hcompl).apply_symm_apply x]
    exact Submodule.coe_prodEquivOfIsCompl' Fix W hcompl _
  have hg₀Q : ∀ x, quadMinus 4 F b c (g₀ x) = quadMinus 4 F b c x := by
    intro x
    let xF : Fix := ((Submodule.prodEquivOfIsCompl Fix W hcompl).symm x).1
    let xW : W := ((Submodule.prodEquivOfIsCompl Fix W hcompl).symm x).2
    have hx : x = (xF : Fin 3 ⊕ Fin 3 ⊕ Fin 2 → F) +
        (xW : Fin 3 ⊕ Fin 3 ⊕ Fin 2 → F) := by
      dsimp only [xF, xW]
      conv_lhs => rw [← (Submodule.prodEquivOfIsCompl Fix W hcompl).apply_symm_apply x]
      exact Submodule.coe_prodEquivOfIsCompl' Fix W hcompl _
    have hgx : g₀ ((xF : Fin 3 ⊕ Fin 3 ⊕ Fin 2 → F) +
        (xW : Fin 3 ⊕ Fin 3 ⊕ Fin 2 → F)) =
        (gFix xF : Fin 3 ⊕ Fin 3 ⊕ Fin 2 → F) +
          (gW xW : Fin 3 ⊕ Fin 3 ⊕ Fin 2 → F) := by
      rw [map_add, hgFixV xF, hgWV xW]
    rw [hx, hgx, QuadraticMap.map_add (quadMinus 4 F b c),
      QuadraticMap.map_add (quadMinus 4 F b c), hgFixQ xF, hgWQ xW,
      k328r8c_polar_fix_W b c z' hz'O (gFix xF).2 (m := gW xW),
      k328r8c_polar_fix_W b c z hzO xF.2 (m := xW)]
  have hg₀O : g₀ ∈ orthogonalGroup (quadMinus 4 F b c) :=
    TauCeti.QuadraticMap.mem_orthogonalGroup_iff.2 hg₀Q
  have hg₀z : ∀ x, g₀ (K328R8L2.k328r8c_l2_fOf F z x) =
      K328R8L2.k328r8c_l2_fOf F z' (g₀ x) := by
    intro x
    let xF : Fix := ((Submodule.prodEquivOfIsCompl Fix W hcompl).symm x).1
    let xW : W := ((Submodule.prodEquivOfIsCompl Fix W hcompl).symm x).2
    have hx : x = (xF : Fin 3 ⊕ Fin 3 ⊕ Fin 2 → F) +
        (xW : Fin 3 ⊕ Fin 3 ⊕ Fin 2 → F) := by
      dsimp only [xF, xW]
      conv_lhs => rw [← (Submodule.prodEquivOfIsCompl Fix W hcompl).apply_symm_apply x]
      exact Submodule.coe_prodEquivOfIsCompl' Fix W hcompl _
    have hfix : K328R8L2.k328r8c_l2_fOf F z (xF : Fin 3 ⊕ Fin 3 ⊕ Fin 2 → F) =
        (xF : Fin 3 ⊕ Fin 3 ⊕ Fin 2 → F) := by
      have h := xF.2
      rw [LinearMap.mem_ker] at h
      exact sub_eq_zero.mp h
    have hfix' : K328R8L2.k328r8c_l2_fOf F z'
        (gFix xF : Fin 3 ⊕ Fin 3 ⊕ Fin 2 → F) =
        (gFix xF : Fin 3 ⊕ Fin 3 ⊕ Fin 2 → F) := by
      have h := (gFix xF).2
      rw [LinearMap.mem_ker] at h
      exact sub_eq_zero.mp h
    have hmove : K328R8L2.k328r8c_l2_fOf F z (xW : Fin 3 ⊕ Fin 3 ⊕ Fin 2 → F) =
        ((K328R8L2.k328r8c_l2_fW F z) xW : Fin 3 ⊕ Fin 3 ⊕ Fin 2 → F) :=
      (k328r8c_l2_fW_coe z xW).symm
    have hmove' : K328R8L2.k328r8c_l2_fOf F z'
        (gW xW : Fin 3 ⊕ Fin 3 ⊕ Fin 2 → F) =
        ((K328R8L2.k328r8c_l2_fW F z') (gW xW) : Fin 3 ⊕ Fin 3 ⊕ Fin 2 → F) :=
      (k328r8c_l2_fW_coe z' (gW xW)).symm
    have hgx : g₀ ((xF : Fin 3 ⊕ Fin 3 ⊕ Fin 2 → F) +
        (xW : Fin 3 ⊕ Fin 3 ⊕ Fin 2 → F)) =
        (gFix xF : Fin 3 ⊕ Fin 3 ⊕ Fin 2 → F) +
          (gW xW : Fin 3 ⊕ Fin 3 ⊕ Fin 2 → F) := by
      rw [map_add, hgFixV xF, hgWV xW]
    have hL : g₀ (K328R8L2.k328r8c_l2_fOf F z x) =
        (gFix xF : Fin 3 ⊕ Fin 3 ⊕ Fin 2 → F) +
          (gW ((K328R8L2.k328r8c_l2_fW F z) xW) : Fin 3 ⊕ Fin 3 ⊕ Fin 2 → F) := by
      rw [hx, map_add, hfix, hmove, map_add, hgFixV xF,
        hgWV ((K328R8L2.k328r8c_l2_fW F z) xW)]
    have hR : K328R8L2.k328r8c_l2_fOf F z' (g₀ x) =
        (gFix xF : Fin 3 ⊕ Fin 3 ⊕ Fin 2 → F) +
          (gW ((K328R8L2.k328r8c_l2_fW F z) xW) : Fin 3 ⊕ Fin 3 ⊕ Fin 2 → F) := by
      rw [hx, hgx, map_add, hfix', hmove', hgWcomm xW]
    rw [hL, hR]
  let g₁ : GL (Fin 3 ⊕ Fin 3 ⊕ Fin 2) F :=
    (toLinEquiv (Fin 3 ⊕ Fin 3 ⊕ Fin 2) F).symm g₀
  have hg₁ : toLinEquiv (Fin 3 ⊕ Fin 3 ⊕ Fin 2) F g₁ = g₀ :=
    (toLinEquiv (Fin 3 ⊕ Fin 3 ⊕ Fin 2) F).apply_symm_apply g₀
  have hg₁O : toLinEquiv (Fin 3 ⊕ Fin 3 ⊕ Fin 2) F g₁ ∈
      orthogonalGroup (quadMinus 4 F b c) := by rw [hg₁]; exact hg₀O
  have hzgGL : g₁ * z = z' * g₁ := by
    apply (toLinEquiv (Fin 3 ⊕ Fin 3 ⊕ Fin 2) F).injective
    rw [map_mul, map_mul, hg₁]
    exact LinearEquiv.ext fun x => hg₀z x
  refine k328r8c5_conclude (a := P.e + P.f) b c hbc hzO hg₁O ?_ ?_ hzgGL
  · exact Submodule.add_mem _ hPe hPf
  · rw [QuadraticMap.map_add (quadMinus 4 F b c), P.Q_e, P.Q_f, P.polar_ef]
    norm_num

private abbrev k328r8cz_zc (F : Type) [Field F] [Fintype F] [DecidableEq F] (b c α : F) :
    Fin 3 ⊕ Fin 3 ⊕ Fin 2 → (Fin 3 ⊕ Fin 3 ⊕ Fin 2 → F) :=
  Sum.elim ![bv F (Sum.inl 0) + bv F (Sum.inr (Sum.inl 1)),
              bv F (Sum.inr (Sum.inl 0)) + bv F (Sum.inl 1), bv F (Sum.inl 2)]
    (Sum.elim ![bv F (Sum.inl 1), bv F (Sum.inl 0), bv F (Sum.inr (Sum.inl 2))]
      ![α • bv F (Sum.inr (Sum.inr 0)) + b⁻¹ • bv F (Sum.inr (Sum.inr 1)),
        (c / b) • bv F (Sum.inr (Sum.inr 0)) + (α + 1) • bv F (Sum.inr (Sum.inr 1))])

private def k328r8cz_zmat (F : Type) [Field F] [Fintype F] [DecidableEq F] (b c α : F) :
    Matrix (Fin 3 ⊕ Fin 3 ⊕ Fin 2) (Fin 3 ⊕ Fin 3 ⊕ Fin 2) F :=
  ofColumns F (k328r8cz_zc F b c α)

private def k328r8cz_zrow (F : Type) [Field F] [Fintype F] [DecidableEq F] (b c α : F)
    (x : Fin 3 ⊕ Fin 3 ⊕ Fin 2 → F) : Fin 3 ⊕ Fin 3 ⊕ Fin 2 → F :=
  Sum.elim
    ![(x (Sum.inl 0) + x (Sum.inr (Sum.inl 1))), (x (Sum.inl 1) + x (Sum.inr (Sum.inl 0))),
      x (Sum.inl 2)]
    (Sum.elim
      ![x (Sum.inl 1), x (Sum.inl 0), x (Sum.inr (Sum.inl 2))]
      ![(α * x (Sum.inr (Sum.inr 0)) + (c / b) * x (Sum.inr (Sum.inr 1))),
        b⁻¹ * x (Sum.inr (Sum.inr 0)) + (α + 1) * x (Sum.inr (Sum.inr 1))])

private theorem k328r8cz_matZ_row (F : Type) [Field F] [Fintype F] [DecidableEq F] (b c α : F)
    (x : Fin 3 ⊕ Fin 3 ⊕ Fin 2 → F) :
    Matrix.mulVec (k328r8cz_zmat F b c α) x = k328r8cz_zrow F b c α x := by
  funext r
  fin_cases r <;>
    simp [k328r8cz_zmat, k328r8cz_zc, k328r8cz_zrow, ofColumns, Matrix.mulVec, dotProduct,
      Fintype.sum_sum_type, Fin.sum_univ_three, Fin.sum_univ_two, Matrix.of_apply, bv,
      Sum.elim_inl, Sum.elim_inr, Pi.add_apply, Pi.smul_apply,
      Matrix.cons_val, Sum.inl.injEq, Sum.inr.injEq, Sum.inl_ne_inr, Sum.inr_ne_inl]

private theorem k328r8cz_ofColumns_mulVec_single (F : Type) [Field F] [Fintype F] [DecidableEq F]
    {ι : Type} [Fintype ι] [DecidableEq ι] (img : ι → ι → F) (k : ι) :
    Matrix.mulVec (ofColumns F img) (Pi.single k 1 : ι → F) = img k := by
  rw [Matrix.mulVec_single_one]
  funext i
  simp [ofColumns]

private theorem k328r8cz_mulVec_id_eq_one {F : Type} [Field F] [Fintype F] [DecidableEq F]
    {M : Matrix (Fin 3 ⊕ Fin 3 ⊕ Fin 2) (Fin 3 ⊕ Fin 3 ⊕ Fin 2) F}
    (h : ∀ x, Matrix.mulVec M x = x) :
    M = 1 := by
  ext r k
  have hh := congrFun (h (Pi.single k 1)) r
  rw [Matrix.mulVec_single_one] at hh
  simpa [Matrix.one_apply, Pi.single_apply] using hh

private theorem k328r8cz_ofNat_mod2 (F : Type) [Field F] [Fintype F] [DecidableEq F] [CharP F 2]
    (n : ℕ) [n.AtLeastTwo] : (OfNat.ofNat n : F) = ((n % 2 : ℕ) : F) := by
  rw [show (OfNat.ofNat n : F) = ((n : ℕ) : F) from rfl]
  exact (CharP.natCast_eq_natCast (R := F) (p := 2) (a := n) (b := n % 2)).mpr
    (Nat.mod_mod n 2).symm

private theorem k328r8cz_hc (F : Type) [Field F] [Fintype F] [DecidableEq F] (b c α : F) [CharP F 2]
    (hα : α ^ 2 + α = 1 + c / b ^ 2) (hb : b ≠ 0) :
    c = b ^ 2 * (α ^ 2 + α + 1) := by
  have h := hα
  rw [div_eq_mul_inv] at h
  have hm : b ^ 2 * (α ^ 2 + α) = b ^ 2 + c := by
    rw [h]; field_simp [hb]
  rw [mul_add, mul_one, hm]
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  linear_combination (-(b ^ 2)) * h2

private theorem k328r8cz_zrow_triple (F : Type) [Field F] [Fintype F] [DecidableEq F] (b c α : F)
    [CharP F 2] (hα : α ^ 2 + α = 1 + c / b ^ 2) (hb : b ≠ 0)
    (x : Fin 3 ⊕ Fin 3 ⊕ Fin 2 → F) :
    k328r8cz_zrow F b c α (k328r8cz_zrow F b c α (k328r8cz_zrow F b c α x)) = x := by
  funext r
  fin_cases r <;> simp [k328r8cz_zrow, Sum.elim_inl, Sum.elim_inr, Matrix.cons_val]
  all_goals (
    try rw [k328r8cz_hc F b c α hα hb]
    try rw [show b⁻¹ ^ 2 = (b ^ 2)⁻¹ from inv_pow b 2]
    try field_simp [hb]
    try ring_nf
    try simp only [k328r8cz_ofNat_mod2 F, Nat.reduceMod, Nat.cast_zero, Nat.cast_one]
    try ring_nf)

private theorem k328r8cz_zmat_cube (F : Type) [Field F] [Fintype F] [DecidableEq F] (b c α : F)
    [CharP F 2] (hα : α ^ 2 + α = 1 + c / b ^ 2) (hb : b ≠ 0) :
    k328r8cz_zmat F b c α ^ 3 = 1 := by
  apply k328r8cz_mulVec_id_eq_one
  intro x
  have hrow := k328r8cz_matZ_row F b c α
  have htriple := k328r8cz_zrow_triple F b c α hα hb
  have : Matrix.mulVec (k328r8cz_zmat F b c α)
      (Matrix.mulVec (k328r8cz_zmat F b c α)
        (Matrix.mulVec (k328r8cz_zmat F b c α) x)) = x := by
    simp only [hrow]; exact htriple x
  simpa only [pow_succ, pow_zero, one_mul, mul_assoc, Matrix.mulVec_mulVec,
    Matrix.one_mulVec] using this

private theorem k328r8cz_zmat_ne_one (F : Type) [Field F] [Fintype F] [DecidableEq F] (b c α : F) :
    k328r8cz_zmat F b c α ≠ 1 := by
  intro h
  have hval : Matrix.mulVec (k328r8cz_zmat F b c α) (bv F (Sum.inl 0))
      (Sum.inr (Sum.inl 1)) = 1 := by
    rw [k328r8cz_matZ_row]
    simp [k328r8cz_zrow, bv]
  rw [h, Matrix.one_mulVec] at hval
  simp [bv] at hval

private theorem k328r8cz_fOf_apply (F : Type) [Field F] [Fintype F] [DecidableEq F]
    (z : GL (Fin 3 ⊕ Fin 3 ⊕ Fin 2) F) (v : Fin 3 ⊕ Fin 3 ⊕ Fin 2 → F) :
    K328R8L2.k328r8c_l2_fOf F z v = Matrix.mulVec (z : Matrix _ _ F) v := by
  simp only [K328R8L2.k328r8c_l2_fOf, Matrix.GeneralLinearGroup.toLin_apply,
    Matrix.mulVecLin_apply]

private theorem k328r8c_z0_orderOf {F : Type} [Field F] [Fintype F] [DecidableEq F]
    (hF : Fintype.card F = 8) (b c : F)
    (hbc : ∀ s : F, s ^ 2 + b * s + c ≠ 0) (α : F) (hα : α ^ 2 + α = 1 + c / b ^ 2)
    (z₀ : GL (Fin 3 ⊕ Fin 3 ⊕ Fin 2) F)
    (hz₀ : (z₀ : Matrix _ _ F) = ofColumns F
      (Sum.elim ![bv F (Sum.inl 0) + bv F (Sum.inr (Sum.inl 1)),
                  bv F (Sum.inr (Sum.inl 0)) + bv F (Sum.inl 1), bv F (Sum.inl 2)]
        (Sum.elim ![bv F (Sum.inl 1), bv F (Sum.inl 0), bv F (Sum.inr (Sum.inl 2))]
          ![α • bv F (Sum.inr (Sum.inr 0)) + b⁻¹ • bv F (Sum.inr (Sum.inr 1)),
            (c / b) • bv F (Sum.inr (Sum.inr 0)) + (α + 1) • bv F (Sum.inr (Sum.inr 1))]))) :
    orderOf z₀ = 3 := by
  have : CharP F 2 :=
    charP_of_card_eq_prime_pow (show Fintype.card F = 2 ^ 3 by rw [hF]; norm_num)
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  have hb : b ≠ 0 := by
    intro hb0
    obtain ⟨s, hs⟩ := FiniteField.isSquare_of_char_two (ringChar.eq F 2) c
    refine hbc s ?_
    rw [hb0, zero_mul, add_zero, hs]
    linear_combination (s ^ 2) * h2
  have hz : (z₀ : Matrix _ _ F) = k328r8cz_zmat F b c α := hz₀
  have hcube : z₀ ^ 3 = 1 := by
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, hz]
    exact k328r8cz_zmat_cube F b c α hα hb
  have hne : z₀ ≠ 1 := by
    intro h
    have h' : k328r8cz_zmat F b c α = 1 := by rw [← hz, h]; rfl
    exact k328r8cz_zmat_ne_one F b c α h'
  exact orderOf_eq_prime hcube hne

private theorem k328r8cz_z0_fix_e2 (F : Type) [Field F] [Fintype F] [DecidableEq F] (b c α : F)
    (z₀ : GL (Fin 3 ⊕ Fin 3 ⊕ Fin 2) F)
    (hz : (z₀ : Matrix _ _ F) = k328r8cz_zmat F b c α) :
    Matrix.mulVec (z₀ : Matrix (Fin 3 ⊕ Fin 3 ⊕ Fin 2) (Fin 3 ⊕ Fin 3 ⊕ Fin 2) F)
      (bv F (Sum.inl 2)) = bv F (Sum.inl 2) := by
  rw [hz]
  change Matrix.mulVec (ofColumns F (k328r8cz_zc F b c α)) (bv F (Sum.inl 2)) = bv F (Sum.inl 2)
  rw [show bv F (Sum.inl 2) = (Pi.single (Sum.inl 2) 1 : Fin 3 ⊕ Fin 3 ⊕ Fin 2 → F) from rfl,
    k328r8cz_ofColumns_mulVec_single]
  simp [k328r8cz_zc, bv]

private theorem k328r8cz_z0_fix_f2 (F : Type) [Field F] [Fintype F] [DecidableEq F] (b c α : F)
    (z₀ : GL (Fin 3 ⊕ Fin 3 ⊕ Fin 2) F)
    (hz : (z₀ : Matrix _ _ F) = k328r8cz_zmat F b c α) :
    Matrix.mulVec (z₀ : Matrix (Fin 3 ⊕ Fin 3 ⊕ Fin 2) (Fin 3 ⊕ Fin 3 ⊕ Fin 2) F)
      (bv F (Sum.inr (Sum.inl 2))) = bv F (Sum.inr (Sum.inl 2)) := by
  rw [hz]
  change Matrix.mulVec (ofColumns F (k328r8cz_zc F b c α)) (bv F (Sum.inr (Sum.inl 2))) =
    bv F (Sum.inr (Sum.inl 2))
  rw [show bv F (Sum.inr (Sum.inl 2)) =
      (Pi.single (Sum.inr (Sum.inl 2)) 1 : Fin 3 ⊕ Fin 3 ⊕ Fin 2 → F) from rfl,
    k328r8cz_ofColumns_mulVec_single]
  simp [k328r8cz_zc, bv]

private theorem k328r8cz_ker_eq_span (F : Type) [Field F] [Fintype F] [DecidableEq F]
    (b c α : F) [CharP F 2] (hα : α ^ 2 + α = 1 + c / b ^ 2) (hb : b ≠ 0)
    (z₀ : GL (Fin 3 ⊕ Fin 3 ⊕ Fin 2) F)
    (hz : (z₀ : Matrix _ _ F) = k328r8cz_zmat F b c α) :
    LinearMap.ker (K328R8L2.k328r8c_l2_fOf F z₀ - 1) =
      Submodule.span F {bv F (Sum.inl 2), bv F (Sum.inr (Sum.inl 2))} := by
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  apply le_antisymm
  · intro v hv
    rw [LinearMap.mem_ker] at hv
    have hzv : Matrix.mulVec (z₀ : Matrix _ _ F) v = v := by
      have h3 : K328R8L2.k328r8c_l2_fOf F z₀ v = v := by
        have := hv
        rw [LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero] at this
        exact this
      rwa [k328r8cz_fOf_apply] at h3
    have hzv' : Matrix.mulVec (k328r8cz_zmat F b c α) v = v := by
      rw [← hz]; exact hzv
    have hrow : k328r8cz_zrow F b c α v = v := by
      rw [← k328r8cz_matZ_row (F := F) b c α v]
      exact hzv'
    have h0 : v (Sum.inl 0) + v (Sum.inr (Sum.inl 1)) = v (Sum.inl 0) := by
      have := congrFun hrow (Sum.inl 0)
      simpa [k328r8cz_zrow] using this
    have h1 : v (Sum.inl 1) + v (Sum.inr (Sum.inl 0)) = v (Sum.inl 1) := by
      have := congrFun hrow (Sum.inl 1)
      simpa [k328r8cz_zrow] using this
    have h3 : v (Sum.inl 1) = v (Sum.inr (Sum.inl 0)) := by
      have := congrFun hrow (Sum.inr (Sum.inl 0))
      simpa [k328r8cz_zrow] using this
    have h4 : v (Sum.inl 0) = v (Sum.inr (Sum.inl 1)) := by
      have := congrFun hrow (Sum.inr (Sum.inl 1))
      simpa [k328r8cz_zrow] using this
    have h6 : α * v (Sum.inr (Sum.inr 0)) + (c / b) * v (Sum.inr (Sum.inr 1)) =
        v (Sum.inr (Sum.inr 0)) := by
      have := congrFun hrow (Sum.inr (Sum.inr 0))
      simpa [k328r8cz_zrow] using this
    have h7 : b⁻¹ * v (Sum.inr (Sum.inr 0)) + (α + 1) * v (Sum.inr (Sum.inr 1)) =
        v (Sum.inr (Sum.inr 1)) := by
      have := congrFun hrow (Sum.inr (Sum.inr 1))
      simpa [k328r8cz_zrow] using this
    have hy1 : v (Sum.inr (Sum.inl 1)) = 0 := by
      exact add_left_cancel (by rw [h0, add_zero])
    have hy0 : v (Sum.inr (Sum.inl 0)) = 0 := by
      exact add_left_cancel (by rw [h1, add_zero])
    have hx1 : v (Sum.inl 1) = 0 := by
      have h := h3; rw [hy0] at h; exact h
    have hx0 : v (Sum.inl 0) = 0 := by
      have h := h4; rw [hy1] at h; exact h
    have h6' : (α + 1) * v (Sum.inr (Sum.inr 0)) +
        (c / b) * v (Sum.inr (Sum.inr 1)) = 0 := by
      linear_combination h6 + (v (Sum.inr (Sum.inr 0))) * h2
    have h7' : b⁻¹ * v (Sum.inr (Sum.inr 0)) + α * v (Sum.inr (Sum.inr 1)) = 0 := by
      linear_combination h7
    have h6b : (α + 1) * v (Sum.inr (Sum.inr 0)) * b +
        c * v (Sum.inr (Sum.inr 1)) = 0 := by
      have h := h6'
      field_simp [hb] at h
      linear_combination h
    have h7b : v (Sum.inr (Sum.inr 0)) +
        α * v (Sum.inr (Sum.inr 1)) * b = 0 := by
      have h := h7'
      field_simp [hb] at h
      linear_combination h
    have hxu : v (Sum.inr (Sum.inr 0)) =
        α * v (Sum.inr (Sum.inr 1)) * b := by
      linear_combination -h7b + (v (Sum.inr (Sum.inr 0))) * h2
    have hmain : v (Sum.inr (Sum.inr 1)) * b ^ 2 = 0 := by
      have h := h6b
      rw [hxu, k328r8cz_hc F b c α hα hb] at h
      linear_combination h - ((α ^ 2 + α) * v (Sum.inr (Sum.inr 1)) * b ^ 2) * h2
    have hvv : v (Sum.inr (Sum.inr 1)) = 0 := by
      exact (mul_eq_zero.mp hmain).resolve_right (pow_ne_zero 2 hb)
    have huu : v (Sum.inr (Sum.inr 0)) = 0 := by
      have h := h7b
      rw [hvv, mul_zero, zero_mul, add_zero] at h
      exact h
    rw [Submodule.mem_span_pair]
    refine ⟨v (Sum.inl 2), v (Sum.inr (Sum.inl 2)), ?_⟩
    funext k
    rcases k with i | i | j
    · fin_cases i <;> simp [bv, hx0, hx1, Pi.smul_apply, Pi.add_apply]
    · fin_cases i <;> simp [bv, hy0, hy1, Pi.smul_apply, Pi.add_apply]
    · fin_cases j <;> simp [bv, huu, hvv, Pi.smul_apply, Pi.add_apply]
  · rw [Submodule.span_le]
    rintro x (rfl | rfl)
    · change (K328R8L2.k328r8c_l2_fOf F z₀ - 1) (bv F (Sum.inl 2)) = 0
      rw [LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero, k328r8cz_fOf_apply]
      exact k328r8cz_z0_fix_e2 F b c α z₀ hz
    · change (K328R8L2.k328r8c_l2_fOf F z₀ - 1) (bv F (Sum.inr (Sum.inl 2))) = 0
      rw [LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero, k328r8cz_fOf_apply]
      exact k328r8cz_z0_fix_f2 F b c α z₀ hz

private theorem k328r8c_z0_finrank_fix {F : Type} [Field F] [Fintype F] [DecidableEq F]
    (hF : Fintype.card F = 8) (b c : F)
    (hbc : ∀ s : F, s ^ 2 + b * s + c ≠ 0) (α : F) (hα : α ^ 2 + α = 1 + c / b ^ 2)
    (z₀ : GL (Fin 3 ⊕ Fin 3 ⊕ Fin 2) F)
    (hz₀ : (z₀ : Matrix _ _ F) = ofColumns F
      (Sum.elim ![bv F (Sum.inl 0) + bv F (Sum.inr (Sum.inl 1)),
                  bv F (Sum.inr (Sum.inl 0)) + bv F (Sum.inl 1), bv F (Sum.inl 2)]
        (Sum.elim ![bv F (Sum.inl 1), bv F (Sum.inl 0), bv F (Sum.inr (Sum.inl 2))]
          ![α • bv F (Sum.inr (Sum.inr 0)) + b⁻¹ • bv F (Sum.inr (Sum.inr 1)),
            (c / b) • bv F (Sum.inr (Sum.inr 0)) + (α + 1) • bv F (Sum.inr (Sum.inr 1))]))) :
    Module.finrank F (LinearMap.ker (K328R8L2.k328r8c_l2_fOf F z₀ - 1)) = 2 := by
  have : CharP F 2 :=
    charP_of_card_eq_prime_pow (show Fintype.card F = 2 ^ 3 by rw [hF]; norm_num)
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  have hb : b ≠ 0 := by
    intro hb0
    obtain ⟨s, hs⟩ := FiniteField.isSquare_of_char_two (ringChar.eq F 2) c
    refine hbc s ?_
    rw [hb0, zero_mul, add_zero, hs]
    linear_combination (s ^ 2) * h2
  have hz : (z₀ : Matrix _ _ F) = k328r8cz_zmat F b c α := hz₀
  have hker := k328r8cz_ker_eq_span F b c α hα hb z₀ hz
  have hli : LinearIndependent F
      (![bv F (Sum.inl 2), bv F (Sum.inr (Sum.inl 2))] :
        Fin 2 → (Fin 3 ⊕ Fin 3 ⊕ Fin 2 → F)) := by
    rw [linearIndependent_fin2]
    constructor
    · intro hzero
      have := congrFun hzero (Sum.inr (Sum.inl 2))
      simp [bv] at this
    · intro a ha
      have h1 := congrFun ha (Sum.inr (Sum.inl 2))
      simp [bv] at h1
      have h2' := congrFun ha (Sum.inl 2)
      rw [h1] at h2'
      simp [bv] at h2'
  have hrange : Set.range (![bv F (Sum.inl 2), bv F (Sum.inr (Sum.inl 2))] :
      Fin 2 → (Fin 3 ⊕ Fin 3 ⊕ Fin 2 → F)) =
      {bv F (Sum.inl 2), bv F (Sum.inr (Sum.inl 2))} := by
    ext z
    simp [or_comm]
  rw [hker, ← hrange, finrank_span_eq_card hli]
  simp

theorem row8_class (F : Type) [Field F] [Fintype F] [DecidableEq F]
    (hF : Fintype.card F = 8) (b c : F)
    (hbc : ∀ s : F, s ^ 2 + b * s + c ≠ 0) (α : F) (hα : α ^ 2 + α = 1 + c / b ^ 2) :
    let e : Fin 3 → (Fin 3 ⊕ Fin 3 ⊕ Fin 2 → F) := fun i => bv F (Sum.inl i)
    let f : Fin 3 → (Fin 3 ⊕ Fin 3 ⊕ Fin 2 → F) := fun i => bv F (Sum.inr (Sum.inl i))
    let u : Fin 3 ⊕ Fin 3 ⊕ Fin 2 → F := bv F (Sum.inr (Sum.inr 0))
    let v : Fin 3 ⊕ Fin 3 ⊕ Fin 2 → F := bv F (Sum.inr (Sum.inr 1))
    ∀ z₀ t₀ : GL (Fin 3 ⊕ Fin 3 ⊕ Fin 2) F,
    (z₀ : Matrix _ _ F) = ofColumns F (Sum.elim ![e 0 + f 1, f 0 + e 1, e 2]
      (Sum.elim ![e 1, e 0, f 2] ![α • u + b⁻¹ • v, (c / b) • u + (α + 1) • v])) →
    (t₀ : Matrix _ _ F) = ofColumns F (Sum.elim ![e 1, e 0 + e 1, e 2]
      (Sum.elim ![f 0 + f 1, f 0, f 2] ![u, v])) →
    ClassLeaf (StatedOmega (StatedQuadMinus 4 F b c)) z₀ := by
  intro e f u v z₀ t₀ hz₀ ht₀
  unfold ClassLeaf
  intro z hzH hz3 X hXH hzX hXC hXperf
  have hzO : toLinEquiv (Fin 3 ⊕ Fin 3 ⊕ Fin 2) F z ∈ orthogonalGroup (quadMinus 4 F b c) :=
    k328r8c_mem_orth b c hzH
  have hz3' : z ^ 3 = 1 := by simpa [hz3] using pow_orderOf_eq_one z
  have hFix := k328r8c_finrank_fix_eq_two hF b c hbc α hα hz3 hzX hXC hXperf
  have hz₀' : (z₀ : Matrix _ _ F) = ofColumns F
      (Sum.elim ![bv F (Sum.inl 0) + bv F (Sum.inr (Sum.inl 1)),
                  bv F (Sum.inr (Sum.inl 0)) + bv F (Sum.inl 1), bv F (Sum.inl 2)]
        (Sum.elim ![bv F (Sum.inl 1), bv F (Sum.inl 0), bv F (Sum.inr (Sum.inl 2))]
          ![α • bv F (Sum.inr (Sum.inr 0)) + b⁻¹ • bv F (Sum.inr (Sum.inr 1)),
            (c / b) • bv F (Sum.inr (Sum.inr 0)) +
              (α + 1) • bv F (Sum.inr (Sum.inr 1))])) := by
    simpa only [e, f, u, v] using hz₀
  have hz₀O := k328r8c_z0_isom hF b c hbc α hα z₀ hz₀'
  have hz₀3 := k328r8c_z0_orderOf hF b c hbc α hα z₀ hz₀'
  have hz₀3' : z₀ ^ 3 = 1 := by simpa [hz₀3] using pow_orderOf_eq_one z₀
  have hFix₀ := k328r8c_z0_finrank_fix hF b c hbc α hα z₀ hz₀'
  obtain ⟨g, hgH, hgz⟩ := k328r8c_conj_GL b c hF hbc hzO hz₀O hz3' hz₀3' hFix hFix₀
  exact ⟨g, hgH, Or.inl hgz⟩

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.K328

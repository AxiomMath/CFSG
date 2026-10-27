module

public import Mathlib.RingTheory.SimpleModule.WedderburnArtin
public import Mathlib.RepresentationTheory.Maschke
public import Mathlib.RingTheory.LittleWedderburn
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs

public section

namespace CFSG.StandardType

namespace LayerCores

open Matrix

variable {F : Type} [Field F] {ι : Type} [Fintype ι] [DecidableEq ι]

@[expose] noncomputable def commRho (A : Subgroup (GL ι F)) : Representation F A (ι → F) :=
  (Matrix.toLinAlgEquiv' : Matrix ι ι F ≃ₐ[F] Module.End F (ι → F)).toMonoidHom.comp
    ((Units.coeHom (Matrix ι ι F)).comp A.subtype)

theorem commRho_apply (A : Subgroup (GL ι F)) (g : A) :
    commRho A g = Matrix.toLinAlgEquiv' ((g : GL ι F) : Matrix ι ι F) := rfl

@[expose] noncomputable def commEndRestrict (A : Subgroup (GL ι F)) :
    Module.End (MonoidAlgebra F A) (commRho A).asModule →ₐ[F] Module.End F (ι → F) where
  toFun f := f.restrictScalars F
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
  commutes' _ := by
    ext v
    rfl

theorem commEndRestrict_injective (A : Subgroup (GL ι F)) :
    Function.Injective (commEndRestrict A) :=
  LinearMap.restrictScalars_injective F

theorem commute_commRho_asAlgebraHom (A : Subgroup (GL ι F)) {X : Module.End F (ι → F)}
    (hX : ∀ g : A, Commute X (commRho A g)) (r : MonoidAlgebra F A) :
    Commute X ((commRho A).asAlgebraHom r) := by
  induction r using MonoidAlgebra.induction_on with
  | of g => rw [Representation.asAlgebraHom_of]; exact hX g
  | add a b ha hb => rw [map_add]; exact ha.add_right hb
  | smul c a ha => rw [map_smul]; exact ha.smul_right c

theorem mem_range_commEndRestrict (A : Subgroup (GL ι F)) (X : Module.End F (ι → F)) :
    X ∈ Set.range (commEndRestrict A) ↔ ∀ g : A, Commute X (commRho A g) := by
  constructor
  · rintro ⟨f, rfl⟩ g
    refine LinearMap.ext fun v => ?_
    have h := f.map_smul (MonoidAlgebra.of F A g) ((commRho A).asModuleEquiv.symm v)
    rw [← Representation.asModuleEquiv_symm_map_rho] at h
    have h2 := congrArg (commRho A).asModuleEquiv h
    rw [Representation.asModuleEquiv_map_smul, Representation.asAlgebraHom_of] at h2
    exact h2
  · intro hX
    refine ⟨{ toFun := X, map_add' := X.map_add, map_smul' := fun r v => ?_ }, rfl⟩
    exact LinearMap.congr_fun (commute_commRho_asAlgebraHom A hX r).eq v

theorem exists_algHom_pi_matrix_commutant [Finite F] (A : Subgroup (GL ι F))
    (hA : (Nat.card A : F) ≠ 0) :
    ∃ (r : ℕ) (D : Fin r → Type) (d : Fin r → ℕ) (_ : ∀ i, Field (D i)) (_ : ∀ i, Finite (D i))
      (_ : ∀ i, Algebra F (D i)) (_ : ∀ i, NeZero (d i))
      (Φ : (∀ i, Matrix (Fin (d i)) (Fin (d i)) (D i)) →ₐ[F] Matrix ι ι F),
      Function.Injective Φ ∧ ∀ X : Matrix ι ι F, X ∈ Set.range Φ ↔
        ∀ g ∈ A, X * (g : Matrix ι ι F) = (g : Matrix ι ι F) * X := by
  have : NeZero (Nat.card A : F) := ⟨hA⟩
  have : Module.Finite (MonoidAlgebra F A) (commRho A).asModule :=
    Module.Finite.of_restrictScalars_finite F (MonoidAlgebra F A) (commRho A).asModule
  have : IsSemisimpleRing (Module.End (MonoidAlgebra F A) (commRho A).asModule) :=
    IsSemisimpleRing.moduleEnd (MonoidAlgebra F A) (commRho A).asModule
  have : Module.Finite F (Module.End (MonoidAlgebra F A) (commRho A).asModule) :=
    Module.Finite.of_injective (LinearMap.restrictScalarsₗ F (MonoidAlgebra F A) _ _ F)
      (LinearMap.restrictScalars_injective F)
  obtain ⟨r, D, d, _, _, _, hd, ⟨e⟩⟩ :=
    IsSemisimpleRing.exists_algEquiv_pi_matrix_divisionRing_finite F
      (Module.End (MonoidAlgebra F A) (commRho A).asModule)
  have hfin : ∀ i, Finite (D i) := fun i => Module.finite_of_finite F
  let Φ : (Π i, Matrix (Fin (d i)) (Fin (d i)) (D i)) →ₐ[F] Matrix ι ι F :=
    ((LinearMap.toMatrixAlgEquiv' : Module.End F (ι → F) ≃ₐ[F] _).toAlgHom.comp
      (commEndRestrict A)).comp e.symm.toAlgHom
  have hΦinj : Function.Injective Φ :=
    (LinearMap.toMatrixAlgEquiv'.injective.comp (commEndRestrict_injective A)).comp
      e.symm.injective
  refine ⟨r, D, d, fun i => littleWedderburn (D i), hfin, inferInstance, hd, Φ, hΦinj,
    fun X => ?_⟩
  constructor
  · rintro ⟨y, rfl⟩ g hg
    have h := (mem_range_commEndRestrict A _).mp ⟨e.symm y, rfl⟩ ⟨g, hg⟩
    have h2 := congrArg (LinearMap.toMatrixAlgEquiv' : Module.End F (ι → F) ≃ₐ[F] _) h.eq
    rw [map_mul, map_mul, commRho_apply, ← Matrix.toLinAlgEquiv'_symm] at h2
    simpa [Φ] using h2
  · intro hX
    obtain ⟨f, hf⟩ := (mem_range_commEndRestrict A (Matrix.toLinAlgEquiv' X)).mpr fun g => by
      rw [commRho_apply]
      show _ * _ = _ * _
      rw [← map_mul, ← map_mul, hX g g.2]
    refine ⟨e f, ?_⟩
    show LinearMap.toMatrixAlgEquiv' (commEndRestrict A (e.symm (e f))) = X
    rw [e.symm_apply_apply, hf]
    exact LinearMap.toMatrixAlgEquiv'_toLinAlgEquiv' X

end LayerCores

end CFSG.StandardType

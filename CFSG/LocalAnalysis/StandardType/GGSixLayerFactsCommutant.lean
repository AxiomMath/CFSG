module

public import Mathlib.RingTheory.SimpleModule.WedderburnArtin
public import Mathlib.RepresentationTheory.Maschke
public import Mathlib.RingTheory.LittleWedderburn
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.Algebra.Group.Pi.Units

public section

namespace CFSG.StandardType

namespace LayerFacts

open Matrix

variable {F : Type} [Field F] {n : ℕ}

@[expose] noncomputable def rhoOf (A : Subgroup (GL (Fin n) F)) : Representation F A (Fin n → F) :=
  (Matrix.toLinAlgEquiv' :
      Matrix (Fin n) (Fin n) F ≃ₐ[F] Module.End F (Fin n → F)).toMonoidHom.comp
    ((Units.coeHom (Matrix (Fin n) (Fin n) F)).comp A.subtype)

theorem rhoOf_apply (A : Subgroup (GL (Fin n) F)) (g : A) :
    rhoOf A g = Matrix.toLinAlgEquiv' ((g : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) := rfl

@[expose] noncomputable def endRestrict (A : Subgroup (GL (Fin n) F)) :
    Module.End (MonoidAlgebra F A) (rhoOf A).asModule →ₐ[F] Module.End F (Fin n → F) where
  toFun f := f.restrictScalars F
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
  commutes' _ := by
    ext v
    rfl

theorem endRestrict_injective (A : Subgroup (GL (Fin n) F)) :
    Function.Injective (endRestrict A) :=
  LinearMap.restrictScalars_injective F

theorem commute_asAlgebraHom (A : Subgroup (GL (Fin n) F)) {X : Module.End F (Fin n → F)}
    (hX : ∀ g : A, Commute X (rhoOf A g)) (r : MonoidAlgebra F A) :
    Commute X ((rhoOf A).asAlgebraHom r) := by
  induction r using MonoidAlgebra.induction_on with
  | of g => rw [Representation.asAlgebraHom_of]; exact hX g
  | add a b ha hb => rw [map_add]; exact ha.add_right hb
  | smul c a ha => rw [map_smul]; exact ha.smul_right c

theorem mem_range_endRestrict (A : Subgroup (GL (Fin n) F)) (X : Module.End F (Fin n → F)) :
    X ∈ Set.range (endRestrict A) ↔ ∀ g : A, Commute X (rhoOf A g) := by
  constructor
  · rintro ⟨f, rfl⟩ g
    refine LinearMap.ext fun v => ?_
    have h := f.map_smul (MonoidAlgebra.of F A g) ((rhoOf A).asModuleEquiv.symm v)
    rw [← Representation.asModuleEquiv_symm_map_rho] at h
    have h2 := congrArg (rhoOf A).asModuleEquiv h
    rw [Representation.asModuleEquiv_map_smul, Representation.asAlgebraHom_of] at h2
    exact h2
  · intro hX
    refine ⟨{ toFun := X, map_add' := X.map_add, map_smul' := fun r v => ?_ }, rfl⟩
    exact LinearMap.congr_fun (commute_asAlgebraHom A hX r).eq v

theorem exists_piGL_centralizer [Finite F] (A : Subgroup (GL (Fin n) F))
    (hA : (Nat.card A : F) ≠ 0) :
    ∃ (r : ℕ) (D : Fin r → Type) (d : Fin r → ℕ) (_ : ∀ i, Field (D i)) (_ : ∀ i, Finite (D i))
      (_ : ∀ i, Algebra F (D i)) (θ : (∀ i, GL (Fin (d i)) (D i)) →* GL (Fin n) F),
      Function.Injective θ ∧ θ.range = Subgroup.centralizer (A : Set (GL (Fin n) F)) := by
  have : NeZero (Nat.card A : F) := ⟨hA⟩
  have : Module.Finite (MonoidAlgebra F A) (rhoOf A).asModule :=
    Module.Finite.of_restrictScalars_finite F (MonoidAlgebra F A) (rhoOf A).asModule
  have : IsSemisimpleRing (Module.End (MonoidAlgebra F A) (rhoOf A).asModule) :=
    IsSemisimpleRing.moduleEnd (MonoidAlgebra F A) (rhoOf A).asModule
  have : Module.Finite F (Module.End (MonoidAlgebra F A) (rhoOf A).asModule) :=
    Module.Finite.of_injective (LinearMap.restrictScalarsₗ F (MonoidAlgebra F A) _ _ F)
      (LinearMap.restrictScalars_injective F)
  obtain ⟨r, D, d, _, _, _, _, ⟨e⟩⟩ :=
    IsSemisimpleRing.exists_algEquiv_pi_matrix_divisionRing_finite F
      (Module.End (MonoidAlgebra F A) (rhoOf A).asModule)
  have hfin : ∀ i, Finite (D i) := fun i => Module.finite_of_finite F
  let Φ : (Π i, Matrix (Fin (d i)) (Fin (d i)) (D i)) →ₐ[F] Matrix (Fin n) (Fin n) F :=
    ((LinearMap.toMatrixAlgEquiv' : Module.End F (Fin n → F) ≃ₐ[F] _).toAlgHom.comp
      (endRestrict A)).comp e.symm.toAlgHom
  have hΦinj : Function.Injective Φ :=
    (LinearMap.toMatrixAlgEquiv'.injective.comp (endRestrict_injective A)).comp e.symm.injective
  have hΦrange : ∀ X : Matrix (Fin n) (Fin n) F, X ∈ Set.range Φ ↔
      ∀ g ∈ A, X * (g : Matrix (Fin n) (Fin n) F) = (g : Matrix (Fin n) (Fin n) F) * X := by
    intro X
    constructor
    · rintro ⟨y, rfl⟩ g hg
      have h := (mem_range_endRestrict A _).mp ⟨e.symm y, rfl⟩ ⟨g, hg⟩
      have h2 := congrArg (LinearMap.toMatrixAlgEquiv' : Module.End F (Fin n → F) ≃ₐ[F] _) h.eq
      rw [map_mul, map_mul, rhoOf_apply, ← Matrix.toLinAlgEquiv'_symm] at h2
      simpa [Φ] using h2
    · intro hX
      obtain ⟨f, hf⟩ := (mem_range_endRestrict A (Matrix.toLinAlgEquiv' X)).mpr fun g => by
        rw [rhoOf_apply]
        show _ * _ = _ * _
        rw [← map_mul, ← map_mul, hX g g.2]
      refine ⟨e f, ?_⟩
      show LinearMap.toMatrixAlgEquiv' (endRestrict A (e.symm (e f))) = X
      rw [e.symm_apply_apply, hf]
      exact LinearMap.toMatrixAlgEquiv'_toLinAlgEquiv' X
  refine ⟨r, D, d, fun i => littleWedderburn (D i), hfin, inferInstance,
    (Units.map Φ.toMonoidHom).comp MulEquiv.piUnits.symm.toMonoidHom, ?_, ?_⟩
  · exact (Units.map_injective (f := Φ.toMonoidHom) hΦinj).comp MulEquiv.piUnits.symm.injective
  · have hmem : ∀ X : GL (Fin n) F, X ∈ Subgroup.centralizer (A : Set (GL (Fin n) F)) →
        (X : Matrix (Fin n) (Fin n) F) ∈ Set.range Φ := fun X hX =>
      (hΦrange _).mpr fun g hg =>
        (congrArg Units.val (Subgroup.mem_centralizer_iff.mp hX g hg)).symm
    ext X
    constructor
    · rintro ⟨w, rfl⟩
      rw [Subgroup.mem_centralizer_iff]
      intro g hg
      apply Units.ext
      exact ((hΦrange _).mp ⟨_, rfl⟩ g hg).symm
    · intro hX
      obtain ⟨y, hy⟩ := hmem X hX
      obtain ⟨y', hy'⟩ := hmem X⁻¹ ((Subgroup.centralizer _).inv_mem hX)
      have h1 : y * y' = 1 := hΦinj (by rw [map_mul, hy, hy', Units.mul_inv, map_one])
      have h2 : y' * y = 1 := hΦinj (by rw [map_mul, hy, hy', Units.inv_mul, map_one])
      refine ⟨MulEquiv.piUnits ⟨y, y', h1, h2⟩, Units.ext ?_⟩
      show Φ ((MulEquiv.piUnits.symm (MulEquiv.piUnits ⟨y, y', h1, h2⟩) :
        (Π i, Matrix (Fin (d i)) (Fin (d i)) (D i))ˣ) : Π i, Matrix (Fin (d i)) (Fin (d i)) (D i))
          = X
      rw [MulEquiv.symm_apply_apply]
      exact hy

end LayerFacts

end CFSG.StandardType

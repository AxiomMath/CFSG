module

public import Mathlib.Basic.Complex.Basic
public import Mathlib.Algebra.Group.ConjFinite
public import Mathlib.Algebra.Group.Conj
public import Mathlib.RepresentationTheory.Character
public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.RepresentationTheory.Induced
public import Mathlib.GroupTheory.GroupAction.Quotient
public import CFSG.ThirdParty.QiuzhenCFSG.Theory.Character.ClassFunction

namespace CFSG
end CFSG
open CFSG

/-!
# Class functions on conjugacy classes

Class functions `ConjClasses G → ℂ`, the inner product, the character
predicates on them, and the bridges to `ClassFunction G` (`G → ℂ`).
-/

noncomputable section

open scoped BigOperators

attribute [local instance] Fintype.ofFinite

namespace CFSG.Theory.Character

variable {G : Type*} [Group G]

/-- Complex-valued class functions on `G`, implemented as functions on conjugacy classes. -/
public abbrev ConjClassFunction (G : Type*) [Group G] := ConjClasses G → ℂ

/-- Turn a complex-valued function on `G` that is constant on conjugacy classes into a class function. -/
@[expose] public noncomputable def conjClassFunctionOfInvariant (f : G → ℂ)
    (hf : ∀ g h : G, f (h * g * h⁻¹) = f g) : ConjClassFunction G := by
  refine Quotient.lift f ?_
  intro a b hab
  rcases hab with ⟨c, hc⟩
  have hconj : (↑c : G) * a * ↑(c⁻¹) = b := by
    calc
      (↑c : G) * a * ↑(c⁻¹) = (b * ↑c) * ↑(c⁻¹) := by rw [hc.eq]
      _ = b := by simp [mul_assoc]
  calc
    f a = f ((↑c : G) * a * ↑(c⁻¹)) := by simpa using (hf a c).symm
    _ = f b := by rw [hconj]

/-- The class function attached to a representation character. -/
@[expose] public noncomputable def characterClassFunction {V : Type*} [AddCommGroup V]
    [Module ℂ V] [FiniteDimensional ℂ V] (ρ : Representation ℂ G V) : ConjClassFunction G :=
  conjClassFunctionOfInvariant ρ.character (by
    intro g h
    simpa [mul_assoc] using Representation.char_conj (ρ := ρ) g h)

/-- Inner product of complex class functions, normalized by `|G|`. -/
@[expose] public noncomputable def classFunctionInner [Finite G]
    (φ ψ : ConjClassFunction G) : ℂ := by
  classical
  letI := Fintype.ofFinite G
  exact (Nat.card G : ℂ)⁻¹ * ∑ g : G, φ (ConjClasses.mk g) * star (ψ (ConjClasses.mk g))

/-- A complex class function on `G` is a character if it comes from a finite-dimensional
representation, encoded on the standard space `Fin n → ℂ`. -/
@[expose] public def IsConjCharacter [Finite G] (χ : ConjClassFunction G) : Prop :=
  ∃ n : ℕ, ∃ ρ : Representation ℂ G (Fin n → ℂ), χ = characterClassFunction ρ

/-- A complex class function on `G` is irreducible if it is a character of norm one. -/
@[expose] public def IsIrreducibleConjCharacter [Finite G] (χ : ConjClassFunction G) : Prop :=
  IsConjCharacter χ ∧ classFunctionInner χ χ = 1

/-- A finite family of class functions containing each irreducible complex character
exactly once. -/
@[expose] public def IsCompleteIrreducibleCharacterFamily [Finite G]
    {ι : Type*} [Fintype ι] (χ : ι → ConjClassFunction G) : Prop :=
  (∀ i, IsIrreducibleConjCharacter (χ i)) ∧
    (∀ χ₀ : ConjClassFunction G, IsIrreducibleConjCharacter χ₀ → ∃ i, χ i = χ₀) ∧
    Function.Injective χ

/-! ## Bridges between `ClassFunction G` (`G → ℂ`) and `ConjClassFunction G` (`ConjClasses G → ℂ`) -/

/-- Turn a class function on `G` into a function on conjugacy classes. -/
@[expose] public noncomputable def toConjClassFunction {G : Type*} [Group G]
    (phi : ClassFunction G) (hphi : IsClassFunction phi) : ConjClassFunction G :=
  conjClassFunctionOfInvariant phi (by
    intro g x
    exact hphi g x)

public theorem toConjClassFunction_apply {G : Type*} [Group G] (phi : ClassFunction G)
    (hphi : IsClassFunction phi) (g : G) :
    toConjClassFunction phi hphi (ConjClasses.mk g) = phi g := rfl

public theorem toConjClassFunction_eq_of_apply {G : Type*} [Group G] (phi : ClassFunction G)
    (hphi : IsClassFunction phi) (Phi : ConjClassFunction G)
    (hPhi : ∀ g : G, Phi (ConjClasses.mk g) = phi g) :
    toConjClassFunction phi hphi = Phi := by
  ext c
  rcases ConjClasses.exists_rep c with ⟨g, rfl⟩
  exact (toConjClassFunction_apply phi hphi g).trans (hPhi g).symm

public theorem classFunctionInner_toConjClassFunction {G : Type*} [Group G] [Finite G]
    (phi psi : ClassFunction G) (hphi : IsClassFunction phi) (hpsi : IsClassFunction psi) :
    classFunctionInner (toConjClassFunction phi hphi) (toConjClassFunction psi hpsi) =
      scalarProduct G phi psi := by
  classical
  rfl

@[expose] public noncomputable def ofConjClassFunction {G : Type*} [Group G]
    (chi : ConjClassFunction G) : ClassFunction G :=
  fun g => chi (ConjClasses.mk g)

public theorem ofConjClassFunction_apply {G : Type*} [Group G]
    (chi : ConjClassFunction G) (g : G) :
    ofConjClassFunction chi g = chi (ConjClasses.mk g) := rfl

public theorem ofConjClassFunction_characterClassFunction {G V : Type*} [Group G]
    [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (rho : Representation ℂ G V) :
    ofConjClassFunction (characterClassFunction rho) = rho.character := by
  rfl

public theorem ofConjClassFunction_isClassFunction {G : Type*} [Group G]
    (chi : ConjClassFunction G) :
    IsClassFunction (ofConjClassFunction chi) := by
  intro x g
  unfold ofConjClassFunction
  congr 1
  exact (ConjClasses.mk_eq_mk_iff_isConj).2
    ((isConj_iff).2 ⟨g⁻¹, by simp [mul_assoc]⟩)

public theorem toConjClassFunction_ofConjClassFunction {G : Type*} [Group G]
    (chi : ConjClassFunction G) :
    toConjClassFunction (ofConjClassFunction chi)
        (ofConjClassFunction_isClassFunction chi) = chi := by
  ext c
  rcases ConjClasses.exists_rep c with ⟨g, rfl⟩
  rfl

public theorem scalarProduct_ofConjClassFunction {G : Type*} [Group G] [Finite G]
    (phi psi : ConjClassFunction G) :
    scalarProduct G (ofConjClassFunction phi) (ofConjClassFunction psi) =
      classFunctionInner phi psi := by
  symm
  simpa only [toConjClassFunction_ofConjClassFunction] using
    (classFunctionInner_toConjClassFunction
      (ofConjClassFunction phi) (ofConjClassFunction psi)
      (ofConjClassFunction_isClassFunction phi)
      (ofConjClassFunction_isClassFunction psi))

public theorem classFunctionInner_toConjClassFunction_right {G : Type*} [Group G] [Finite G]
    (phi : ClassFunction G) (hphi : IsClassFunction phi) (chi : ConjClassFunction G) :
    classFunctionInner (toConjClassFunction phi hphi) chi =
      scalarProduct G phi (ofConjClassFunction chi) := by
  rw [← toConjClassFunction_ofConjClassFunction chi]
  exact classFunctionInner_toConjClassFunction phi (ofConjClassFunction chi)
    hphi (ofConjClassFunction_isClassFunction chi)

end CFSG.Theory.Character

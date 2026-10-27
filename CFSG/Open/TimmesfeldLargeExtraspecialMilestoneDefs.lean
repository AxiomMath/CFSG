module

public import CFSG.Open.Defs
public import CFSG.GroupTheory.Fitting.WholeGroupConstruction

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Open
open CFSG.Open

open Matrix
open scoped MatrixGroups

@[expose] def timmesfeldFitting (H : Type*) [Group H] : Subgroup H :=
  CFSG.fittingSubgroup H

theorem timmesfeldFitting.eq_sSup (H : Type*) [Group H] :
    timmesfeldFitting H = sSup {N : Subgroup H | N.Normal ∧ Group.IsNilpotent N} :=
  rfl

attribute [eqns timmesfeldFitting.eq_sSup] timmesfeldFitting

@[expose] def timmesfeldLayer (H : Type*) [Group H] : Subgroup H :=
  CFSG.WholeGroup.layerOf fun L : Subgroup H => IsComponentOf L ⊤

theorem timmesfeldLayer.eq_sSup (H : Type*) [Group H] :
    timmesfeldLayer H = sSup {L : Subgroup H | IsComponentOf L ⊤} :=
  rfl

attribute [eqns timmesfeldLayer.eq_sSup] timmesfeldLayer

@[expose] def timmesfeldFStar (H : Type*) [Group H] : Subgroup H :=
  CFSG.WholeGroup.fstarOf (timmesfeldLayer H)

theorem timmesfeldFStar.eq_sup (H : Type*) [Group H] :
    timmesfeldFStar H = timmesfeldFitting H ⊔ timmesfeldLayer H :=
  rfl

attribute [eqns timmesfeldFStar.eq_sup] timmesfeldFStar

@[expose] def timmesfeldOddCore (H : Type*) [Group H] : Subgroup H :=
  sSup {N : Subgroup H | N.Normal ∧ Odd (Nat.card N)}

@[expose] def timmesfeldIsExtraspecial (P : Type*) [Group P] : Prop :=
  IsPGroup 2 P ∧ commutator P = frattini P ∧ frattini P = Subgroup.center P ∧
    Nat.card (Subgroup.center P) = 2

@[expose] def timmesfeldQuotientIso {A : Type*} [Group A] (N : Subgroup A) (X : Type*) [Group X] :
    Prop :=
  ∃ φ : A →* X, Function.Surjective φ ∧ φ.ker = N

@[expose] noncomputable def timmesfeldPSU (n : ℕ) :
    Subgroup (ProjGenLinGroup (Fin n) (GaloisField 2 2)) :=
  (Subgroup.closure {A : GL (Fin n) (GaloisField 2 2) |
      (Matrix.of fun i j => (A : Matrix (Fin n) (Fin n) (GaloisField 2 2)) j i ^ 2) *
          (A : Matrix (Fin n) (Fin n) (GaloisField 2 2)) = 1 ∧
        GeneralLinearGroup.det A = 1}).map ProjGenLinGroup.mk

@[expose] def timmesfeldIsometries {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] (q : V → ZMod 2) :
    Subgroup (V ≃ₗ[ZMod 2] V) where
  carrier := {g | ∀ v, q (g v) = q v}
  mul_mem' {a b} ha hb v := (ha (b v)).trans (hb v)
  one_mem' _ := rfl
  inv_mem' {a} ha v := by
    have h := ha (a⁻¹ v)
    rw [← LinearEquiv.mul_apply, mul_inv_cancel] at h
    exact h.symm

@[expose] noncomputable def timmesfeldOmega {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    (q : V → ZMod 2) : Subgroup (V ≃ₗ[ZMod 2] V) :=
  Subgroup.closure {g | g ∈ timmesfeldIsometries q ∧
    Even (Module.finrank (ZMod 2) (LinearMap.range ((g : V →ₗ[ZMod 2] V) - LinearMap.id)))}

@[expose] def timmesfeldNondegenerate {d : ℕ} (q : QuadraticForm (ZMod 2) (Fin d → ZMod 2)) : Prop :=
  ∀ u, (∀ v, QuadraticMap.polar q u v = 0) → u = 0

@[expose] def timmesfeldPlusType {d : ℕ} (q : QuadraticForm (ZMod 2) (Fin d → ZMod 2)) : Prop :=
  ∃ W : Submodule (ZMod 2) (Fin d → ZMod 2), 2 * Module.finrank (ZMod 2) W = d ∧
    ∀ v ∈ W, q v = 0

@[expose] def timmesfeldPlusForm (n : ℕ) : (Fin n → ZMod 2) × (Fin n → ZMod 2) → ZMod 2 :=
  fun v => ∑ i, v.1 i * v.2 i

@[expose] def timmesfeldOmegaPlus (n : ℕ) :
    Subgroup (((Fin n → ZMod 2) × (Fin n → ZMod 2)) ≃ₗ[ZMod 2]
      ((Fin n → ZMod 2) × (Fin n → ZMod 2))) :=
  ⁅timmesfeldIsometries (timmesfeldPlusForm n), timmesfeldIsometries (timmesfeldPlusForm n)⁆

@[expose] def timmesfeldOrderCo2 : ℕ := 2 ^ 18 * 3 ^ 6 * 5 ^ 3 * 7 * 11 * 23

@[expose] def timmesfeldOrderCo1 : ℕ := 2 ^ 21 * 3 ^ 9 * 5 ^ 4 * 7 ^ 2 * 11 * 13 * 23

end CFSG.Open

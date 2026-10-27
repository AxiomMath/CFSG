module

public import CFSG.Quasithin.Vol2.Ch10Reselect.AutSL2
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar

public section

namespace CFSG.Quasithin.Vol2.Ch10Reselect

open Matrix

theorem mix_mul_aux {K : Type*} [Field K] (C D : Matrix (Fin 2) (Fin 2) K)
    (v : (Fin 2 → K) × (Fin 2 → K)) :
    (C 0 0 • (D 0 0 • v.1 + D 0 1 • v.2) + C 0 1 • (D 1 0 • v.1 + D 1 1 • v.2),
      C 1 0 • (D 0 0 • v.1 + D 0 1 • v.2) + C 1 1 • (D 1 0 • v.1 + D 1 1 • v.2)) =
    (((C * D) 0 0) • v.1 + ((C * D) 0 1) • v.2, ((C * D) 1 0) • v.1 + ((C * D) 1 1) • v.2) := by
  simp only [Matrix.mul_apply, Fin.sum_univ_two, Prod.mk.injEq]
  constructor <;> module

theorem bPerm_aux {K : Type*} [Field K] (C D : Matrix (Fin 2) (Fin 2) K) (h : C * D = 1)
    (v : (Fin 2 → K) × (Fin 2 → K)) :
    (C 0 0 • (D 0 0 • v.1 + D 0 1 • v.2) + C 0 1 • (D 1 0 • v.1 + D 1 1 • v.2),
      C 1 0 • (D 0 0 • v.1 + D 0 1 • v.2) + C 1 1 • (D 1 0 • v.1 + D 1 1 • v.2)) = v := by
  rw [mix_mul_aux, h]
  simp [Matrix.one_apply]

section Defs

variable (K : Type*) [Field K]

abbrev UTilde := (Fin 2 → K) × (Fin 2 → K)

@[expose] noncomputable def rhoSL :
    Matrix.SpecialLinearGroup (Fin 2) K →* Equiv.Perm (UTilde K) :=
  MulAction.toPermHom (Matrix.SpecialLinearGroup (Fin 2) K) (UTilde K)

@[expose] def sigmaPerm (σ : RingAut K) : Equiv.Perm (UTilde K) where
  toFun v := (fun i => σ (v.1 i), fun i => σ (v.2 i))
  invFun v := (fun i => σ.symm (v.1 i), fun i => σ.symm (v.2 i))
  left_inv v := by ext <;> simp
  right_inv v := by ext <;> simp

@[expose] noncomputable def bPerm (B : GL (Fin 2) K) : Equiv.Perm (UTilde K) where
  toFun v := (((B : Matrix (Fin 2) (Fin 2) K) 0 0) • v.1 + ((B : Matrix (Fin 2) (Fin 2) K) 0 1) • v.2,
    ((B : Matrix (Fin 2) (Fin 2) K) 1 0) • v.1 + ((B : Matrix (Fin 2) (Fin 2) K) 1 1) • v.2)
  invFun v := (((B⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) 0 0 • v.1 +
      ((B⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) 0 1 • v.2,
    ((B⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) 1 0 • v.1 +
      ((B⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) 1 1 • v.2)
  left_inv v := bPerm_aux _ _ (Units.inv_mul B) v
  right_inv v := bPerm_aux _ _ (Units.mul_inv B) v

@[expose] noncomputable def phi (g : Matrix.SpecialLinearGroup (Fin 2) K) (σ : RingAut K)
    (B : GL (Fin 2) K) : Equiv.Perm (UTilde K) :=
  rhoSL K g * sigmaPerm K σ * bPerm K B

@[expose] def glMap (σ : RingAut K) : GL (Fin 2) K →* GL (Fin 2) K :=
  Matrix.GeneralLinearGroup.map (σ : K →+* K)

@[expose] noncomputable def wMap (σ : RingAut K) (B : GL (Fin 2) K) : Equiv.Perm (Fin 2 → K) where
  toFun w := fun i => σ (((B : Matrix (Fin 2) (Fin 2) K) *ᵥ w) i)
  invFun w := ((B⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) *ᵥ (fun i => σ.symm (w i))
  left_inv w := by
    have h1 : (fun i => σ.symm (σ (((B : Matrix (Fin 2) (Fin 2) K) *ᵥ w) i))) =
        (B : Matrix (Fin 2) (Fin 2) K) *ᵥ w :=
      funext fun i => RingEquiv.symm_apply_apply σ _
    show ((B⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) *ᵥ
      (fun i => σ.symm (σ (((B : Matrix (Fin 2) (Fin 2) K) *ᵥ w) i))) = w
    rw [h1, Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec]
  right_inv w := by
    show (fun i => σ (((B : Matrix (Fin 2) (Fin 2) K) *ᵥ
      (((B⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) *ᵥ (fun j => σ.symm (w j)))) i)) = w
    rw [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]
    funext i
    exact RingEquiv.apply_symm_apply σ (w i)

@[expose] def linePair (w : Fin 2 → K) : Set (UTilde K) :=
  {p | ∃ v : Fin 2 → K, p = (w 0 • v, w 1 • v)}

end Defs

end CFSG.Quasithin.Vol2.Ch10Reselect

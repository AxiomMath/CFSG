module

public import CFSG.Quasithin.EmptyFaithful.SzC4ChiModDef
public import Mathlib.Algebra.CharP.CharAndCard
public import Mathlib.Algebra.CharP.Two
public import Mathlib.Data.Matrix.Mul

public section

namespace CFSG.Quasithin.SzC4

open scoped Matrix

namespace ChiMod

@[expose] def kerP {F : Type} [Field F] (B : Matrix (Fin 3) (Fin 3) F) : Set (Fin 3 → F) :=
  {v | B *ᵥ (B *ᵥ (B *ᵥ v)) + B *ᵥ (B *ᵥ v) + v = 0}

@[expose] def kerT {F : Type} [Field F] (B : Matrix (Fin 3) (Fin 3) F) : Set (Fin 3 → F) :=
  {v | B *ᵥ (B *ᵥ (B *ᵥ v)) + B *ᵥ v + v = 0}

end ChiMod

@[expose] noncomputable def chiMat {F : Type} [Field F] (B : Matrix (Fin 3) (Fin 3) F) : ℤ :=
  (padicValNat 2 (Nat.card (ChiMod.kerP B)) : ℤ) - padicValNat 2 (Nat.card (ChiMod.kerT B))

@[expose] def vecAut {F : Type} [Field F] (k : ℕ) (B : Matrix (Fin 3) (Fin 3) F)
    (hB : B ^ 7 = 1) : MulAut (Multiplicative (Fin k → Fin 3 → F)) where
  toFun x := Multiplicative.ofAdd fun i => B *ᵥ Multiplicative.toAdd x i
  invFun x := Multiplicative.ofAdd fun i => (B ^ 6) *ᵥ Multiplicative.toAdd x i
  left_inv x := by
    have h : B ^ 6 * B = 1 := by rw [← pow_succ]; exact hB
    apply Multiplicative.toAdd.injective
    funext i
    simp [Matrix.mulVec_mulVec, h]
  right_inv x := by
    have h : B * B ^ 6 = 1 := by rw [← pow_succ']; exact hB
    apply Multiplicative.toAdd.injective
    funext i
    simp [Matrix.mulVec_mulVec, h]
  map_mul' x y := by
    apply Multiplicative.toAdd.injective
    funext i
    simp [Matrix.mulVec_add]

namespace ChiMod

section Kernels

variable {F : Type} [Field F] (k : ℕ) (B : Matrix (Fin 3) (Fin 3) F) (hB : B ^ 7 = 1)

theorem toAdd_vecAut (x : Multiplicative (Fin k → Fin 3 → F)) :
    Multiplicative.toAdd (vecAut k B hB x) = fun i => B *ᵥ Multiplicative.toAdd x i := rfl

theorem mem_Kp_vecAut (x : Multiplicative (Fin k → Fin 3 → F)) :
    x ∈ Kp (vecAut k B hB) ↔ ∀ i, Multiplicative.toAdd x i ∈ kerP B := by
  show _ = (1 : Multiplicative (Fin k → Fin 3 → F)) ↔ _
  rw [← toAdd_eq_zero, funext_iff]
  simp only [toAdd_mul, toAdd_vecAut, Pi.add_apply, Pi.zero_apply]
  rfl

theorem mem_Kt_vecAut (x : Multiplicative (Fin k → Fin 3 → F)) :
    x ∈ Kt (vecAut k B hB) ↔ ∀ i, Multiplicative.toAdd x i ∈ kerT B := by
  show _ = (1 : Multiplicative (Fin k → Fin 3 → F)) ↔ _
  rw [← toAdd_eq_zero, funext_iff]
  simp only [toAdd_mul, toAdd_vecAut, Pi.add_apply, Pi.zero_apply]
  rfl

theorem card_Kp_vecAut :
    Nat.card (Kp (vecAut k B hB)) = Nat.card (kerP B) ^ k := by
  have e : Kp (vecAut k B hB) ≃ (Fin k → kerP B) :=
    (Equiv.subtypeEquiv Multiplicative.toAdd (fun x => mem_Kp_vecAut k B hB x)).trans
      Equiv.subtypePiEquivPi
  rw [Nat.card_congr e, Nat.card_fun, Nat.card_eq_fintype_card (α := Fin k), Fintype.card_fin]

theorem card_Kt_vecAut :
    Nat.card (Kt (vecAut k B hB)) = Nat.card (kerT B) ^ k := by
  have e : Kt (vecAut k B hB) ≃ (Fin k → kerT B) :=
    (Equiv.subtypeEquiv Multiplicative.toAdd (fun x => mem_Kt_vecAut k B hB x)).trans
      Equiv.subtypePiEquivPi
  rw [Nat.card_congr e, Nat.card_fun, Nat.card_eq_fintype_card (α := Fin k), Fintype.card_fin]

theorem delta_vecAut_aux :
    delta (Multiplicative (Fin k → Fin 3 → F)) (vecAut k B hB) = k * chiMat B := by
  rw [delta, card_Kp_vecAut, card_Kt_vecAut, padicValNat.pow, padicValNat.pow, chiMat]
  push_cast
  ring

end Kernels

end ChiMod

end CFSG.Quasithin.SzC4

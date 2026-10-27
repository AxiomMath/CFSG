module

public import CFSG.LocalAnalysis.StandardType.GGTBJF4Defs
public import CFSG.LocalAnalysis.StandardType.GGTBJF4Roots
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs

public section

namespace CFSG.StandardType

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

@[expose] noncomputable def ggTBJRefl (p : ℕ) [Fact p.Prime] (β : Fin 4 → ℤ)
    (w : Fin 4 → ZMod p) : Fin 4 → ZMod p :=
  fun i => w i - ggTBJFun p β w * ggTBJVec p β i

theorem ggTBJ_refl_aux_inv {R : Type} [CommRing R] (a x v : R) : a - x * v - (-x) * v = a := by
  ring

theorem ggTBJ_refl_aux_sub_eq_self {R : Type} [CommRing R] {a b : R} (h : a - b = a) : b = 0 := by
  have h' : a + -b = a + 0 := by simpa using h
  exact neg_eq_zero.mp (add_left_cancel h')

theorem ggTBJ_refl_aux_sub_zero {R : Type} [CommRing R] (a : R) : a - 0 = a := by
  ring

theorem ggTBJ_reflAut_ofAdd (p : ℕ) [Fact p.Prime] {β : Fin 4 → ℤ}
    (h : ggTBJFun p β (ggTBJVec p β) = 2) (w : Fin 4 → ZMod p) :
    ggTBJReflAut p β (Multiplicative.ofAdd w) = Multiplicative.ofAdd (ggTBJRefl p β w) := by
  apply Multiplicative.toAdd.injective
  funext i
  rw [ggTBJReflAut_apply p h, toAdd_ofAdd, toAdd_ofAdd]
  rfl

theorem ggTBJ_reflAut_sq (p : ℕ) [Fact p.Prime] {β : Fin 4 → ℤ}
    (h : ggTBJFun p β (ggTBJVec p β) = 2) :
    ggTBJReflAut p β ^ 2 = 1 := by
  apply MulEquiv.ext
  intro f
  rw [pow_two, MulAut.mul_apply, MulAut.one_apply]
  apply Multiplicative.toAdd.injective
  funext i
  have htoAdd : Multiplicative.toAdd (ggTBJReflAut p β f) =
      fun i => Multiplicative.toAdd f i -
        ggTBJFun p β (Multiplicative.toAdd f) * ggTBJVec p β i :=
    funext fun i => ggTBJReflAut_apply p h f i
  rw [ggTBJReflAut_apply p h (ggTBJReflAut p β f) i, htoAdd,
    ggTBJFun_sub_smul_vec p h (Multiplicative.toAdd f)]
  exact ggTBJ_refl_aux_inv _ _ _

theorem ggTBJ_card_fixed_mul (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) {β : Fin 4 → ℤ}
    (h : ggTBJFun p β (ggTBJVec p β) = 2) :
    Nat.card {f : Multiplicative (Fin 4 → ZMod p) // ggTBJReflAut p β f = f} * p = p ^ 4 := by
  have hv : ggTBJVec p β ≠ 0 := by
    intro h0
    have h2 : ggTBJFun p β (ggTBJVec p β) = 0 := by rw [h0, map_zero]
    rw [h] at h2
    exact zmod_two_ne_zero hp2 h2
  have hvi : ∃ i, ggTBJVec p β i ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hv (funext hcon)
  have hfix : ∀ a : Multiplicative (Fin 4 → ZMod p),
      ggTBJReflAut p β a = a ↔ Multiplicative.toAdd a ∈ LinearMap.ker (ggTBJFun p β) := by
    intro a
    constructor
    · intro ha
      rw [LinearMap.mem_ker]
      obtain ⟨i0, hi0⟩ := hvi
      have hcoord := congrFun (congrArg Multiplicative.toAdd ha) i0
      rw [ggTBJReflAut_apply p h a i0] at hcoord
      have hmul : ggTBJFun p β (Multiplicative.toAdd a) * ggTBJVec p β i0 = 0 :=
        ggTBJ_refl_aux_sub_eq_self hcoord
      exact (mul_eq_zero.mp hmul).resolve_right hi0
    · intro ha
      apply Multiplicative.toAdd.injective
      funext i
      rw [ggTBJReflAut_apply p h a i, LinearMap.mem_ker.mp ha, zero_mul]
      exact ggTBJ_refl_aux_sub_zero _
  have hcard : Nat.card {f : Multiplicative (Fin 4 → ZMod p) // ggTBJReflAut p β f = f} =
      Nat.card ↥(LinearMap.ker (ggTBJFun p β)) :=
    Nat.card_congr
      (Equiv.subtypeEquiv
        (Multiplicative.toAdd : Multiplicative (Fin 4 → ZMod p) ≃ (Fin 4 → ZMod p)) hfix)
  have hne : (ggTBJFun p β : Module.Dual (ZMod p) (Fin 4 → ZMod p)) ≠ 0 := by
    intro h0
    have h1 := congrArg (fun l : Module.Dual (ZMod p) (Fin 4 → ZMod p) => l (ggTBJVec p β)) h0
    simp only [LinearMap.zero_apply] at h1
    rw [h] at h1
    exact zmod_two_ne_zero hp2 h1
  have hsurj : Function.Surjective (ggTBJFun p β) := by
    intro y
    have hx : ∃ x, ggTBJFun p β x ≠ 0 := by
      by_contra hcon
      push Not at hcon
      exact hne (LinearMap.ext fun x => by simpa using hcon x)
    obtain ⟨x, hx⟩ := hx
    refine ⟨(y * (ggTBJFun p β x)⁻¹) • x, ?_⟩
    rw [map_smul, smul_eq_mul, mul_assoc, inv_mul_cancel₀ hx, mul_one]
  have hVcard : Nat.card (Fin 4 → ZMod p) = p ^ 4 := by
    rw [Nat.card_fun, Nat.card_zmod, Nat.card_fin]
  have heq : Nat.card ↥(LinearMap.ker (ggTBJFun p β)) =
      Nat.card (ggTBJFun p β).toAddMonoidHom.ker :=
    Nat.card_congr (Equiv.subtypeEquivRight fun x => by
      rw [AddMonoidHom.mem_ker]; exact LinearMap.mem_ker)
  have hker := AddSubgroup.card_ker_mul_card_range (ggTBJFun p β).toAddMonoidHom
  rw [AddMonoidHom.range_eq_top.mpr hsurj, AddSubgroup.card_top, Nat.card_zmod, hVcard] at hker
  rw [hcard.trans heq]
  exact hker

end CFSG.StandardType

end
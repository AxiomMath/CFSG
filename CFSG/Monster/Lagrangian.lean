module

public import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
public import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Finite.GaloisField

public section

namespace CFSG.Monster

open Module

@[expose] def sgn (t : ZMod 2) : ℚ := if t = 0 then 1 else -1

theorem sgn_add (s t : ZMod 2) : sgn (s + t) = sgn s * sgn t := by
  fin_cases s <;> fin_cases t <;> simp [sgn] <;> decide

theorem sgn_zero : sgn 0 = 1 := rfl

variable {E : Type*} [AddCommGroup E] [Module (ZMod 2) E] [Fintype E]

@[expose] def fourier (b : LinearMap.BilinForm (ZMod 2) E) (m : ℕ) (f : E → ℚ) (u : E) : ℚ :=
  ((2 : ℚ) ^ m)⁻¹ * ∑ v, sgn (b u v) * f v

@[expose] def signOp (q : E → ZMod 2) (f : E → ℚ) (v : E) : ℚ := sgn (q v) * f v

@[expose] def lagrangianFun (b : LinearMap.BilinForm (ZMod 2) E) (K : Submodule (ZMod 2) E)
    (a : E) [DecidablePred (· ∈ K)] (v : E) : ℚ :=
  if v - a ∈ K then sgn (b a v) else 0

omit [Fintype E] in
theorem symm_of_alternating {b : LinearMap.BilinForm (ZMod 2) E} (halt : ∀ v, b v v = 0)
    (x y : E) : b x y = b y x := by
  have h := halt (x + y)
  simp only [map_add, LinearMap.add_apply, halt x, halt y, zero_add, add_zero] at h
  have h' : b y x = -b x y := eq_neg_of_add_eq_zero_left h
  rw [ZMod.neg_eq_self_mod_two] at h'
  exact h'.symm

theorem sum_sgn_of_perp (b : LinearMap.BilinForm (ZMod 2) E) (K : Submodule (ZMod 2) E)
    [DecidablePred (· ∈ K)] {w : E} (h : ∀ k ∈ K, b w k = 0) :
    ∑ k : K, sgn (b w k) = (Fintype.card K : ℚ) := by
  simp [h, sgn]

theorem sum_sgn_of_not_perp (b : LinearMap.BilinForm (ZMod 2) E) (K : Submodule (ZMod 2) E)
    [DecidablePred (· ∈ K)] {w : E} {k₀ : E} (hk₀ : k₀ ∈ K) (hne : b w k₀ ≠ 0) :
    ∑ k : K, sgn (b w k) = 0 := by
  have h1 : b w k₀ = 1 := by
    have : ∀ t : ZMod 2, t ≠ 0 → t = 1 := by decide
    exact this _ hne
  have hshift : ∑ k : K, sgn (b w k) = ∑ k : K, sgn (b w ((k : E) + k₀)) :=
    (Fintype.sum_equiv (Equiv.addRight (⟨k₀, hk₀⟩ : K)) _ _ fun k => by simp).symm
  simp only [map_add, sgn_add, h1] at hshift
  have : sgn 1 = -1 := rfl
  rw [this] at hshift
  simp only [mul_neg, mul_one, Finset.sum_neg_distrib] at hshift
  linarith

omit [Fintype E] in
theorem sub_eq_add_zmod_two (v a : E) : v - a = v + a := by
  rw [sub_eq_add_neg, neg_eq_of_add_eq_zero_right]
  rw [← two_smul (ZMod 2) a]
  simp [show (2 : ZMod 2) = 0 from rfl]

theorem fourier_lagrangianFun (b : LinearMap.BilinForm (ZMod 2) E) (hb : b.Nondegenerate)
    (halt : ∀ v, b v v = 0) {m : ℕ} (hE : finrank (ZMod 2) E = 2 * m)
    (K : Submodule (ZMod 2) E) [DecidablePred (· ∈ K)] (hK : finrank (ZMod 2) K = m)
    (hKK : ∀ x ∈ K, ∀ y ∈ K, b x y = 0) (a : E) :
    fourier b m (lagrangianFun b K a) = lagrangianFun b K a := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hsymm := symm_of_alternating halt
  have hKperp : b.orthogonal K = K := by
    symm
    have hle : K ≤ b.orthogonal K := fun x hx =>
      (LinearMap.BilinForm.mem_orthogonal_iff).2 fun n hn => hKK n hn x hx
    refine Submodule.eq_of_le_of_finrank_eq hle ?_
    rw [LinearMap.BilinForm.finrank_orthogonal hb, hE, hK]
    omega
  have hmemperp : ∀ w : E, (∀ k ∈ K, b w k = 0) ↔ w ∈ K := by
    intro w
    constructor
    · intro h
      have hw : w ∈ b.orthogonal K := (LinearMap.BilinForm.mem_orthogonal_iff).2 fun n hn => by
        change b n w = 0
        rw [hsymm]
        exact h n hn
      rwa [hKperp] at hw
    · intro hw k hk
      exact hKK w hw k hk
  have hcardK : (Fintype.card K : ℚ) = 2 ^ m := by
    rw [← FiniteField.pow_finrank_eq_card 2 K, hK]
    push_cast
    rfl
  funext u
  simp only [fourier, lagrangianFun]
  have hre : ∑ v, sgn (b u v) * (if v - a ∈ K then sgn (b a v) else 0) =
      ∑ k : K, sgn (b u (a + k)) * sgn (b a (a + k)) := by
    rw [← Fintype.sum_equiv (Equiv.addLeft a) (fun w => sgn (b u (a + w)) *
      (if a + w - a ∈ K then sgn (b a (a + w)) else 0)) _ (fun w => rfl)]
    simp only [add_sub_cancel_left, mul_ite, mul_zero]
    rw [← Finset.sum_filter]
    exact Finset.sum_subtype _ (fun x => by simp) (fun x => sgn (b u (a + x)) * sgn (b a (a + x)))
  rw [hre]
  have hterm : ∀ k : K, sgn (b u (a + k)) * sgn (b a (a + k)) =
      sgn (b u a) * sgn (b (u + a) k) := by
    intro k
    simp only [map_add, LinearMap.add_apply, halt a, zero_add, sgn_add]
    ring
  rw [Finset.sum_congr rfl (fun k _ => hterm k), ← Finset.mul_sum, sub_eq_add_zmod_two]
  by_cases h : u + a ∈ K
  · rw [ite_eq_left h, sum_sgn_of_perp b K ((hmemperp _).2 h), hcardK, hsymm u a]
    field_simp
  · rw [ite_eq_right h]
    have : ¬ ∀ k ∈ K, b (u + a) k = 0 := fun h' => h ((hmemperp _).1 h')
    simp only [not_forall] at this
    obtain ⟨k₀, hk₀, hne⟩ := this
    rw [sum_sgn_of_not_perp b K hk₀ hne]
    simp

omit [Fintype E] in
theorem signOp_lagrangianFun (b : LinearMap.BilinForm (ZMod 2) E) (K : Submodule (ZMod 2) E)
    [DecidablePred (· ∈ K)] (a : E) (q : E → ZMod 2) (hq : ∀ v, v - a ∈ K → q v = 0) :
    signOp q (lagrangianFun b K a) = lagrangianFun b K a := by
  funext v
  simp only [signOp, lagrangianFun]
  split_ifs with h
  · rw [hq v h, sgn_zero, one_mul]
  · rw [mul_zero]

theorem fourier_signOp_lagrangianFun (b : LinearMap.BilinForm (ZMod 2) E) (hb : b.Nondegenerate)
    (halt : ∀ v, b v v = 0) {m : ℕ} (hE : finrank (ZMod 2) E = 2 * m)
    (K : Submodule (ZMod 2) E) [DecidablePred (· ∈ K)] (hK : finrank (ZMod 2) K = m)
    (hKK : ∀ x ∈ K, ∀ y ∈ K, b x y = 0) (a : E) (q : E → ZMod 2)
    (hq : ∀ v, v - a ∈ K → q v = 0) :
    fourier b m (signOp q (lagrangianFun b K a)) = lagrangianFun b K a := by
  rw [signOp_lagrangianFun b K a q hq, fourier_lagrangianFun b hb halt hE K hK hKK a]

theorem signOp_fourier_lagrangianFun (b : LinearMap.BilinForm (ZMod 2) E) (hb : b.Nondegenerate)
    (halt : ∀ v, b v v = 0) {m : ℕ} (hE : finrank (ZMod 2) E = 2 * m)
    (K : Submodule (ZMod 2) E) [DecidablePred (· ∈ K)] (hK : finrank (ZMod 2) K = m)
    (hKK : ∀ x ∈ K, ∀ y ∈ K, b x y = 0) (a : E) (q : E → ZMod 2)
    (hq : ∀ v, v - a ∈ K → q v = 0) :
    signOp q (fourier b m (lagrangianFun b K a)) = lagrangianFun b K a := by
  rw [fourier_lagrangianFun b hb halt hE K hK hKK a, signOp_lagrangianFun b K a q hq]

end CFSG.Monster

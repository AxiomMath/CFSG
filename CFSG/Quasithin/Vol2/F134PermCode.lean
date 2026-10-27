module

public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Topology.Sheaves.Init

public section

namespace CFSG.Quasithin.F134

open Equiv

@[expose] def ofDigs (b : ℕ) : List ℕ → ℕ
  | [] => 0
  | d :: l => d + b * ofDigs b l

@[expose] def digW (w x i : ℕ) : ℕ := Nat.land (Nat.shiftRight x (Nat.mul w i)) (2 ^ w - 1)

theorem digW_eq (w x i : ℕ) : digW w x i = x / (2 ^ w) ^ i % 2 ^ w := by
  have h : digW w x i = (x >>> (w * i)) &&& (2 ^ w - 1) := rfl
  rw [h, Nat.and_two_pow_sub_one_eq_mod, Nat.shiftRight_eq_div_pow, pow_mul]

theorem div_pow_mod_ofDigs {b : ℕ} (hb : 0 < b) : ∀ (l : List ℕ), (∀ d ∈ l, d < b) →
    ∀ (i : ℕ) (hi : i < l.length), ofDigs b l / b ^ i % b = l[i]
  | [], _, i, hi => absurd hi (by simp)
  | d :: l, hl, 0, _ => by
      simp only [ofDigs, pow_zero, Nat.div_one, List.getElem_cons_zero]
      rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (hl d List.mem_cons_self)]
  | d :: l, hl, i + 1, hi => by
      simp only [List.getElem_cons_succ]
      have hd : d < b := hl d List.mem_cons_self
      rw [pow_succ', ← Nat.div_div_eq_div_mul, ofDigs, Nat.add_mul_div_left _ _ hb,
        Nat.div_eq_of_lt hd, zero_add]
      exact div_pow_mod_ofDigs hb l (fun d' hd' => hl d' (List.mem_cons_of_mem _ hd')) i
        (by simpa using hi)

theorem digW_ofDigs {w : ℕ} (l : List ℕ) (hl : ∀ d ∈ l, d < 2 ^ w) (i : ℕ) (hi : i < l.length) :
    digW w (ofDigs (2 ^ w) l) i = l[i] := by
  rw [digW_eq]
  exact div_pow_mod_ofDigs (by positivity) l hl i hi

@[expose] def permCode {n : ℕ} (σ : Perm (Fin n)) : ℕ :=
  ofDigs (2 ^ 5) (List.ofFn fun i => (σ i : ℕ))

theorem digW_permCode {n : ℕ} (hn : n ≤ 32) (σ : Perm (Fin n)) (i : Fin n) :
    digW 5 (permCode σ) i = σ i := by
  have hl : ∀ d ∈ List.ofFn (fun j => (σ j : ℕ)), d < 2 ^ 5 := by
    intro d hd
    obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hd
    have := (σ j).2
    norm_num
    omega
  rw [permCode, digW_ofDigs _ hl i (by simp)]
  simp

theorem permCode_injective {n : ℕ} (hn : n ≤ 32) :
    Function.Injective (permCode : Perm (Fin n) → ℕ) := by
  intro σ τ h
  ext i
  rw [← digW_permCode hn σ i, ← digW_permCode hn τ i, h]

@[expose] def dig5 (x i : ℕ) : ℕ := Nat.land (Nat.shiftRight x (Nat.mul 5 i)) 31

@[expose] def mul22 (x y : ℕ) : ℕ :=
  Nat.add (dig5 x (dig5 y 0)) (Nat.mul 32 (Nat.add (dig5 x (dig5 y 1)) (Nat.mul 32 (Nat.add (dig5 x
  (dig5 y 2)) (Nat.mul 32 (Nat.add (dig5 x (dig5 y 3)) (Nat.mul 32 (Nat.add (dig5 x (dig5 y 4))
  (Nat.mul 32 (Nat.add (dig5 x (dig5 y 5)) (Nat.mul 32 (Nat.add (dig5 x (dig5 y 6)) (Nat.mul 32
  (Nat.add (dig5 x (dig5 y 7)) (Nat.mul 32 (Nat.add (dig5 x (dig5 y 8)) (Nat.mul 32 (Nat.add (dig5 x
  (dig5 y 9)) (Nat.mul 32 (Nat.add (dig5 x (dig5 y 10)) (Nat.mul 32 (Nat.add (dig5 x (dig5 y 11))
  (Nat.mul 32 (Nat.add (dig5 x (dig5 y 12)) (Nat.mul 32 (Nat.add (dig5 x (dig5 y 13)) (Nat.mul 32
  (Nat.add (dig5 x (dig5 y 14)) (Nat.mul 32 (Nat.add (dig5 x (dig5 y 15)) (Nat.mul 32 (Nat.add (dig5
  x (dig5 y 16)) (Nat.mul 32 (Nat.add (dig5 x (dig5 y 17)) (Nat.mul 32 (Nat.add (dig5 x (dig5 y 18))
  (Nat.mul 32 (Nat.add (dig5 x (dig5 y 19)) (Nat.mul 32 (Nat.add (dig5 x (dig5 y 20)) (Nat.mul 32
  (Nat.add (dig5 x (dig5 y 21)) (Nat.mul 32 0)))))))))))))))))))))))))))))))))))))))))))

theorem mul22_eq (x y : ℕ) :
    mul22 x y = ofDigs (2 ^ 5) (List.ofFn fun k : Fin 22 => digW 5 x (digW 5 y k)) := by
  simp only [List.ofFn_succ, List.ofFn_zero, ofDigs]
  rfl

theorem permCode_mul22 (σ τ : Perm (Fin 22)) :
    permCode (σ * τ) = mul22 (permCode σ) (permCode τ) := by
  rw [mul22_eq]
  have key : ∀ k : Fin 22, digW 5 (permCode σ) (digW 5 (permCode τ) k) = ((σ * τ) k : ℕ) := by
    intro k
    rw [digW_permCode (by norm_num) τ k, digW_permCode (by norm_num) σ (τ k)]
    rfl
  simp only [key]
  rfl

@[expose] def powC (one : ℕ) : ℕ → ℕ → ℕ
  | 0, _ => one
  | n + 1, x => mul22 (powC one n x) x

theorem permCode_pow (σ : Perm (Fin 22)) (n : ℕ) :
    permCode (σ ^ n) = powC (permCode (1 : Perm (Fin 22))) n (permCode σ) := by
  induction n with
  | zero => rfl
  | succ n ih => rw [pow_succ, permCode_mul22, ih, powC]

@[expose] def sqC : ℕ → ℕ → ℕ
  | 0, x => x
  | n + 1, x => sqC n (mul22 x x)

theorem permCode_pow_two_pow (n : ℕ) : ∀ σ : Perm (Fin 22),
    permCode (σ ^ 2 ^ n) = sqC n (permCode σ) := by
  induction n with
  | zero => intro σ; rw [pow_zero, pow_one]; rfl
  | succ n ih =>
    intro σ
    rw [pow_succ', pow_mul, sq, ih, permCode_mul22]
    rfl

end CFSG.Quasithin.F134

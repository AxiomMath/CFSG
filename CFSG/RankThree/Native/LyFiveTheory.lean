module

public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
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
public import Mathlib.RingTheory.PiTensorProduct
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.WittVector.IsPoly
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
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init

public noncomputable section

namespace CFSG.RankThree.Native

open Subgroup
open scoped commutatorElement

variable {G : Type*} [Group G]

section Calculus

theorem mul_eq_commutator_mul (s g : G) : s * g = ⁅s, g⁆ * g * s := by
  rw [commutatorElement_def]; group

theorem commutator_mul_left_of_commute {g g' s : G} (h : Commute ⁅g', s⁆ g) :
    ⁅g * g', s⁆ = ⁅g', s⁆ * ⁅g, s⁆ := by
  have e : ⁅g * g', s⁆ = g * ⁅g', s⁆ * g⁻¹ * ⁅g, s⁆ := by
    simp only [commutatorElement_def]; group
  rw [e, h.symm.eq]; group

theorem commutator_inv_left_of_commute {g s : G} (h : Commute ⁅g, s⁆ g) :
    ⁅g⁻¹, s⁆ = ⁅g, s⁆⁻¹ := by
  have e : ⁅g⁻¹, s⁆ = g⁻¹ * ⁅g, s⁆⁻¹ * g := by
    simp only [commutatorElement_def]; group
  rw [e, mul_assoc, (h.inv_left).eq, ← mul_assoc, inv_mul_cancel, one_mul]

theorem commutator_mul_right_of_commute {g h h' : G} (hc : Commute ⁅g, h'⁆ h) :
    ⁅g, h * h'⁆ = ⁅g, h⁆ * ⁅g, h'⁆ := by
  have e : ⁅g, h * h'⁆ = ⁅g, h⁆ * h * ⁅g, h'⁆ * h⁻¹ := by
    simp only [commutatorElement_def]; group
  rw [e, mul_assoc (⁅g, h⁆ * h), (hc.inv_right).eq]; group

theorem commutator_inv_right_of_commute {g h : G} (hc : Commute ⁅g, h⁆ h) :
    ⁅g, h⁻¹⁆ = ⁅g, h⁆⁻¹ := by
  have e : ⁅g, h⁻¹⁆ = h⁻¹ * ⁅g, h⁆⁻¹ * h := by
    simp only [commutatorElement_def]; group
  rw [e, mul_assoc, (hc.inv_left).eq, ← mul_assoc, inv_mul_cancel, one_mul]

theorem commutator_pow_left_of_commute {g s : G} (h : Commute ⁅g, s⁆ g) (n : ℕ) :
    ⁅g ^ n, s⁆ = ⁅g, s⁆ ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', commutator_mul_left_of_commute (by rw [ih]; exact h.pow_left n), ih, pow_succ]

theorem commutator_pow_right_of_commute {g h : G} (hc : Commute ⁅g, h⁆ h) (n : ℕ) :
    ⁅g, h ^ n⁆ = ⁅g, h⁆ ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, commutator_mul_right_of_commute (hc.pow_right n), ih, pow_succ]

theorem pow_mul_eq_of_commute {g h : G} (hh : Commute ⁅h, g⁆ h) (m : ℕ) :
    h ^ m * g = ⁅h, g⁆ ^ m * g * h ^ m := by
  induction m with
  | zero => simp
  | succ m ih =>
    have e1 : h ^ (m + 1) * g = h ^ m * (⁅h, g⁆ * g * h) := by
      rw [pow_succ, mul_assoc, ← mul_eq_commutator_mul h g]
    have e2 : h ^ m * (⁅h, g⁆ * g * h) = ⁅h, g⁆ * (h ^ m * g) * h := by
      rw [show h ^ m * (⁅h, g⁆ * g * h) = (h ^ m * ⁅h, g⁆) * g * h by simp only [mul_assoc],
        ← (hh.pow_right m).eq]
      simp only [mul_assoc]
    rw [e1, e2, ih, pow_succ', pow_succ]
    simp only [mul_assoc]

theorem mul_pow_of_commute {g h : G} (hg : Commute ⁅h, g⁆ g) (hh : Commute ⁅h, g⁆ h) (n : ℕ) :
    (g * h) ^ n = g ^ n * h ^ n * ⁅h, g⁆ ^ n.choose 2 := by
  induction n with
  | zero => simp
  | succ n ih =>
    set z := ⁅h, g⁆ with hz
    set T := z ^ n.choose 2 with hT
    have hzgh : Commute T (g * h) := (hg.mul_right hh).pow_left _
    have hzn : Commute (z ^ n) (g ^ (n + 1) * h ^ (n + 1)) :=
      ((hg.pow_right _).mul_right (hh.pow_right _)).pow_left n
    have hzng : Commute (z ^ n) (g ^ n) := (hg.pow_right n).pow_left n
    rw [Nat.choose_succ_succ, Nat.choose_one_right, pow_succ, ih]
    calc g ^ n * h ^ n * T * (g * h) = g ^ n * h ^ n * (g * h) * T := by
          rw [mul_assoc (g ^ n * h ^ n) T, hzgh.eq, ← mul_assoc]
      _ = g ^ n * (h ^ n * g) * h * T := by simp only [mul_assoc]
      _ = g ^ n * (z ^ n * g * h ^ n) * h * T := by rw [pow_mul_eq_of_commute hh n]
      _ = z ^ n * (g ^ n * g) * (h ^ n * h) * T := by
          rw [show g ^ n * (z ^ n * g * h ^ n) * h * T = (g ^ n * z ^ n) * g * h ^ n * h * T by
            simp only [mul_assoc], hzng.symm.eq]
          simp only [mul_assoc]
      _ = z ^ n * (g ^ (n + 1) * h ^ (n + 1)) * T := by
          rw [← pow_succ, ← pow_succ]; simp only [mul_assoc]
      _ = g ^ (n + 1) * h ^ (n + 1) * z ^ (n + n.choose 2) := by
          rw [hzn.eq, pow_add z n (n.choose 2), ← hT]; simp only [mul_assoc]

end Calculus

@[expose] def fiveNF (x : G) (v : Fin 4 → G) (c : ZMod 5) (e : Fin 4 → ZMod 5) : G :=
  v 3 ^ (e 3).val * v 2 ^ (e 2).val * v 1 ^ (e 1).val * v 0 ^ (e 0).val * x ^ c.val

@[expose] def fiveQ (x : G) (v : Fin 4 → G) : Subgroup G := closure (insert x (Set.range v))

structure FiveQRel (x : G) (v : Fin 4 → G) (ω : Fin 4 → Fin 4 → ZMod 5) : Prop where
  x5 : x ^ 5 = 1
  x1 : x ≠ 1
  v5 : ∀ i, v i ^ 5 = 1
  xv : ∀ i, x * v i = v i * x
  comm : ∀ i j, ⁅v i, v j⁆ = x ^ (ω i j).val
  nondeg : ∀ e : Fin 4 → ZMod 5, (∀ j, ∑ i, e i * ω i j = 0) → e = 0

theorem pow_mod_five {g : G} (hg : g ^ 5 = 1) (n : ℕ) : g ^ (n % 5) = g ^ n := by
  conv_rhs => rw [← Nat.div_add_mod n 5, pow_add, pow_mul, hg, one_pow, one_mul]

theorem zmod5_val_add_one (a : ZMod 5) : (a + 1).val = (a.val + 1) % 5 := by
  revert a; decide

namespace FiveQRel

variable {x : G} {v : Fin 4 → G} {ω : Fin 4 → Fin 4 → ZMod 5}

theorem x_mem : x ∈ fiveQ x v := subset_closure (Set.mem_insert _ _)

theorem v_mem (i : Fin 4) : v i ∈ fiveQ x v :=
  subset_closure (Set.mem_insert_of_mem _ ⟨i, rfl⟩)

theorem pow_mem {g : G} (hg : g ∈ fiveQ x v) (n : ℕ) : g ^ n ∈ fiveQ x v :=
  Subgroup.pow_mem _ hg n

variable (h : FiveQRel x v ω)
include h

theorem orderOf_x : orderOf x = 5 := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  exact orderOf_eq_prime h.x5 h.x1

theorem x_pow_eq_one_iff (n : ℕ) : x ^ n = 1 ↔ (n : ZMod 5) = 0 := by
  rw [← orderOf_dvd_iff_pow_eq_one, h.orderOf_x, ZMod.natCast_eq_zero_iff]

theorem x_comm {g : G} (hg : g ∈ fiveQ x v) : Commute x g := by
  induction hg using Subgroup.closure_induction with
  | mem y hy =>
    rcases hy with rfl | ⟨i, rfl⟩
    · exact Commute.refl _
    · exact h.xv i
  | one => exact Commute.one_right _
  | mul _ _ _ _ h1 h2 => exact h1.mul_right h2
  | inv _ _ h1 => exact h1.inv_right

theorem zpowers_comm {z g : G} (hz : z ∈ zpowers x) (hg : g ∈ fiveQ x v) : Commute z g := by
  obtain ⟨k, rfl⟩ := hz
  exact (h.x_comm hg).zpow_left k

theorem comm_gen_mem {g : G} (hg : g ∈ fiveQ x v) {s : G} (hs : s ∈ insert x (Set.range v)) :
    ⁅g, s⁆ ∈ zpowers x := by
  induction hg using Subgroup.closure_induction with
  | mem y hy =>
    rcases hy with rfl | ⟨i, rfl⟩ <;> rcases hs with rfl | ⟨j, rfl⟩
    · rw [commutatorElement_self]; exact one_mem _
    · rw [commutatorElement_eq_one_iff_mul_comm.2 (h.xv j)]; exact one_mem _
    · rw [commutatorElement_eq_one_iff_mul_comm.2 (h.xv i).symm]; exact one_mem _
    · rw [h.comm i j]; exact npow_mem_zpowers x _
  | one => rw [commutatorElement_one_left]; exact one_mem _
  | mul a b ha hb iha ihb =>
    rw [commutator_mul_left_of_commute (h.zpowers_comm ihb ha)]
    exact mul_mem ihb iha
  | inv a ha iha =>
    rw [commutator_inv_left_of_commute (h.zpowers_comm iha ha)]
    exact inv_mem iha

theorem comm_mem {g k : G} (hg : g ∈ fiveQ x v) (hk : k ∈ fiveQ x v) : ⁅g, k⁆ ∈ zpowers x := by
  induction hk using Subgroup.closure_induction with
  | mem s hs => exact h.comm_gen_mem hg hs
  | one => rw [commutatorElement_one_right]; exact one_mem _
  | mul a b ha hb iha ihb =>
    rw [commutator_mul_right_of_commute (h.zpowers_comm ihb ha)]
    exact mul_mem iha ihb
  | inv a ha iha =>
    rw [commutator_inv_right_of_commute (h.zpowers_comm iha ha)]
    exact inv_mem iha

theorem comm_comm {g k m : G} (hg : g ∈ fiveQ x v) (hk : k ∈ fiveQ x v)
    (hm : m ∈ fiveQ x v) : Commute ⁅g, k⁆ m :=
  h.zpowers_comm (h.comm_mem hg hk) hm

omit h in
theorem nf_mem (c : ZMod 5) (e : Fin 4 → ZMod 5) : fiveNF x v c e ∈ fiveQ x v := by
  unfold fiveNF
  exact mul_mem (mul_mem (mul_mem (mul_mem (pow_mem (v_mem 3) _) (pow_mem (v_mem 2) _))
    (pow_mem (v_mem 1) _)) (pow_mem (v_mem 0) _)) (pow_mem x_mem _)

theorem comm_v_pow (i j : Fin 4) (n : ℕ) : ⁅v i ^ n, v j⁆ = x ^ ((ω i j).val * n) := by
  rw [commutator_pow_left_of_commute (h.comm_comm (v_mem (x := x) i) (v_mem j) (v_mem i)), h.comm,
    pow_mul]

theorem comm_x_pow (n : ℕ) (j : Fin 4) : ⁅x ^ n, v j⁆ = 1 := by
  rw [commutatorElement_eq_one_iff_mul_comm]
  exact ((h.x_comm (v_mem (x := x) j)).pow_left n).eq

theorem comm_nf (c : ZMod 5) (e : Fin 4 → ZMod 5) (j : Fin 4) :
    ⁅fiveNF x v c e, v j⁆ =
      x ^ ((ω 0 j).val * (e 0).val + (ω 1 j).val * (e 1).val + (ω 2 j).val * (e 2).val +
        (ω 3 j).val * (e 3).val) := by
  have hm : ∀ {g s : G}, g ∈ fiveQ x v → s ∈ fiveQ x v → ∀ k ∈ fiveQ x v,
      Commute ⁅g, s⁆ k := fun hg hs k hk => h.comm_comm hg hs hk
  have hv : ∀ i, v i ∈ fiveQ x v := fun i => v_mem i
  have hvj := hv j
  have h3 := pow_mem (hv 3) (e 3).val
  have h2 := pow_mem (hv 2) (e 2).val
  have h1 := pow_mem (hv 1) (e 1).val
  have h0 := pow_mem (hv 0) (e 0).val
  have hx := pow_mem (x_mem (x := x) (v := v)) c.val
  unfold fiveNF
  rw [commutator_mul_left_of_commute (hm hx hvj _ (mul_mem (mul_mem (mul_mem h3 h2) h1) h0)),
    h.comm_x_pow, one_mul,
    commutator_mul_left_of_commute (hm h0 hvj _ (mul_mem (mul_mem h3 h2) h1)),
    commutator_mul_left_of_commute (hm h1 hvj _ (mul_mem h3 h2)),
    commutator_mul_left_of_commute (hm h2 hvj _ h3),
    h.comm_v_pow, h.comm_v_pow, h.comm_v_pow, h.comm_v_pow, ← pow_add, ← pow_add, ← pow_add]
  congr 1
  ring

theorem comm_nf_eq_one_iff (c : ZMod 5) (e : Fin 4 → ZMod 5) (j : Fin 4) :
    ⁅fiveNF x v c e, v j⁆ = 1 ↔ ∑ i, e i * ω i j = 0 := by
  rw [h.comm_nf, h.x_pow_eq_one_iff, Fin.sum_univ_four]
  push_cast
  simp only [ZMod.natCast_val, ZMod.cast_id', id]
  constructor <;> intro hs <;> linear_combination hs

theorem coord_eq_of_comm {c c' : ZMod 5} {e e' : Fin 4 → ZMod 5}
    (hcomm : ∀ j, ⁅fiveNF x v c e, v j⁆ = ⁅fiveNF x v c' e', v j⁆) : e = e' := by
  have hd : e - e' = 0 := by
    apply h.nondeg
    intro j
    have hj := hcomm j
    rw [h.comm_nf, h.comm_nf] at hj
    have h5 := h.orderOf_x
    have := (pow_eq_pow_iff_modEq.1 hj)
    rw [h5] at this
    have hz := (ZMod.natCast_eq_natCast_iff _ _ 5).2 this
    push_cast at hz
    simp only [ZMod.natCast_val, ZMod.cast_id', id] at hz
    simp only [Pi.sub_apply, sub_mul, Finset.sum_sub_distrib, Fin.sum_univ_four]
    linear_combination hz
  exact sub_eq_zero.1 hd

theorem xpow_comm (k : ℕ) {g : G} (hg : g ∈ fiveQ x v) : x ^ k * g = g * x ^ k :=
  ((h.x_comm hg).pow_left k).eq

theorem xpow_mul_nf (m : ℕ) (c : ZMod 5) (e : Fin 4 → ZMod 5) :
    x ^ m * fiveNF x v c e = fiveNF x v (c + m) e := by
  have hv : ∀ i, v i ∈ fiveQ x v := fun i => v_mem i
  have hP : v 3 ^ (e 3).val * v 2 ^ (e 2).val * v 1 ^ (e 1).val * v 0 ^ (e 0).val ∈ fiveQ x v :=
    mul_mem (mul_mem (mul_mem (pow_mem (hv 3) _) (pow_mem (hv 2) _)) (pow_mem (hv 1) _))
      (pow_mem (hv 0) _)
  unfold fiveNF
  rw [← mul_assoc, h.xpow_comm m hP, mul_assoc, ← pow_add, ZMod.val_add, ZMod.val_natCast,
    Nat.add_mod_mod, pow_mod_five h.x5, Nat.add_comm]

theorem v_mul_vpow (i j : Fin 4) (a : ℕ) :
    v i * v j ^ a = x ^ ((ω i j).val * a) * v j ^ a * v i := by
  rw [mul_eq_commutator_mul, commutator_pow_right_of_commute
    (h.comm_comm (v_mem (x := x) i) (v_mem j) (v_mem j)), h.comm, ← pow_mul]

@[expose] def fiveBump (e : Fin 4 → ZMod 5) (i : Fin 4) : Fin 4 → ZMod 5 :=
  fun k => if k = i then e k + 1 else e k

omit h in
theorem single_val (i k : Fin 4) (e : Fin 4 → ZMod 5) :
    (fiveBump e i k).val = if k = i then ((e k).val + 1) % 5 else (e k).val := by
  unfold fiveBump
  split_ifs
  · exact zmod5_val_add_one _
  · rfl

theorem v3_mul_nf (c : ZMod 5) (e : Fin 4 → ZMod 5) :
    v 3 * fiveNF x v c e = fiveNF x v c (fiveBump e 3) := by
  unfold fiveNF
  rw [single_val, single_val, single_val, single_val]
  simp only [show (2 : Fin 4) ≠ 3 by decide, show (1 : Fin 4) ≠ 3 by decide,
    show (0 : Fin 4) ≠ 3 by decide, ite_true, ite_false]
  rw [pow_mod_five (h.v5 3), pow_succ']
  simp only [mul_assoc]

theorem v2_mul_nf (c : ZMod 5) (e : Fin 4 → ZMod 5) :
    ∃ c', v 2 * fiveNF x v c e = fiveNF x v c' (fiveBump e 2) := by
  refine ⟨c + ((ω 2 3).val * (e 3).val : ℕ), ?_⟩
  rw [← h.xpow_mul_nf]
  unfold fiveNF
  rw [single_val, single_val, single_val, single_val]
  simp only [show (3 : Fin 4) ≠ 2 by decide, show (1 : Fin 4) ≠ 2 by decide,
    show (0 : Fin 4) ≠ 2 by decide, ite_true, ite_false]
  rw [pow_mod_five (h.v5 2)]
  calc v 2 * (v 3 ^ (e 3).val * v 2 ^ (e 2).val * v 1 ^ (e 1).val * v 0 ^ (e 0).val *
        x ^ c.val) = (v 2 * v 3 ^ (e 3).val) * v 2 ^ (e 2).val * v 1 ^ (e 1).val *
          v 0 ^ (e 0).val * x ^ c.val := by simp only [mul_assoc]
    _ = _ := by
        rw [h.v_mul_vpow, pow_succ' (v 2)]
        simp only [mul_assoc]

theorem v1_mul_nf (c : ZMod 5) (e : Fin 4 → ZMod 5) :
    ∃ c', v 1 * fiveNF x v c e = fiveNF x v c' (fiveBump e 1) := by
  refine ⟨c + ((ω 1 3).val * (e 3).val + (ω 1 2).val * (e 2).val : ℕ), ?_⟩
  rw [← h.xpow_mul_nf]
  unfold fiveNF
  rw [single_val, single_val, single_val, single_val]
  simp only [show (3 : Fin 4) ≠ 1 by decide, show (2 : Fin 4) ≠ 1 by decide,
    show (0 : Fin 4) ≠ 1 by decide, ite_true, ite_false]
  rw [pow_mod_five (h.v5 1)]
  have h3 : v 3 ^ (e 3).val ∈ fiveQ x v := pow_mem (v_mem 3) _
  calc v 1 * (v 3 ^ (e 3).val * v 2 ^ (e 2).val * v 1 ^ (e 1).val * v 0 ^ (e 0).val *
        x ^ c.val) = (v 1 * v 3 ^ (e 3).val) * v 2 ^ (e 2).val * v 1 ^ (e 1).val *
          v 0 ^ (e 0).val * x ^ c.val := by simp only [mul_assoc]
    _ = x ^ ((ω 1 3).val * (e 3).val) * v 3 ^ (e 3).val * (v 1 * v 2 ^ (e 2).val) *
          v 1 ^ (e 1).val * v 0 ^ (e 0).val * x ^ c.val := by
        rw [h.v_mul_vpow]; simp only [mul_assoc]
    _ = x ^ ((ω 1 3).val * (e 3).val) * (v 3 ^ (e 3).val * x ^ ((ω 1 2).val * (e 2).val)) *
          v 2 ^ (e 2).val * (v 1 * v 1 ^ (e 1).val) * v 0 ^ (e 0).val * x ^ c.val := by
        rw [h.v_mul_vpow]; simp only [mul_assoc]
    _ = _ := by
        rw [← h.xpow_comm _ h3, ← pow_succ' (v 1),
          pow_add x ((ω 1 3).val * (e 3).val) ((ω 1 2).val * (e 2).val)]
        simp only [mul_assoc]

theorem v0_mul_nf (c : ZMod 5) (e : Fin 4 → ZMod 5) :
    ∃ c', v 0 * fiveNF x v c e = fiveNF x v c' (fiveBump e 0) := by
  refine ⟨c + ((ω 0 3).val * (e 3).val + (ω 0 2).val * (e 2).val +
    (ω 0 1).val * (e 1).val : ℕ), ?_⟩
  rw [← h.xpow_mul_nf]
  unfold fiveNF
  rw [single_val, single_val, single_val, single_val]
  simp only [show (3 : Fin 4) ≠ 0 by decide, show (2 : Fin 4) ≠ 0 by decide,
    show (1 : Fin 4) ≠ 0 by decide, ite_true, ite_false]
  rw [pow_mod_five (h.v5 0)]
  have h3 : v 3 ^ (e 3).val ∈ fiveQ x v := pow_mem (v_mem 3) _
  have h2 : v 2 ^ (e 2).val ∈ fiveQ x v := pow_mem (v_mem 2) _
  calc v 0 * (v 3 ^ (e 3).val * v 2 ^ (e 2).val * v 1 ^ (e 1).val * v 0 ^ (e 0).val *
        x ^ c.val) = (v 0 * v 3 ^ (e 3).val) * v 2 ^ (e 2).val * v 1 ^ (e 1).val *
          v 0 ^ (e 0).val * x ^ c.val := by simp only [mul_assoc]
    _ = x ^ ((ω 0 3).val * (e 3).val) * v 3 ^ (e 3).val * (v 0 * v 2 ^ (e 2).val) *
          v 1 ^ (e 1).val * v 0 ^ (e 0).val * x ^ c.val := by
        rw [h.v_mul_vpow]; simp only [mul_assoc]
    _ = x ^ ((ω 0 3).val * (e 3).val) * (v 3 ^ (e 3).val * x ^ ((ω 0 2).val * (e 2).val)) *
          v 2 ^ (e 2).val * (v 0 * v 1 ^ (e 1).val) * v 0 ^ (e 0).val * x ^ c.val := by
        rw [h.v_mul_vpow]; simp only [mul_assoc]
    _ = x ^ ((ω 0 3).val * (e 3).val) * (v 3 ^ (e 3).val * x ^ ((ω 0 2).val * (e 2).val)) *
          (v 2 ^ (e 2).val * x ^ ((ω 0 1).val * (e 1).val)) * v 1 ^ (e 1).val *
          (v 0 * v 0 ^ (e 0).val) * x ^ c.val := by
        rw [h.v_mul_vpow]; simp only [mul_assoc]
    _ = _ := by
        rw [← h.xpow_comm _ h3, ← h.xpow_comm _ h2,
          show x ^ ((ω 0 3).val * (e 3).val) * (x ^ ((ω 0 2).val * (e 2).val) * v 3 ^ (e 3).val) *
            (x ^ ((ω 0 1).val * (e 1).val) * v 2 ^ (e 2).val) * v 1 ^ (e 1).val *
            (v 0 * v 0 ^ (e 0).val) * x ^ c.val =
            x ^ ((ω 0 3).val * (e 3).val) * x ^ ((ω 0 2).val * (e 2).val) *
            (v 3 ^ (e 3).val * x ^ ((ω 0 1).val * (e 1).val)) * v 2 ^ (e 2).val *
            v 1 ^ (e 1).val * (v 0 * v 0 ^ (e 0).val) * x ^ c.val by simp only [mul_assoc],
          ← h.xpow_comm _ h3, ← pow_succ' (v 0),
          pow_add x ((ω 0 3).val * (e 3).val + (ω 0 2).val * (e 2).val)
            ((ω 0 1).val * (e 1).val),
          pow_add x ((ω 0 3).val * (e 3).val) ((ω 0 2).val * (e 2).val)]
        simp only [mul_assoc]

omit h in
theorem gen_pow_five' (h5 : FiveQRel x v ω) {s : G} (hs : s ∈ insert x (Set.range v)) :
    s ^ 5 = 1 := by
  rcases hs with rfl | ⟨i, rfl⟩
  · exact h5.x5
  · exact h5.v5 i

theorem gen_mul_nf {s : G} (hs : s ∈ insert x (Set.range v)) (c : ZMod 5)
    (e : Fin 4 → ZMod 5) : ∃ c' e', s * fiveNF x v c e = fiveNF x v c' e' := by
  rcases hs with rfl | ⟨i, rfl⟩
  · exact ⟨c + ((1 : ℕ) : ZMod 5), e, by rw [← h.xpow_mul_nf, pow_one]⟩
  · match i with
    | 0 => obtain ⟨c', hc⟩ := h.v0_mul_nf c e; exact ⟨c', _, hc⟩
    | 1 => obtain ⟨c', hc⟩ := h.v1_mul_nf c e; exact ⟨c', _, hc⟩
    | 2 => obtain ⟨c', hc⟩ := h.v2_mul_nf c e; exact ⟨c', _, hc⟩
    | 3 => exact ⟨c, _, h.v3_mul_nf c e⟩

omit h in
theorem nf_zero : fiveNF x v 0 0 = 1 := by simp [fiveNF]

theorem mem_range_nf {g : G} (hg : g ∈ fiveQ x v) : ∃ c e, g = fiveNF x v c e := by
  induction hg using Subgroup.closure_induction_left with
  | one => exact ⟨0, 0, nf_zero.symm⟩
  | mul_left s hs y _ ih =>
    obtain ⟨c, e, rfl⟩ := ih
    obtain ⟨c', e', he⟩ := h.gen_mul_nf hs c e
    exact ⟨c', e', he⟩
  | inv_mul_cancel s hs y _ ih =>
    obtain ⟨c, e, rfl⟩ := ih
    have hinv : s⁻¹ = s * (s * (s * s)) := by
      rw [inv_eq_iff_mul_eq_one, ← h.gen_pow_five' hs]
      simp only [pow_succ, pow_zero, one_mul, mul_assoc]
    obtain ⟨c1, e1, h1⟩ := h.gen_mul_nf hs c e
    obtain ⟨c2, e2, h2⟩ := h.gen_mul_nf hs c1 e1
    obtain ⟨c3, e3, h3⟩ := h.gen_mul_nf hs c2 e2
    obtain ⟨c4, e4, h4⟩ := h.gen_mul_nf hs c3 e3
    exact ⟨c4, e4, by rw [hinv, mul_assoc, mul_assoc, mul_assoc, h1, h2, h3, h4]⟩

theorem nf_injective :
    Function.Injective fun p : ZMod 5 × (Fin 4 → ZMod 5) => fiveNF x v p.1 p.2 := by
  rintro ⟨c, e⟩ ⟨c', e'⟩ hEq
  simp only at hEq
  have he : e = e' := h.coord_eq_of_comm fun j => by rw [hEq]
  subst he
  have hx : x ^ c.val = x ^ c'.val := by
    unfold fiveNF at hEq
    exact mul_left_cancel hEq
  have hmod := pow_eq_pow_iff_modEq.1 hx
  rw [h.orderOf_x] at hmod
  have : c = c' := ZMod.val_injective _ (Nat.ModEq.eq_of_lt_of_lt hmod (ZMod.val_lt c)
    (ZMod.val_lt c'))
  rw [this]

@[expose] def nfEquiv : ZMod 5 × (Fin 4 → ZMod 5) ≃ fiveQ x v :=
  Equiv.ofBijective (fun p => ⟨fiveNF x v p.1 p.2, nf_mem p.1 p.2⟩)
    ⟨fun p q e => h.nf_injective (congrArg Subtype.val e), fun g => by
      obtain ⟨c, e, he⟩ := h.mem_range_nf g.2
      exact ⟨(c, e), Subtype.ext he.symm⟩⟩

theorem nfEquiv_apply (p : ZMod 5 × (Fin 4 → ZMod 5)) :
    (h.nfEquiv p : G) = fiveNF x v p.1 p.2 := rfl

theorem card_fiveQ : Nat.card (fiveQ x v) = 3125 := by
  rw [← Nat.card_congr h.nfEquiv, Nat.card_eq_fintype_card, Fintype.card_prod,
    Fintype.card_fun, ZMod.card, Fintype.card_fin]
  norm_num

theorem zpowers_pow_five {z : G} (hz : z ∈ zpowers x) : z ^ 5 = 1 := by
  obtain ⟨k, rfl⟩ := hz
  rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, h.x5, one_zpow]

theorem pow_five_of_mem {g : G} (hg : g ∈ fiveQ x v) : g ^ 5 = 1 := by
  induction hg using Subgroup.closure_induction with
  | mem s hs => exact h.gen_pow_five' hs
  | one => exact one_pow 5
  | mul a b ha hb iha ihb =>
    rw [mul_pow_of_commute (h.comm_comm hb ha ha) (h.comm_comm hb ha hb), iha, ihb, one_mul,
      one_mul, show Nat.choose 5 2 = 5 * 2 by decide, pow_mul, h.zpowers_pow_five
        (h.comm_mem hb ha), one_pow]
  | inv a ha iha => rw [inv_pow, iha, inv_one]

theorem exponent_fiveQ : Monoid.exponent (fiveQ x v) = 5 := by
  have hdvd : Monoid.exponent (fiveQ x v) ∣ 5 :=
    Monoid.exponent_dvd_of_forall_pow_eq_one fun g => Subtype.ext (h.pow_five_of_mem g.2)
  rcases (Nat.dvd_prime (by norm_num : Nat.Prime 5)).1 hdvd with he | he
  · exfalso
    have hs := Monoid.exp_eq_one_iff.1 he
    have : (⟨x, x_mem⟩ : fiveQ x v) = 1 := Subsingleton.elim _ _
    exact h.x1 (congrArg Subtype.val this)
  · exact he

@[expose] def fiveForm (ω : Fin 4 → Fin 4 → ZMod 5) (e : Fin 4 → ZMod 5) (j : Fin 4) : ZMod 5 :=
  ∑ i, e i * ω i j

theorem x_pow_eq_x_pow_val (n : ℕ) : x ^ n = x ^ ((n : ZMod 5).val) := by
  rw [ZMod.val_natCast, pow_mod_five h.x5]

theorem comm_nf' (c : ZMod 5) (e : Fin 4 → ZMod 5) (j : Fin 4) :
    ⁅fiveNF x v c e, v j⁆ = x ^ (fiveForm ω e j).val := by
  rw [h.comm_nf, h.x_pow_eq_x_pow_val, fiveForm, Fin.sum_univ_four]
  push_cast
  simp only [ZMod.natCast_val, ZMod.cast_id', id]
  congr 2
  ring

theorem x_pow_val_inj {a b : ZMod 5} (hab : x ^ a.val = x ^ b.val) : a = b := by
  have hmod := pow_eq_pow_iff_modEq.1 hab
  rw [h.orderOf_x] at hmod
  exact ZMod.val_injective _ (Nat.ModEq.eq_of_lt_of_lt hmod (ZMod.val_lt a) (ZMod.val_lt b))

theorem fiveForm_injective : Function.Injective (fiveForm ω) := by
  intro e e' he
  have : e - e' = 0 := h.nondeg _ fun j => by
    have := congrFun he j
    simp only [fiveForm] at this
    simp only [Pi.sub_apply, sub_mul, Finset.sum_sub_distrib, this, sub_self]
  exact sub_eq_zero.1 this

omit [Group G] h in
theorem fiveForm_add (e e' : Fin 4 → ZMod 5) :
    fiveForm ω (e + e') = fiveForm ω e + fiveForm ω e' := by
  funext j
  simp only [fiveForm, Pi.add_apply, add_mul, Finset.sum_add_distrib]

@[expose] def coord (g : fiveQ x v) : Fin 4 → ZMod 5 := (h.nfEquiv.symm g).2

theorem coord_nf (c : ZMod 5) (e : Fin 4 → ZMod 5) : h.coord ⟨fiveNF x v c e, nf_mem c e⟩ = e := by
  have : (⟨fiveNF x v c e, nf_mem c e⟩ : fiveQ x v) = h.nfEquiv (c, e) := rfl
  rw [coord, this, Equiv.symm_apply_apply]

theorem eq_nf (g : fiveQ x v) : (g : G) = fiveNF x v (h.nfEquiv.symm g).1 (h.coord g) := by
  conv_lhs => rw [← h.nfEquiv.apply_symm_apply g]
  rfl

theorem comm_coord (g : fiveQ x v) (j : Fin 4) :
    ⁅(g : G), v j⁆ = x ^ (fiveForm ω (h.coord g) j).val := by
  rw [h.eq_nf g, h.comm_nf']

theorem coord_mul (g g' : fiveQ x v) : h.coord (g * g') = h.coord g + h.coord g' := by
  apply h.fiveForm_injective
  funext j
  apply h.x_pow_val_inj
  have e := h.comm_coord (g * g') j
  rw [Subgroup.coe_mul, commutator_mul_left_of_commute (h.comm_comm g'.2 (v_mem j) g.2),
    h.comm_coord, h.comm_coord, ← pow_add] at e
  rw [← e, fiveForm_add, Pi.add_apply, ZMod.val_add, pow_mod_five h.x5, Nat.add_comm]

@[expose] def coordHom : fiveQ x v →* Multiplicative (Fin 4 → ZMod 5) where
  toFun g := Multiplicative.ofAdd (h.coord g)
  map_one' := by
    have : (1 : fiveQ x v) = ⟨fiveNF x v 0 0, nf_mem 0 0⟩ := Subtype.ext nf_zero.symm
    rw [this, h.coord_nf]; rfl
  map_mul' g g' := by rw [h.coord_mul]; rfl

theorem coord_eq_zero_iff (g : fiveQ x v) : h.coord g = 0 ↔ (g : G) ∈ zpowers x := by
  constructor
  · intro hg
    rw [h.eq_nf g, hg, fiveNF]
    simp only [Pi.zero_apply, ZMod.val_zero, pow_zero, one_mul]
    exact npow_mem_zpowers x _
  · intro hg
    apply h.fiveForm_injective
    funext j
    apply h.x_pow_val_inj
    rw [← h.comm_coord, commutatorElement_eq_one_iff_mul_comm.2
      ((h.zpowers_comm hg (v_mem j)).eq)]
    simp [fiveForm]

theorem coordHom_ker : h.coordHom.ker = (zpowers x).subgroupOf (fiveQ x v) := by
  ext g
  rw [MonoidHom.mem_ker, mem_subgroupOf, ← h.coord_eq_zero_iff]
  exact Multiplicative.ofAdd.injective.eq_iff' rfl

theorem coordHom_surjective : Function.Surjective h.coordHom := fun e =>
  ⟨⟨fiveNF x v 0 (Multiplicative.toAdd e), nf_mem _ _⟩, by
    change Multiplicative.ofAdd _ = e
    rw [h.coord_nf]; rfl⟩

theorem zpowers_normal : ((zpowers x).subgroupOf (fiveQ x v)).Normal := by
  rw [← h.coordHom_ker]; infer_instance

@[expose] def quotEquiv [((zpowers x).subgroupOf (fiveQ x v)).Normal] :
    fiveQ x v ⧸ (zpowers x).subgroupOf (fiveQ x v) ≃* Multiplicative (Fin 4 → ZMod 5) :=
  (QuotientGroup.quotientMulEquivOfEq h.coordHom_ker.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective _ h.coordHom_surjective)

theorem quotEquiv_mk [((zpowers x).subgroupOf (fiveQ x v)).Normal] (g : fiveQ x v) :
    h.quotEquiv (g : fiveQ x v ⧸ (zpowers x).subgroupOf (fiveQ x v)) =
      Multiplicative.ofAdd (h.coord g) := rfl

theorem mem_center_iff (g : fiveQ x v) : g ∈ center (fiveQ x v) ↔ (g : G) ∈ zpowers x := by
  constructor
  · intro hg
    rw [← h.coord_eq_zero_iff]
    apply h.fiveForm_injective
    funext j
    apply h.x_pow_val_inj
    rw [← h.comm_coord]
    have := (Subgroup.mem_center_iff.1 hg) ⟨v j, v_mem j⟩
    rw [commutatorElement_eq_one_iff_mul_comm.2 (congrArg Subtype.val this).symm]
    simp [fiveForm]
  · intro hg
    rw [Subgroup.mem_center_iff]
    intro k
    exact Subtype.ext (h.zpowers_comm hg k.2).symm.eq

theorem center_map : (center (fiveQ x v)).map (fiveQ x v).subtype = zpowers x := by
  ext g
  constructor
  · rintro ⟨q, hq, rfl⟩
    exact (h.mem_center_iff q).1 hq
  · intro hg
    have hgQ : g ∈ fiveQ x v := (zpowers_le.2 x_mem) hg
    exact ⟨⟨g, hgQ⟩, (h.mem_center_iff ⟨g, hgQ⟩).2 hg, rfl⟩

theorem card_center : Nat.card (center (fiveQ x v)) = 5 := by
  rw [← card_map_of_injective (fiveQ x v).subtype_injective, h.center_map, Nat.card_zpowers,
    h.orderOf_x]

theorem exists_comm_ne_one : ∃ i j, ⁅v i, v j⁆ ≠ 1 := by
  by_contra hall
  push Not at hall
  have : (Pi.single 0 1 : Fin 4 → ZMod 5) = 0 := h.nondeg _ fun j => by
    have hj := hall 0 j
    rw [h.comm] at hj
    have h0 : ω 0 j = 0 := by
      rw [h.x_pow_eq_one_iff, ZMod.natCast_val, ZMod.cast_id', id] at hj
      exact hj
    rw [Fin.sum_univ_four]
    simp [h0]
  have := congrFun this 0
  simp only [Pi.single_eq_same, Pi.zero_apply] at this
  exact absurd this (by decide)

theorem commutator_eq_center : commutator (fiveQ x v) = center (fiveQ x v) := by
  have hle : commutator (fiveQ x v) ≤ center (fiveQ x v) := by
    rw [_root_.commutator_def, Subgroup.commutator_le]
    intro g _ k _
    rw [h.mem_center_iff]
    exact h.comm_mem g.2 k.2
  have : Fact (Nat.card (center (fiveQ x v))).Prime := ⟨by rw [h.card_center]; norm_num⟩
  rcases Subgroup.eq_bot_or_eq_top_of_prime_card
    ((commutator (fiveQ x v)).subgroupOf (center (fiveQ x v))) with hb | ht
  · exfalso
    obtain ⟨i, j, hij⟩ := h.exists_comm_ne_one
    have hmem : ⁅(⟨v i, v_mem i⟩ : fiveQ x v), ⟨v j, v_mem j⟩⁆ ∈ commutator (fiveQ x v) := by
      rw [_root_.commutator_def]
      exact Subgroup.commutator_mem_commutator (mem_top _) (mem_top _)
    have hc : ⁅(⟨v i, v_mem i⟩ : fiveQ x v), ⟨v j, v_mem j⟩⁆ ∈ center (fiveQ x v) := hle hmem
    have : (⟨_, hc⟩ : center (fiveQ x v)) ∈ (commutator (fiveQ x v)).subgroupOf
        (center (fiveQ x v)) := hmem
    rw [hb, mem_bot] at this
    apply hij
    have h2 := congrArg (fun z : center (fiveQ x v) => ((z : fiveQ x v) : G)) this
    simp only [Subgroup.coe_one, commutatorElement_def, Subgroup.coe_mul, Subgroup.coe_inv] at h2
    rw [commutatorElement_def]
    exact h2
  · apply le_antisymm hle
    intro g hg
    have : (⟨g, hg⟩ : center (fiveQ x v)) ∈ (commutator (fiveQ x v)).subgroupOf
        (center (fiveQ x v)) := by rw [ht]; trivial
    exact this

end FiveQRel

end CFSG.RankThree.Native

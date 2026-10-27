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
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.PiTensorProduct
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
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
public import Std.Tactic.BVDecide.Normalize.Prop

public section

namespace CFSG.RankThree.PartOne.AUTSL

open scoped _root_.Classical

section Count

variable {K : Type*} [Field K] [Fintype K]

@[expose] noncomputable def cntQ {X : Type*} [Fintype X] (q : X → K) (a : K) : ℕ :=
  (Finset.univ.filter fun x => q x = a).card

omit [Field K] in
theorem sum_cntQ {X : Type*} [Fintype X] (q : X → K) : ∑ a : K, cntQ q a = Fintype.card X := by
  rw [← Finset.card_univ, Finset.card_eq_sum_card_fiberwise (f := q) (t := Finset.univ)
    (fun x _ => Finset.mem_univ _)]
  rfl

omit [Fintype K] in
theorem cntQ_prod_add {X Y : Type*} [Fintype X] [Fintype Y] (q₁ : X → K) (q₂ : Y → K) (a : K) :
    cntQ (fun p : X × Y => q₁ p.1 + q₂ p.2) a = ∑ x : X, cntQ q₂ (a - q₁ x) := by
  simp only [cntQ]
  rw [Finset.card_filter, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Finset.card_filter]
  refine Finset.sum_congr rfl fun y _ => ?_
  have : (q₁ x + q₂ y = a) ↔ (q₂ y = a - q₁ x) := by
    constructor
    · intro h
      linear_combination h
    · intro h
      linear_combination h
  simp only [this]

theorem cntQ_hyp (t : K) :
    cntQ (fun p : K × K => p.1 * p.2) t =
      Fintype.card K - 1 + if t = 0 then Fintype.card K else 0 := by
  simp only [cntQ]
  rw [Finset.card_filter, Fintype.sum_prod_type]
  simp only []
  have h1 : ∀ x : K, x ≠ 0 → ∑ y : K, (if x * y = t then 1 else 0) = 1 := by
    intro x hx
    have : ∀ y : K, (x * y = t) ↔ (y = t / x) := fun y => by
      constructor
      · intro h
        field_simp
        linear_combination h
      · intro h
        rw [h]
        field_simp
    simp only [this, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  have h0 : ∑ y : K, (if (0 : K) * y = t then 1 else 0) =
      if t = 0 then Fintype.card K else 0 := by
    simp only [zero_mul]
    by_cases ht : t = 0
    · simp [ht]
    · simp [Ne.symm ht, ht]
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (0 : K)), h0]
  have : ∑ x ∈ Finset.univ.erase (0 : K), ∑ y : K, (if x * y = t then 1 else 0) =
      ∑ x ∈ Finset.univ.erase (0 : K), 1 := by
    refine Finset.sum_congr rfl fun x hx => ?_
    exact h1 x (Finset.ne_of_mem_erase hx)
  rw [this, Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
    smul_eq_mul, mul_one]
  ring

theorem cntQ_hyp_add {Y : Type*} [Fintype Y] (q₂ : Y → K) (a : K) :
    cntQ (fun r : (K × K) × Y => r.1.1 * r.1.2 + q₂ r.2) a =
      (Fintype.card K - 1) * Fintype.card Y + Fintype.card K * cntQ q₂ a := by
  rw [cntQ_prod_add (fun p : K × K => p.1 * p.2) q₂ a]
  set F : K → ℕ := fun t => cntQ q₂ (a - t) with hF
  have h1 : ∑ p : K × K, F (p.1 * p.2) =
      ∑ t : K, cntQ (fun p : K × K => p.1 * p.2) t * F t := by
    calc ∑ p : K × K, F (p.1 * p.2)
        = ∑ t : K, ∑ p ∈ Finset.univ.filter (fun p : K × K => p.1 * p.2 = t), F (p.1 * p.2) :=
          (Finset.sum_fiberwise _ _ _).symm
      _ = ∑ t : K, ∑ p ∈ Finset.univ.filter (fun p : K × K => p.1 * p.2 = t), F t := by
          refine Finset.sum_congr rfl fun t _ => Finset.sum_congr rfl fun p hp => ?_
          rw [(Finset.mem_filter.1 hp).2]
      _ = ∑ t : K, cntQ (fun p : K × K => p.1 * p.2) t * F t := by
          refine Finset.sum_congr rfl fun t _ => ?_
          rw [Finset.sum_const, smul_eq_mul]
          rfl
  rw [h1]
  simp only [cntQ_hyp]
  have h2 : ∑ t : K, F t = Fintype.card Y := by
    rw [← sum_cntQ q₂]
    exact Fintype.sum_equiv (Equiv.subLeft a) _ _ fun t => rfl
  calc ∑ t : K, (Fintype.card K - 1 + if t = 0 then Fintype.card K else 0) * F t
      = (Fintype.card K - 1) * ∑ t : K, F t + Fintype.card K * F 0 := by
        simp only [add_mul, Finset.sum_add_distrib, ← Finset.mul_sum]
        congr 1
        simp [ite_mul]
    _ = _ := by
        rw [h2]
        simp [hF]


omit [Field K] [Fintype K] in
theorem cntQ_comp_equiv {X X' : Type*} [Fintype X] [Fintype X'] (e : X ≃ X') (q : X' → K) (a : K) :
    cntQ (fun x => q (e x)) a = cntQ q a := by
  simp only [cntQ]
  refine Finset.card_bij (fun x _ => e x) ?_ ?_ ?_
  · intro x hx
    simpa using hx
  · intro x _ y _ h
    exact e.injective h
  · intro y hy
    refine ⟨e.symm y, ?_, by simp⟩
    simpa using hy


@[expose] def hypForm (m : ℕ) (v : Fin m → K × K) : K := ∑ i, (v i).1 * (v i).2

omit [Fintype K] in
theorem hypForm_zero (v : Fin 0 → K × K) : hypForm 0 v = 0 := by
  simp [hypForm]

omit [Fintype K] in
theorem hypForm_succ (m : ℕ) (v : Fin (m + 1) → K × K) :
    hypForm (m + 1) v = (v 0).1 * (v 0).2 + hypForm m (fun i => v i.succ) := by
  simp [hypForm, Fin.sum_univ_succ]

theorem cntQ_hypForm_succ {Y : Type*} [Fintype Y] (q₂ : Y → K) (m : ℕ) (a : K) :
    cntQ (fun r : (Fin (m + 1) → K × K) × Y => hypForm (m + 1) r.1 + q₂ r.2) a =
      (Fintype.card K - 1) * (Fintype.card K ^ (2 * m) * Fintype.card Y) +
        Fintype.card K * cntQ (fun r : (Fin m → K × K) × Y => hypForm m r.1 + q₂ r.2) a := by
  let e : (K × K) × ((Fin m → K × K) × Y) ≃ (Fin (m + 1) → K × K) × Y :=
    (Equiv.prodAssoc _ _ _).symm.trans
      (Equiv.prodCongr (Fin.consEquiv (fun _ => K × K)) (Equiv.refl Y))
  have h1 : cntQ (fun r : (K × K) × ((Fin m → K × K) × Y) =>
      r.1.1 * r.1.2 + (hypForm m r.2.1 + q₂ r.2.2)) a =
      cntQ (fun r : (Fin (m + 1) → K × K) × Y => hypForm (m + 1) r.1 + q₂ r.2) a := by
    rw [← cntQ_comp_equiv e]
    congr 1
    funext r
    simp [e, hypForm_succ, Fin.consEquiv, add_assoc]
  rw [← h1, cntQ_hyp_add (fun r : (Fin m → K × K) × Y => hypForm m r.1 + q₂ r.2) a]
  congr 2
  rw [Fintype.card_prod, Fintype.card_fun, Fintype.card_prod, Fintype.card_fin, pow_mul, sq]


theorem cntQ_hypForm_zero {Y : Type*} [Fintype Y] (q₂ : Y → K) (h0 : cntQ q₂ 0 = 1)
    (hY : Fintype.card Y = Fintype.card K ^ 2) (m : ℕ) :
    cntQ (fun r : (Fin m → K × K) × Y => hypForm m r.1 + q₂ r.2) 0 + Fintype.card K ^ (m + 1) =
      Fintype.card K ^ (2 * m + 1) + Fintype.card K ^ m := by
  obtain ⟨r, hr⟩ : ∃ r, Fintype.card K = r + 1 :=
    ⟨Fintype.card K - 1, by have := Fintype.card_pos (α := K); omega⟩
  induction m with
  | zero =>
    have h1 : cntQ (fun x : (Fin 0 → K × K) × Y => hypForm 0 x.1 + q₂ x.2) 0 = cntQ q₂ 0 := by
      rw [← cntQ_comp_equiv (Equiv.uniqueProd Y (Fin 0 → K × K)) q₂]
      congr 1
      funext x
      simp [hypForm_zero]
    rw [h1, h0]
    simp only [Nat.mul_zero, Nat.zero_add, pow_one, pow_zero]
    omega
  | succ m ih =>
    rw [cntQ_hypForm_succ, hY, hr]
    rw [hr] at ih
    set N := cntQ (fun x : (Fin m → K × K) × Y => hypForm m x.1 + q₂ x.2) 0
    calc (r + 1 - 1) * ((r + 1) ^ (2 * m) * (r + 1) ^ 2) + (r + 1) * N + (r + 1) ^ (m + 1 + 1)
        = r * ((r + 1) ^ (2 * m) * (r + 1) ^ 2) + (r + 1) * (N + (r + 1) ^ (m + 1)) := by
          simp only [Nat.add_sub_cancel]
          ring
      _ = r * ((r + 1) ^ (2 * m) * (r + 1) ^ 2) +
            (r + 1) * ((r + 1) ^ (2 * m + 1) + (r + 1) ^ m) := by
          rw [ih]
      _ = (r + 1) ^ (2 * (m + 1) + 1) + (r + 1) ^ (m + 1) := by ring

end Count

end CFSG.RankThree.PartOne.AUTSL

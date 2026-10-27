module

public import CFSG.LocalAnalysis.ComponentInitial.LinearUnitaryField
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
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.Tactic.Basify
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
public import Std.Tactic.BVDecide.Normalize.Prop

public section

namespace CFSG.RankThree.PartOne.KCUnitaryPlane

open CFSG.LocalAnalysis.ComponentInitial

variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]
variable {P : Type*} [Group P] (ρ : P →* LinearMap.GeneralLinearGroup K V)

@[expose] def act (x : P) : Module.End K V :=
  ((ρ x : LinearMap.GeneralLinearGroup K V) : Module.End K V)

theorem act_mul (x y : P) : act ρ (x * y) = act ρ x * act ρ y := by simp [act]

theorem act_one : act ρ 1 = 1 := by simp [act]

theorem act_pow (x : P) (k : ℕ) : act ρ (x ^ k) = act ρ x ^ k := by
  induction k with
  | zero => simp [act_one]
  | succ k ih => rw [pow_succ, act_mul, ih, pow_succ]

theorem act_inv_apply (x : P) (w : V) : act ρ x (act ρ x⁻¹ w) = w := by
  have h : act ρ x * act ρ x⁻¹ = 1 := by rw [← act_mul, mul_inv_cancel, act_one]
  simpa using congrArg (fun f : Module.End K V => f w) h

@[expose] def fixedSpace (L : Subgroup P) : Submodule K V where
  carrier := {v | ∀ y ∈ L, act ρ y v = v}
  zero_mem' := fun y _ => map_zero _
  add_mem' := fun {a b} ha hb y hy => by rw [map_add, ha y hy, hb y hy]
  smul_mem' := fun c a ha y hy => by rw [map_smul, ha y hy]

theorem mem_fixedSpace {L : Subgroup P} {v : V} :
    v ∈ fixedSpace ρ L ↔ ∀ y ∈ L, act ρ y v = v := Iff.rfl

variable [Fintype P]

open scoped _root_.Classical in
@[expose] noncomputable def sumOp (L : Subgroup P) : Module.End K V :=
  ∑ x ∈ Finset.univ.filter (fun x : P => x ∈ L), act ρ x

@[expose] noncomputable def avgOp (L : Subgroup P) : Module.End K V :=
  ((Nat.card L : ℕ) : K)⁻¹ • sumOp ρ L

open scoped _root_.Classical in
theorem card_filter_mem (L : Subgroup P) :
    (Finset.univ.filter fun x : P => x ∈ L).card = Nat.card L := by
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]

theorem mul_sumOp {L : Subgroup P} {y : P} (hy : y ∈ L) :
    act ρ y * sumOp ρ L = sumOp ρ L := by
  classical
  unfold sumOp
  rw [Finset.mul_sum]
  refine Finset.sum_equiv (Equiv.mulLeft y) ?_ ?_
  · intro x
    simp [Finset.mem_filter, L.mul_mem_cancel_left hy]
  · intro x _
    simp [act_mul]

theorem sumOp_mul {L : Subgroup P} {y : P} (hy : y ∈ L) :
    sumOp ρ L * act ρ y = sumOp ρ L := by
  classical
  unfold sumOp
  rw [Finset.sum_mul]
  refine Finset.sum_equiv (Equiv.mulRight y) ?_ ?_
  · intro x
    simp [Finset.mem_filter, L.mul_mem_cancel_right hy]
  · intro x _
    simp [act_mul]

theorem sumOp_mul_sumOp (L : Subgroup P) :
    sumOp ρ L * sumOp ρ L = (Nat.card L : K) • sumOp ρ L := by
  classical
  have h : ∀ x ∈ Finset.univ.filter (fun x : P => x ∈ L), act ρ x * sumOp ρ L = sumOp ρ L :=
    fun x hx => mul_sumOp ρ (Finset.mem_filter.mp hx).2
  conv_lhs => arg 1; rw [sumOp]
  rw [Finset.sum_mul, Finset.sum_congr rfl h, Finset.sum_const, card_filter_mem,
    Nat.cast_smul_eq_nsmul]

theorem avgOp_mul_avgOp {L : Subgroup P} (hL : ((Nat.card L : ℕ) : K) ≠ 0) :
    avgOp ρ L * avgOp ρ L = avgOp ρ L := by
  unfold avgOp
  rw [smul_mul_smul_comm, sumOp_mul_sumOp, smul_smul]
  congr 1
  field_simp

theorem avgOp_apply_of_mem_fixedSpace {L : Subgroup P} (hL : ((Nat.card L : ℕ) : K) ≠ 0) {v : V}
    (hv : v ∈ fixedSpace ρ L) : avgOp ρ L v = v := by
  classical
  have h1 : sumOp ρ L v = ((Nat.card L : ℕ) : K) • v := by
    unfold sumOp
    rw [LinearMap.sum_apply]
    rw [Finset.sum_congr rfl (fun x hx => hv x (Finset.mem_filter.mp hx).2)]
    rw [Finset.sum_const, card_filter_mem, Nat.cast_smul_eq_nsmul]
  unfold avgOp
  rw [LinearMap.smul_apply, h1, smul_smul, inv_mul_cancel₀ hL, one_smul]

theorem act_mul_avgOp {L : Subgroup P} {y : P} (hy : y ∈ L) :
    act ρ y * avgOp ρ L = avgOp ρ L := by
  unfold avgOp
  rw [mul_smul_comm, mul_sumOp ρ hy]

theorem avgOp_mul_act {L : Subgroup P} {y : P} (hy : y ∈ L) :
    avgOp ρ L * act ρ y = avgOp ρ L := by
  unfold avgOp
  rw [smul_mul_assoc, sumOp_mul ρ hy]

theorem avgOp_apply_mem_fixedSpace (L : Subgroup P) (v : V) : avgOp ρ L v ∈ fixedSpace ρ L := by
  intro y hy
  have := congrArg (fun f : Module.End K V => f v) (act_mul_avgOp ρ hy)
  simpa using this

theorem range_avgOp {L : Subgroup P} (hL : ((Nat.card L : ℕ) : K) ≠ 0) :
    LinearMap.range (avgOp ρ L) = fixedSpace ρ L := by
  ext v
  constructor
  · rintro ⟨w, rfl⟩
    exact avgOp_apply_mem_fixedSpace ρ L w
  · intro hv
    exact ⟨v, avgOp_apply_of_mem_fixedSpace ρ hL hv⟩

theorem avgOp_mul_avgOp_of_le {L M : Subgroup P} (hLM : L ≤ M)
    (hL : ((Nat.card L : ℕ) : K) ≠ 0) : avgOp ρ M * avgOp ρ L = avgOp ρ M := by
  classical
  have h : ∀ x ∈ Finset.univ.filter (fun x : P => x ∈ L), avgOp ρ M * act ρ x = avgOp ρ M :=
    fun x hx => avgOp_mul_act ρ (hLM (Finset.mem_filter.mp hx).2)
  have e : avgOp ρ M * sumOp ρ L = ((Nat.card L : ℕ) : K) • avgOp ρ M := by
    unfold sumOp
    rw [Finset.mul_sum, Finset.sum_congr rfl h, Finset.sum_const, card_filter_mem,
      Nat.cast_smul_eq_nsmul]
  have e2 : avgOp ρ M * avgOp ρ L = ((Nat.card L : ℕ) : K)⁻¹ • (avgOp ρ M * sumOp ρ L) := by
    conv_lhs => arg 2; rw [avgOp]
    rw [mul_smul_comm]
  rw [e2, e, smul_smul, inv_mul_cancel₀ hL, one_smul]

theorem avgOp_mul_avgOp_of_le' {L M : Subgroup P} (hLM : L ≤ M)
    (hL : ((Nat.card L : ℕ) : K) ≠ 0) : avgOp ρ L * avgOp ρ M = avgOp ρ M := by
  classical
  have h : ∀ x ∈ Finset.univ.filter (fun x : P => x ∈ L), act ρ x * avgOp ρ M = avgOp ρ M :=
    fun x hx => act_mul_avgOp ρ (hLM (Finset.mem_filter.mp hx).2)
  have e : sumOp ρ L * avgOp ρ M = ((Nat.card L : ℕ) : K) • avgOp ρ M := by
    unfold sumOp
    rw [Finset.sum_mul, Finset.sum_congr rfl h, Finset.sum_const, card_filter_mem,
      Nat.cast_smul_eq_nsmul]
  have e2 : avgOp ρ L * avgOp ρ M = ((Nat.card L : ℕ) : K)⁻¹ • (sumOp ρ L * avgOp ρ M) := by
    conv_lhs => arg 1; rw [avgOp]
    rw [smul_mul_assoc]
  rw [e2, e, smul_smul, inv_mul_cancel₀ hL, one_smul]

end CFSG.RankThree.PartOne.KCUnitaryPlane

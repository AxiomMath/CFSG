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
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.WittVector.IsPoly
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

public section

namespace CFSG.RankThree.PartOne.KFU

structure IsCentralPQuot {E P : Type*} [Group E] [Group P] (p : ℕ) (ε : E →* P) : Prop where
  surjective : Function.Surjective ε
  central : ε.ker ≤ Subgroup.center E
  coprime : Nat.Coprime p (Nat.card ε.ker)

namespace IsCentralPQuot

variable {E P : Type*} [Group E] [Group P] {p : ℕ} {ε : E →* P}
  (h : IsCentralPQuot p ε)

include h in
theorem eq_one_of_pow_eq_one {z : E} (hz : z ∈ ε.ker) (hzp : z ^ p = 1) : z = 1 := by
  have h1 : orderOf (⟨z, hz⟩ : ε.ker) ∣ Nat.card ε.ker := orderOf_dvd_natCard _
  have h2 : orderOf (⟨z, hz⟩ : ε.ker) ∣ p :=
    orderOf_dvd_of_pow_eq_one (Subtype.ext (by simpa using hzp))
  have h3 : orderOf (⟨z, hz⟩ : ε.ker) ∣ Nat.gcd p (Nat.card ε.ker) := Nat.dvd_gcd h2 h1
  rw [h.coprime] at h3
  have h4 := orderOf_eq_one_iff.mp (Nat.dvd_one.mp h3)
  exact congrArg Subtype.val h4

include h in
theorem eq_of_map_eq {a b : E} (ha : a ^ p = 1) (hb : b ^ p = 1) (hab : ε a = ε b) : a = b := by
  have hz : a⁻¹ * b ∈ ε.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hab, inv_mul_cancel]
  have hc : a⁻¹ * b ∈ Subgroup.center E := h.central hz
  have hcomm : Commute a (a⁻¹ * b) := (Subgroup.mem_center_iff.mp hc a)
  have hbz : b = a * (a⁻¹ * b) := by group
  have hpow : (a⁻¹ * b) ^ p = 1 := by
    have h1 : b ^ p = a ^ p * (a⁻¹ * b) ^ p := by
      conv_lhs => rw [hbz]
      exact hcomm.mul_pow p
    rw [hb, ha, one_mul] at h1
    exact h1.symm
  have := h.eq_one_of_pow_eq_one hz hpow
  calc a = a * (a⁻¹ * b) := by rw [this, mul_one]
    _ = b := by group

include h in
theorem commute_of_map_commute {a b : E} (ha : a ^ p = 1) (hab : Commute (ε a) (ε b)) :
    Commute a b := by
  set z := a * b * a⁻¹ * b⁻¹ with hzdef
  have hz : z ∈ ε.ker := by
    rw [MonoidHom.mem_ker, hzdef, map_mul, map_mul, map_mul, map_inv, map_inv]
    have := hab.eq
    calc ε a * ε b * (ε a)⁻¹ * (ε b)⁻¹ = ε b * ε a * (ε a)⁻¹ * (ε b)⁻¹ := by rw [this]
      _ = 1 := by group
  have hc : z ∈ Subgroup.center E := h.central hz
  have hzk : ∀ (k : ℕ) (g : E), g * z ^ k = z ^ k * g := fun k g =>
    Subgroup.mem_center_iff.mp (Subgroup.pow_mem _ hc k) g
  have hconj : ∀ k : ℕ, a ^ k * b * (a ^ k)⁻¹ = z ^ k * b := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      have h1 : a * b * a⁻¹ = z * b := by rw [hzdef]; group
      calc a ^ (k + 1) * b * (a ^ (k + 1))⁻¹ = a * (a ^ k * b * (a ^ k)⁻¹) * a⁻¹ := by group
        _ = a * (z ^ k * b) * a⁻¹ := by rw [ih]
        _ = z ^ k * (a * b * a⁻¹) := by rw [← mul_assoc, hzk k a]; group
        _ = z ^ (k + 1) * b := by rw [h1]; group
  have hzp : z ^ p = 1 := by
    calc z ^ p = z ^ p * b * b⁻¹ := by group
      _ = (a ^ p * b * (a ^ p)⁻¹) * b⁻¹ := by rw [hconj p]
      _ = 1 := by rw [ha]; group
  have hz1 := h.eq_one_of_pow_eq_one hz hzp
  exact commutatorElement_eq_one_iff_mul_comm.mp (by rw [commutatorElement_def]; exact hz1)

include h in
theorem exists_lift {x : P} (hx : x ^ p = 1) : ∃ y : E, ε y = x ∧ y ^ p = 1 := by
  obtain ⟨y₀, hy₀⟩ := h.surjective x
  obtain ⟨c, hc1, hc2⟩ := Nat.chineseRemainder h.coprime 1 0
  refine ⟨y₀ ^ c, ?_, ?_⟩
  · rw [map_pow, hy₀, pow_eq_pow_mod c hx, hc1]
    exact (pow_eq_pow_mod 1 hx).symm.trans (pow_one x)
  · have hmem : y₀ ^ p ∈ ε.ker := by
      rw [MonoidHom.mem_ker, map_pow, hy₀, hx]
    have hk : (y₀ ^ p) ^ Nat.card ε.ker = 1 := by
      have := pow_card_eq_one' (G := ε.ker) (x := ⟨y₀ ^ p, hmem⟩)
      simpa using congrArg Subtype.val this
    have hkc : Nat.card ε.ker ∣ c := (Nat.modEq_zero_iff_dvd).mp hc2
    obtain ⟨t, ht⟩ := hkc
    calc (y₀ ^ c) ^ p = (y₀ ^ p) ^ c := by rw [← pow_mul, ← pow_mul, mul_comm]
      _ = ((y₀ ^ p) ^ Nat.card ε.ker) ^ t := by rw [ht, pow_mul]
      _ = 1 := by rw [hk, one_pow]

end IsCentralPQuot

end CFSG.RankThree.PartOne.KFU

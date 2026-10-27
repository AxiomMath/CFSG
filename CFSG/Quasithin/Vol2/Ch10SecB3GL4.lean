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

namespace CFSG.Quasithin.Vol2.Ch10.SecB

theorem fixedPoints_trivial_of_orderOf_five {V : Type*} [Group V] [Finite V]
    (hV : Nat.card V = 16) {g : MulAut V} (hg : orderOf g = 5) {v : V} (hv : g v = v) :
    v = 1 := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  set P := Subgroup.zpowers g with hPdef
  have hP : IsPGroup 5 P := IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hg, pow_one])
  let F : Subgroup V :=
    { carrier := {w | g w = w}
      mul_mem' := fun {a b} ha hb => by
        show g (a * b) = a * b
        rw [map_mul, show g a = a from ha, show g b = b from hb]
      one_mem' := map_one g
      inv_mem' := fun {a} ha => by
        show g a⁻¹ = a⁻¹
        rw [map_inv, show g a = a from ha] }
  have hfix : MulAction.fixedPoints P V = (F : Set V) := by
    ext w
    constructor
    · intro hw
      exact hw ⟨g, Subgroup.mem_zpowers g⟩
    · intro hw
      rintro ⟨h, hh⟩
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hh
      have hw' : g w = w := hw
      show (g ^ k) w = w
      have key : ∀ n : ℕ, (g ^ n) w = w := by
        intro n
        induction n with
        | zero => simp
        | succ n ih => rw [pow_succ, MulAut.mul_apply, hw', ih]
      rcases Int.eq_nat_or_neg k with ⟨n, rfl | rfl⟩
      · rw [zpow_natCast]
        exact key n
      · rw [zpow_neg, zpow_natCast]
        calc (g ^ n)⁻¹ w = (g ^ n)⁻¹ ((g ^ n) w) := by rw [key n]
          _ = w := MulAut.inv_apply_self _ _ _
  have hmod := hP.card_modEq_card_fixedPoints V
  rw [hfix, hV] at hmod
  have hcF : Nat.card (F : Set V) = Nat.card F := rfl
  rw [hcF] at hmod
  have hdvd : Nat.card F ∣ 2 ^ 4 := by
    have := Subgroup.card_subgroup_dvd_card F
    rw [hV] at this
    simpa using this
  obtain ⟨k, hk, hkF⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
  interval_cases k
  ·
    have hF : F = ⊥ := Subgroup.eq_bot_of_card_eq F (by rw [hkF, pow_zero])
    have hvF : v ∈ F := hv
    rw [hF] at hvF
    exact hvF
  · rw [hkF] at hmod
    norm_num [Nat.ModEq] at hmod
  · rw [hkF] at hmod
    norm_num [Nat.ModEq] at hmod
  · rw [hkF] at hmod
    norm_num [Nat.ModEq] at hmod
  ·
    exfalso
    have hF : F = ⊤ := Subgroup.eq_top_of_card_eq F (by rw [hkF, hV]; norm_num)
    have hg1 : g = 1 := MulEquiv.ext fun w => by
      have hw : w ∈ F := by rw [hF]; trivial
      exact hw
    rw [hg1, orderOf_one] at hg
    norm_num at hg

end CFSG.Quasithin.Vol2.Ch10.SecB

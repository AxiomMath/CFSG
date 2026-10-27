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
public import Mathlib.Data.Nat.Prime.Factorial
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

namespace CFSG.RankThree.PartTwo.Sec21.Hering233i

@[expose] def invSet {G : Type*} [Group G] (Y : Subgroup G) (b : G) : Set G :=
  {y | y ∈ Y ∧ y * y = 1 ∧ y * b * y⁻¹ = b⁻¹}

variable {G : Type*} [Group G]

theorem invSet_mono {Y Y' : Subgroup G} (h : Y ≤ Y') (b : G) : invSet Y b ⊆ invSet Y' b :=
  fun _ ⟨hy, h2, hb⟩ => ⟨h hy, h2, hb⟩

theorem conj_mem_invSet {Y : Subgroup G} {b d : G} (hdY : d ∈ Subgroup.normalizer (Y : Set G))
    (hdb : d * b = b * d) {y : G} (hy : y ∈ invSet Y b) : d * y * d⁻¹ ∈ invSet Y b := by
  obtain ⟨hyY, hy2, hyb⟩ := hy
  refine ⟨(Subgroup.mem_normalizer_iff.mp hdY y).mp hyY, ?_, ?_⟩
  · calc d * y * d⁻¹ * (d * y * d⁻¹) = d * (y * y) * d⁻¹ := by group
      _ = 1 := by rw [hy2]; group
  · have hdb' : d⁻¹ * b * d = b := by
      calc d⁻¹ * b * d = d⁻¹ * (b * d) := by group
        _ = d⁻¹ * (d * b) := by rw [hdb]
        _ = b := by group
    calc d * y * d⁻¹ * b * (d * y * d⁻¹)⁻¹ = d * y * (d⁻¹ * b * d) * y⁻¹ * d⁻¹ := by group
      _ = d * (y * b * y⁻¹) * d⁻¹ := by rw [hdb']; group
      _ = b⁻¹ := by
        rw [hyb]
        calc d * b⁻¹ * d⁻¹ = (d * b * d⁻¹)⁻¹ := by group
          _ = b⁻¹ := by rw [show d * b * d⁻¹ = b by rw [hdb]; group]

theorem commute_of_invSet [Finite G] {Y : Subgroup G} {b d w : G}
    (hdY : d ∈ Subgroup.normalizer (Y : Set G)) (hdb : d * b = b * d) {q : ℕ} (hq : q.Prime)
    (hq4 : 4 < q) (hdq : ∃ k : ℕ, d ^ q ^ k = 1) (hcard : (invSet Y b).ncard ≤ 4)
    (hw : w ∈ invSet Y b) : d * w = w * d := by
  set S : Set G := invSet Y b with hS
  haveI : Finite S := Set.Finite.to_subtype (Set.toFinite S)
  let f : S → S := fun y => ⟨d * y * d⁻¹, conj_mem_invSet hdY hdb y.2⟩
  have hfinj : Function.Injective f := by
    intro y z h
    have h' : d * (y : G) * d⁻¹ = d * (z : G) * d⁻¹ := congrArg Subtype.val h
    exact Subtype.ext (by simpa using h')
  let σ : Equiv.Perm S := Equiv.ofBijective f (Finite.injective_iff_bijective.mp hfinj)
  have hσpow : ∀ n : ℕ, ∀ y : S, (((σ ^ n) y : S) : G) = d ^ n * (y : G) * (d ^ n)⁻¹ := by
    intro n
    induction n with
    | zero => intro y; simp
    | succ n ih =>
      intro y
      rw [pow_succ, Equiv.Perm.mul_apply]
      have h1 : ((σ y : S) : G) = d * (y : G) * d⁻¹ := rfl
      rw [ih (σ y), h1, pow_succ, mul_inv_rev]
      group
  obtain ⟨k, hk⟩ := hdq
  have hσ1 : σ ^ (q ^ k) = 1 := by
    ext y
    rw [hσpow, hk]
    simp
  have hord : orderOf σ ∣ q ^ k := orderOf_dvd_of_pow_eq_one hσ1
  classical
  haveI : Fintype S := Fintype.ofFinite S
  have hcardS : Fintype.card S ≤ 4 := by
    rw [← Nat.card_eq_fintype_card, Nat.card_coe_set_eq]
    exact hcard
  have hdvd : orderOf σ ∣ (Fintype.card S).factorial := by
    have := orderOf_dvd_natCard σ
    rwa [Nat.card_eq_fintype_card, Fintype.card_perm] at this
  have hcop : Nat.Coprime (q ^ k) (Fintype.card S).factorial := by
    refine Nat.Coprime.pow_left k ?_
    rw [Nat.Prime.coprime_iff_not_dvd hq, Nat.Prime.dvd_factorial hq]
    omega
  have hone : orderOf σ = 1 :=
    Nat.eq_one_of_dvd_one (hcop.gcd_eq_one ▸ Nat.dvd_gcd hord hdvd)
  have hσ : σ = 1 := orderOf_eq_one_iff.mp hone
  have hw' : d * w * d⁻¹ = w := by
    have h1 := congrArg (fun τ : Equiv.Perm S => ((τ ⟨w, hw⟩ : S) : G)) hσ
    have h2 : ((σ ⟨w, hw⟩ : S) : G) = d * w * d⁻¹ := rfl
    simp only [Equiv.Perm.coe_one, id_eq] at h1
    rw [h2] at h1
    exact h1
  exact mul_inv_eq_iff_eq_mul.mp hw'

end CFSG.RankThree.PartTwo.Sec21.Hering233i

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

namespace CFSG.RankThree.PartTwo.Sec19.NF5Pair
open MulAction

theorem isPGroup_zpowers_conjAct {M : Type*} [Group M] {v : M} (hv : v ^ 3 = 1) :
    IsPGroup 3 (Subgroup.zpowers (ConjAct.toConjAct v)) := by
  have hord : orderOf (ConjAct.toConjAct v) ∣ 3 := by
    apply orderOf_dvd_of_pow_eq_one
    rw [← map_pow, hv, map_one]
  rcases (Nat.dvd_prime Nat.prime_three).1 hord with h | h
  · exact IsPGroup.of_card (n := 0) (by rw [Nat.card_zpowers, h]; simp)
  · exact IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, h]; simp)

theorem exists_partner_of_free {M : Type*} [Group M] [Finite M] {z u : M}
    (hz3 : z ^ 3 = 1) (hz1 : z ≠ 1) (hu3 : u ^ 3 = 1)
    (hfree : ∀ m : M, (m * z * m⁻¹) * u ≠ u * (m * z * m⁻¹)) :
    ∃ m : M, (m * z * m⁻¹) * z = z * (m * z * m⁻¹) ∧ m * z * m⁻¹ ∉ Subgroup.zpowers z := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let Ω := orbit (ConjAct M) z
  haveI : Finite Ω := Set.toFinite _
  have hu_fix : Nat.card (fixedPoints (Subgroup.zpowers (ConjAct.toConjAct u)) Ω) = 0 := by
    rw [Nat.card_eq_zero]
    left
    constructor
    rintro ⟨⟨w, c, rfl⟩, hw⟩
    have h1 := mem_fixedPoints.1 hw ⟨ConjAct.toConjAct u, Subgroup.mem_zpowers _⟩
    have h2 : ConjAct.toConjAct u • (c • z) = c • z := congrArg Subtype.val h1
    apply hfree (ConjAct.ofConjAct c)
    rw [ConjAct.smul_def, ConjAct.smul_def] at h2
    simp only [ConjAct.ofConjAct_toConjAct] at h2
    exact (mul_inv_eq_iff_eq_mul.1 h2).symm
  have hu_mod := (isPGroup_zpowers_conjAct hu3).card_modEq_card_fixedPoints Ω
  rw [hu_fix] at hu_mod
  have hz_mod := (isPGroup_zpowers_conjAct hz3).card_modEq_card_fixedPoints Ω
  set Fz := fixedPoints (Subgroup.zpowers (ConjAct.toConjAct z)) Ω with hFz
  have hFz3 : Nat.card Fz ≡ 0 [MOD 3] := hz_mod.symm.trans hu_mod
  have hzmem : (⟨z, mem_orbit_self z⟩ : Ω) ∈ Fz := by
    rw [hFz, mem_fixedPoints]
    intro g
    have hle : Subgroup.zpowers (ConjAct.toConjAct z) ≤ stabilizer (ConjAct M) z := by
      rw [Subgroup.zpowers_le]
      rw [mem_stabilizer_iff, ConjAct.smul_def]
      simp
    exact Subtype.ext (mem_stabilizer_iff.1 (hle g.2))
  haveI : Finite Fz := Finite.of_injective (fun p : Fz => p.1) Subtype.val_injective
  have hpos : 0 < Nat.card Fz := Nat.card_pos_iff.2 ⟨⟨⟨_, hzmem⟩⟩, inferInstance⟩
  have h3 : 3 ≤ Nat.card Fz := by
    have := (Nat.modEq_zero_iff_dvd.1 hFz3)
    obtain ⟨k, hk⟩ := this
    omega
  by_contra hcon
  push Not at hcon
  have hord : orderOf z = 3 := orderOf_eq_prime hz3 hz1
  have hzi : z⁻¹ ≠ z := by
    intro h
    apply hz1
    have h2 : z ^ 2 = 1 := by rw [pow_two]; nth_rewrite 2 [← h]; exact mul_inv_cancel z
    calc z = z ^ 3 * (z ^ 2)⁻¹ := by group
      _ = 1 := by rw [hz3, h2]; simp
  have hfix : ∀ p : Fz, p.1.1 = z ∨ p.1.1 = z⁻¹ := by
    rintro ⟨⟨w, c, rfl⟩, hf⟩
    have h1 := mem_fixedPoints.1 hf ⟨ConjAct.toConjAct z, Subgroup.mem_zpowers _⟩
    have h2 : ConjAct.toConjAct z • (c • z) = c • z := congrArg Subtype.val h1
    rw [ConjAct.smul_def, ConjAct.smul_def] at h2
    simp only [ConjAct.ofConjAct_toConjAct] at h2
    have hcomm : (ConjAct.ofConjAct c * z * (ConjAct.ofConjAct c)⁻¹) * z =
        z * (ConjAct.ofConjAct c * z * (ConjAct.ofConjAct c)⁻¹) :=
      (mul_inv_eq_iff_eq_mul.1 h2).symm
    have hmem := hcon (ConjAct.ofConjAct c) hcomm
    have hne : ConjAct.ofConjAct c * z * (ConjAct.ofConjAct c)⁻¹ ≠ 1 := fun h => hz1 (by
      have : z = (ConjAct.ofConjAct c)⁻¹ * (ConjAct.ofConjAct c * z *
        (ConjAct.ofConjAct c)⁻¹) * ConjAct.ofConjAct c := by group
      rw [this, h]; group)
    rw [Subgroup.mem_zpowers_iff] at hmem
    obtain ⟨k, hk⟩ := hmem
    have hk3 := zpow_mod_orderOf z k
    rw [hord] at hk3
    show c • z = z ∨ c • z = z⁻¹
    rw [ConjAct.smul_def]
    rw [← hk, ← hk3]
    have hr : k % ((3 : ℕ) : ℤ) = 0 ∨ k % ((3 : ℕ) : ℤ) = 1 ∨ k % ((3 : ℕ) : ℤ) = 2 := by omega
    rcases hr with hr | hr | hr
    · exfalso
      apply hne
      rw [← hk, ← hk3, hr]; simp
    · left; rw [hr]; simp
    · right
      rw [hr]
      have : z ^ (2 : ℤ) = z⁻¹ := by
        rw [zpow_two, ← pow_two]
        exact eq_inv_of_mul_eq_one_left (by rw [← pow_succ]; exact hz3)
      exact this
  have hle : Nat.card Fz ≤ 2 := by
    have hinj : Function.Injective (fun p : Fz => decide (p.1.1 = z)) := by
      intro p q hpq
      simp only [decide_eq_decide] at hpq
      apply Subtype.ext
      apply Subtype.ext
      rcases hfix p with hp | hp <;> rcases hfix q with hq | hq
      · rw [hp, hq]
      · exfalso
        have h := hpq.1 hp
        rw [hq] at h
        exact hzi h
      · exfalso
        have h := hpq.2 hq
        rw [hp] at h
        exact hzi h
      · rw [hp, hq]
    have := Nat.card_le_card_of_injective _ hinj
    simpa using this
  omega

end CFSG.RankThree.PartTwo.Sec19.NF5Pair
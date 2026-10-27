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

namespace CFSG.Walter.J1Recog

variable {G : Type*} [Group G]

theorem mem_centralizer_zpowers_iff' (x u : G) :
    u ∈ Subgroup.centralizer ((Subgroup.zpowers x : Subgroup G) : Set G) ↔ u * x = x * u := by
  rw [Subgroup.mem_centralizer_iff]
  constructor
  · intro hz
    exact (hz x (Subgroup.mem_zpowers x)).symm
  · rintro hx _ ⟨k, rfl⟩
    exact (Commute.zpow_left (Commute.symm hx) k).eq

theorem mem_zpowers_of_comm [Finite G] {A : Subgroup G} (habel : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x)
    {p : ℕ} (hp : p.Prime) (hpA : ¬ p ^ 2 ∣ Nat.card A) {x y : G} (hx : x ∈ A) (hy : y ∈ A)
    (hxp : x ^ p = 1) (hyp : y ^ p = 1) (hy1 : y ≠ 1) : x ∈ Subgroup.zpowers y := by
  have := Fact.mk hp
  let K : Subgroup G :=
    { carrier := {z | z ∈ A ∧ z ^ p = 1}
      mul_mem' := by
        rintro a b ⟨ha, hap⟩ ⟨hb, hbp⟩
        refine ⟨A.mul_mem ha hb, ?_⟩
        rw [(Commute.mul_pow (habel a ha b hb) p), hap, hbp, one_mul]
      one_mem' := ⟨A.one_mem, one_pow p⟩
      inv_mem' := by
        rintro a ⟨ha, hap⟩
        exact ⟨A.inv_mem ha, by rw [inv_pow, hap, inv_one]⟩ }
  have hKA : K ≤ A := fun z hz => hz.1
  have hKp : IsPGroup p K := fun z => ⟨1, by
    apply Subtype.ext
    simpa using z.2.2⟩
  obtain ⟨k, hk⟩ := hKp.exists_card_eq
  have hdvd : p ^ k ∣ Nat.card A := hk ▸ Subgroup.card_dvd_of_le hKA
  have hk1 : k ≤ 1 := by
    by_contra hlt
    exact hpA (dvd_trans (pow_dvd_pow p (by omega)) hdvd)
  have hyK : Subgroup.zpowers y ≤ K := Subgroup.zpowers_le.mpr ⟨hy, hyp⟩
  have hyo : orderOf y = p := orderOf_eq_prime hyp hy1
  have hle : Nat.card K ≤ Nat.card (Subgroup.zpowers y) := by
    rw [hk, Nat.card_zpowers, hyo]
    calc p ^ k ≤ p ^ 1 := Nat.pow_le_pow_right hp.pos hk1
      _ = p := pow_one p
  have heq := Subgroup.eq_of_le_of_card_ge hyK hle
  rw [heq]
  exact ⟨hx, hxp⟩

theorem conj_eq_pow_of_seven_three {x y : G} (hy : orderOf y = 7) (hx : x ^ 3 = 1)
    (hxy : x * y * x⁻¹ ∈ Subgroup.zpowers y) :
    x * y * x⁻¹ = y ∨ x * y * x⁻¹ = y ^ 2 ∨ x * y * x⁻¹ = y ^ 4 := by
  have hy7 : y ^ 7 = 1 := by rw [← hy]; exact pow_orderOf_eq_one y
  obtain ⟨k, hk⟩ : ∃ k : ℕ, k < 7 ∧ x * y * x⁻¹ = y ^ k := by
    obtain ⟨j, hj⟩ := hxy
    refine ⟨(j % 7).toNat, by omega, ?_⟩
    rw [← hj]
    change y ^ j = y ^ (j % 7).toNat
    have hy7' : y ^ (7 : ℤ) = 1 := by exact_mod_cast hy7
    rw [← zpow_natCast, Int.toNat_of_nonneg (Int.emod_nonneg j (by norm_num)),
      ← zpow_eq_zpow_emod j hy7']
  obtain ⟨hk7, hk⟩ := hk
  have hconj : ∀ i : ℕ, ∀ a : ℕ, x ^ i * y ^ a * (x ^ i)⁻¹ = y ^ (a * k ^ i) := by
    intro i
    induction i with
    | zero => intro a; simp
    | succ i ih =>
      intro a
      rw [pow_succ', mul_inv_rev, show x * x ^ i * y ^ a * ((x ^ i)⁻¹ * x⁻¹) =
        x * (x ^ i * y ^ a * (x ^ i)⁻¹) * x⁻¹ by group, ih, ← conj_pow, hk, ← pow_mul,
        pow_succ]
      ring_nf
  have h3 := hconj 3 1
  rw [hx, one_mul, inv_one, mul_one, pow_one, one_mul] at h3
  have hmod : k ^ 3 % 7 = 1 := by
    have := (pow_eq_pow_iff_modEq.mp (h3.symm.trans (pow_one y).symm))
    rw [hy] at this
    exact this
  interval_cases k
  · norm_num at hmod
  · left; rw [hk, pow_one]
  · right; left; exact hk
  · norm_num at hmod
  · right; right; exact hk
  · norm_num at hmod
  · norm_num at hmod

theorem exists_pow_of_mem_zpowers {x y : G} {n : ℕ} (hn : 0 < n) (hy : y ^ n = 1)
    (hx : x ∈ Subgroup.zpowers y) : ∃ k < n, x = y ^ k := by
  obtain ⟨j, hj⟩ := hx
  have hn' : (0 : ℤ) < n := by exact_mod_cast hn
  have hlt : j % n < n := Int.emod_lt_of_pos j hn'
  refine ⟨(j % n).toNat, by omega, ?_⟩
  rw [← hj]
  change y ^ j = y ^ (j % n).toNat
  have hy' : y ^ (n : ℤ) = 1 := by exact_mod_cast hy
  rw [← zpow_natCast, Int.toNat_of_nonneg (Int.emod_nonneg j hn'.ne'),
    ← zpow_eq_zpow_emod j hy']

theorem conj_commute {g x z : G} (h : z * x = x * z) :
    (g * z * g⁻¹) * (g * x * g⁻¹) = (g * x * g⁻¹) * (g * z * g⁻¹) := by
  simp only [mul_assoc, inv_mul_cancel_left]
  rw [← mul_assoc z, h, mul_assoc]

end CFSG.Walter.J1Recog

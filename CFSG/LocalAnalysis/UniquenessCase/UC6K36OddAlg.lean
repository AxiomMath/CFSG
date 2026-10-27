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
public import Mathlib.Data.Int.Star
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
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UCK.Odd

variable {A : Type*} [CommGroup A]

def nrm (σ : A →* A) (u : A) : ℕ → A
  | 0 => 1
  | n + 1 => u * σ (nrm σ u n)

@[simp] theorem nrm_zero (σ : A →* A) (u : A) : nrm σ u 0 = 1 := by simp [nrm]

theorem nrm_succ (σ : A →* A) (u : A) (n : ℕ) : nrm σ u (n + 1) = u * σ (nrm σ u n) := by
  simp [nrm]

theorem nrm_zpow (σ : A →* A) (u : A) (k : ℤ) (n : ℕ) : nrm σ (u ^ k) n = nrm σ u n ^ k := by
  induction n with
  | zero => simp [nrm]
  | succ n ih => simp [nrm, ih, mul_zpow, map_zpow]

theorem iterate_aff (σ : A →* A) (u : A) (n : ℕ) (w : A) :
    (fun v => u⁻¹ * σ v)^[n] w = (nrm σ u n)⁻¹ * (⇑σ)^[n] w := by
  induction n with
  | zero => simp [nrm]
  | succ n ih =>
    rw [Function.iterate_succ_apply', ih, Function.iterate_succ_apply', nrm]
    simp only [map_mul, map_inv, mul_inv_rev]
    rw [← mul_assoc, mul_comm u⁻¹]

theorem exists_fixed_of_norm [Finite A] {p m : ℕ} [hp : Fact p.Prime] (hpm : Nat.Coprime p m)
    (σ : A →* A) (hσ : ∀ a, (⇑σ)^[p] a = a) {u : A} (hu : u ^ m = 1) (hN : nrm σ u p = 1) :
    ∃ w : A, w ^ m = 1 ∧ σ w * w⁻¹ = u := by
  classical
  haveI : Fintype A := Fintype.ofFinite A
  have hp0 : 0 < p := hp.out.pos
  have hinj : Function.Injective σ := by
    intro a b hab
    have hp1 : p - 1 + 1 = p := Nat.sub_add_cancel hp0
    have h1 : (⇑σ)^[p - 1] (σ a) = a := by
      have := hσ a
      rw [← hp1, Function.iterate_succ_apply] at this
      exact this
    have h2 : (⇑σ)^[p - 1] (σ b) = b := by
      have := hσ b
      rw [← hp1, Function.iterate_succ_apply] at this
      exact this
    rw [← h1, ← h2, hab]
  have hTinj : Function.Injective (fun v : A => u⁻¹ * σ v) := fun a b hab =>
    hinj (mul_left_cancel hab)
  let f : Equiv.Perm A := Equiv.ofBijective _ (Finite.injective_iff_bijective.1 hTinj)
  have hf : ∀ v, f v = u⁻¹ * σ v := fun v => rfl
  have hfn : ∀ (n : ℕ) (v : A), (f ^ n) v = (nrm σ u n)⁻¹ * (⇑σ)^[n] v := by
    intro n v
    have h1 : ⇑(f ^ n) = (fun v : A => u⁻¹ * σ v)^[n] := by
      rw [Equiv.Perm.coe_pow]
      rfl
    rw [h1, iterate_aff]
  have hfp : f ^ p = 1 := by
    ext v
    rw [hfn, hN, hσ]
    simp
  have hP : ∀ w : A, (f w) ^ m = 1 ↔ w ^ m = 1 := by
    intro w
    have h1 : (f w) ^ m = σ (w ^ m) := by
      rw [hf, mul_pow, inv_pow, hu, inv_one, one_mul, map_pow]
    rw [h1, map_eq_one_iff σ hinj]
  let fS : Equiv.Perm {w : A // w ^ m = 1} := f.subtypePerm hP
  have hfS : fS ^ p ^ 1 = 1 := by
    rw [pow_one]
    refine Equiv.ext fun x => Subtype.ext ?_
    change (((f.subtypePerm hP) ^ p) x : A) = x
    rw [Equiv.Perm.subtypePerm_pow, Equiv.Perm.subtypePerm_apply]
    show (f ^ p) x = x
    rw [hfp]
    rfl
  have hcard : ¬ p ∣ Fintype.card {w : A // w ^ m = 1} := by
    intro hd
    let S : Subgroup A := (powMonoidHom m : A →* A).ker
    have hS : ∀ w : A, w ∈ S ↔ w ^ m = 1 := fun w => by simp [S]
    have hc : Nat.card S = Fintype.card {w : A // w ^ m = 1} := by
      rw [← Nat.card_eq_fintype_card]
      exact Nat.card_congr (Equiv.subtypeEquivRight hS)
    rw [← hc] at hd
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := S) p hd
    have hxm : (x : A) ^ m = 1 := (hS x).1 x.2
    have : p ∣ m := by
      rw [← hx]
      exact orderOf_dvd_of_pow_eq_one (Subtype.ext (by simpa using hxm))
    exact hp.out.one_lt.ne' (Nat.Coprime.eq_one_of_dvd hpm this)
  obtain ⟨⟨w, hw⟩, hfw⟩ := Equiv.Perm.exists_fixed_point_of_prime hcard hfS
  have hfw' : f w = w := congrArg Subtype.val hfw
  refine ⟨w, hw, ?_⟩
  rw [hf] at hfw'
  have h3 : σ w = u * w := by
    calc σ w = u * (u⁻¹ * σ w) := by rw [mul_inv_cancel_left]
      _ = u * w := by rw [hfw']
  rw [h3, mul_inv_cancel_right]

theorem exists_mul_pPower [Finite A] {p : ℕ} [hp : Fact p.Prime] (σ : A →* A)
    (hσ : ∀ a, (⇑σ)^[p] a = a) {z : A} (hz : nrm σ z p = 1) :
    ∃ w : A, ∃ n : ℕ, (z * (σ w * w⁻¹)) ^ (p ^ n) = 1 := by
  classical
  have hN0 : Nat.card A ≠ 0 := Nat.card_pos.ne'
  obtain ⟨a, m, hpm, hN⟩ := Nat.exists_eq_pow_mul_and_not_dvd hN0 p hp.out.ne_one
  have hcop : Nat.Coprime p m := (Nat.Prime.coprime_iff_not_dvd hp.out).2 hpm
  have hcop' : IsCoprime ((p ^ a : ℕ) : ℤ) (m : ℤ) := by
    rw [Nat.isCoprime_iff_coprime]
    exact hcop.pow_left a
  obtain ⟨t, s, hts⟩ := hcop'
  have hzN : z ^ (p ^ a * m) = 1 := by
    rw [← hN]
    exact pow_card_eq_one'
  set u : A := z ^ (t * ((p ^ a : ℕ) : ℤ)) with hu
  have hum : u ^ m = 1 := by
    calc u ^ m = z ^ (((p ^ a * m : ℕ) : ℤ) * t) := by
          rw [hu, ← zpow_natCast, ← zpow_mul]
          congr 1
          push_cast
          ring
      _ = (z ^ (p ^ a * m)) ^ t := by rw [zpow_mul, zpow_natCast]
      _ = 1 := by rw [hzN, one_zpow]
  have hNu : nrm σ u p = 1 := by rw [hu, nrm_zpow, hz, one_zpow]
  obtain ⟨w, -, hw⟩ := exists_fixed_of_norm hcop σ hσ hum hNu
  refine ⟨w⁻¹, a, ?_⟩
  have h1 : σ w⁻¹ * (w⁻¹)⁻¹ = u⁻¹ := by
    rw [map_inv, inv_inv, ← hw, mul_inv_rev, inv_inv, mul_comm]
  have h2 : z * u⁻¹ = z ^ (s * (m : ℤ)) := by
    rw [hu, ← zpow_neg, show s * (m : ℤ) = 1 + -(t * ((p ^ a : ℕ) : ℤ)) by linarith, zpow_add,
      zpow_one]
  rw [h1, h2, ← zpow_natCast, ← zpow_mul]
  calc z ^ (s * (m : ℤ) * ((p ^ a : ℕ) : ℤ)) = (z ^ (p ^ a * m)) ^ s := by
        rw [← zpow_natCast, ← zpow_mul]
        congr 1
        push_cast
        ring
    _ = 1 := by rw [hzN, one_zpow]

end CFSG.LocalAnalysis.UniquenessCase.UCK.Odd

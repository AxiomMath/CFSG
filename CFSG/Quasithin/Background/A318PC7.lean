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
public import Mathlib.GroupTheory.Nilpotent
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

namespace CFSG.Quasithin

namespace A318P

section Arith

variable {G : Type*} [Group G]

theorem conj_pow_eq_zpow {r y : G} {t : ℤ} (hyr : y * r * y⁻¹ = r ^ t) (k : ℕ) :
    y ^ k * r * (y ^ k)⁻¹ = r ^ (t ^ k) := by
  induction k with
  | zero => simp
  | succ k ih =>
    have h1 : y ^ (k + 1) * r * (y ^ (k + 1))⁻¹ = y * (y ^ k * r * (y ^ k)⁻¹) * y⁻¹ := by group
    rw [h1, ih, ← conj_zpow, hyr, ← zpow_mul, pow_succ']

theorem conj_pow_zpow_eq {r y : G} {t : ℤ} (hyr : y * r * y⁻¹ = r ^ t) (k : ℕ) (j : ℤ) :
    y ^ k * r ^ j * (y ^ k)⁻¹ = r ^ (t ^ k * j) := by
  rw [← conj_zpow, conj_pow_eq_zpow hyr k, ← zpow_mul]

theorem three_dvd_of_cube_eq_zpow {r y : G} {m : ℕ} (hm : 1 ≤ m) (hr : orderOf r = 3 ^ m)
    {s : ℤ} (hys : y ^ 3 = r ^ s) (hmax : orderOf y ≤ 3 ^ m) : (3 : ℤ) ∣ s := by
  by_contra hns
  have hs0 : s ≠ 0 := fun h => hns (h ▸ dvd_zero 3)
  have hcop : Nat.Coprime (3 ^ m) s.natAbs := by
    apply Nat.Coprime.pow_left
    rw [Nat.Prime.coprime_iff_not_dvd Nat.prime_three]
    intro h
    apply hns
    omega
  have h1 : orderOf (y ^ 3) = 3 ^ m := by
    rw [hys, orderOf_zpow' r hs0, hr, hcop.gcd_eq_one, Nat.div_one]
  have h2 : orderOf (y ^ 3) = orderOf y / Nat.gcd (orderOf y) 3 := orderOf_pow' _ (by norm_num)
  rw [h2] at h1
  set o := orderOf y with ho
  have hdvd : Nat.gcd o 3 ∣ 3 := Nat.gcd_dvd_right o 3
  have hg : Nat.gcd o 3 = 1 ∨ Nat.gcd o 3 = 3 := (Nat.dvd_prime Nat.prime_three).1 hdvd
  have h3m : 3 ∣ 3 ^ m := dvd_pow_self 3 (by omega)
  rcases hg with hg | hg
  · rw [hg, Nat.div_one] at h1
    have h3o : 3 ∣ o := h1 ▸ h3m
    rw [Nat.gcd_eq_right h3o] at hg
    omega
  · rw [hg] at h1
    have h3o : 3 ∣ o := hg ▸ Nat.gcd_dvd_left o 3
    obtain ⟨c, hc⟩ := h3o
    have hpos : 0 < 3 ^ m := by positivity
    rw [hc, Nat.mul_div_cancel_left _ (by norm_num)] at h1
    rw [hc, h1] at hmax
    omega

theorem exists_cube_eq_one {r y : G} {m : ℕ} (hm : 1 ≤ m) (hr : orderOf r = 3 ^ m) {t s : ℤ}
    (hyr : y * r * y⁻¹ = r ^ t) (hys : y ^ 3 = r ^ s) (hmax : orderOf y ≤ 3 ^ m) :
    ∃ j : ℤ, (r ^ j * y) ^ 3 = 1 := by
  have h3s : (3 : ℤ) ∣ s := three_dvd_of_cube_eq_zpow hm hr hys hmax
  obtain ⟨s', rfl⟩ := h3s
  have hrN : r ^ (3 ^ m : ℤ) = 1 := by
    have : r ^ (3 ^ m : ℕ) = 1 := hr ▸ pow_orderOf_eq_one r
    exact_mod_cast this
  have ht3 : (3 : ℤ) ∣ t ^ 3 - 1 := by
    have h1 : y ^ 3 * r * (y ^ 3)⁻¹ = r ^ (t ^ 3) := conj_pow_eq_zpow hyr 3
    have h2 : y ^ 3 * r * (y ^ 3)⁻¹ = r := by
      rw [hys]
      group
    have h3 : r ^ (t ^ 3 - 1) = 1 := by
      rw [zpow_sub, zpow_one, ← h1, h2, mul_inv_cancel]
    have h4 : ((orderOf r : ℕ) : ℤ) ∣ t ^ 3 - 1 := orderOf_dvd_iff_zpow_eq_one.2 h3
    rw [hr] at h4
    refine dvd_trans ?_ h4
    exact_mod_cast dvd_pow_self 3 (show m ≠ 0 by omega)
  have ht1 : (3 : ℤ) ∣ t - 1 := by
    have h := (ZMod.intCast_zmod_eq_zero_iff_dvd (t ^ 3 - 1) 3).2 ht3
    push_cast at h
    have hz : (t : ZMod 3) ^ 3 = 1 := sub_eq_zero.1 h
    have hz1 : (t : ZMod 3) = 1 := by
      revert hz
      generalize (t : ZMod 3) = u
      revert u
      decide
    have h0 : ((t - 1 : ℤ) : ZMod 3) = 0 := by
      push_cast
      rw [hz1, sub_self]
    exact_mod_cast (ZMod.intCast_zmod_eq_zero_iff_dvd (t - 1) 3).1 h0
  obtain ⟨a, ha⟩ := ht1
  have hta : t = 1 + 3 * a := by linarith
  set u : ℤ := 1 + 3 * a + 3 * a ^ 2 with hu
  have htu : 1 + t + t ^ 2 = 3 * u := by rw [hta, hu]; ring
  have hcop : IsCoprime u ((3 : ℤ) ^ (m - 1)) := by
    apply IsCoprime.pow_right
    exact ⟨1, -(a + a ^ 2), by rw [hu]; ring⟩
  obtain ⟨a₁, b₁, hab⟩ := hcop
  refine ⟨-(s' * a₁), ?_⟩
  set j : ℤ := -(s' * a₁) with hj
  have h1 : y * r ^ j * y⁻¹ = r ^ (t * j) := by
    have := conj_pow_zpow_eq hyr 1 j
    simpa using this
  have h2 : y ^ 2 * r ^ j * (y ^ 2)⁻¹ = r ^ (t ^ 2 * j) := conj_pow_zpow_eq hyr 2 j
  have hcube : (r ^ j * y) ^ 3 = r ^ j * (y * r ^ j * y⁻¹) * (y ^ 2 * r ^ j * (y ^ 2)⁻¹) * y ^ 3 := by
    simp only [pow_succ, pow_zero, one_mul]
    group
  rw [hcube, h1, h2, hys, ← zpow_add, ← zpow_add, ← zpow_add]
  have hexp : j + t * j + t ^ 2 * j + 3 * s' = (3 ^ m : ℤ) * (s' * b₁) := by
    have e1 : j + t * j + t ^ 2 * j + 3 * s' = 3 * (j * u + s') := by
      have : j + t * j + t ^ 2 * j = j * (1 + t + t ^ 2) := by ring
      rw [this, htu]
      ring
    have e2 : j * u + s' = s' * b₁ * 3 ^ (m - 1) := by
      rw [hj]
      linear_combination (-s') * hab
    have e3 : (3 : ℤ) ^ m = 3 * 3 ^ (m - 1) := by
      rw [← pow_succ']
      congr 1
      omega
    rw [e1, e2, e3]
    ring
  rw [hexp, zpow_mul, hrN, one_zpow]

end Arith

section Cyclic

variable {G : Type*} [Group G]

theorem isCyclic_of_unique_three [Finite G] {R Z : Subgroup G} (hR : IsPGroup 3 R)
    (hZ : Nat.card Z = 3) (h3 : ∀ r ∈ R, orderOf r = 3 → r ∈ Z) : IsCyclic R := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Group.IsNilpotent ↥R := hR.isNilpotent
  obtain ⟨r, hrmax⟩ := Finite.exists_max (fun g : ↥R => orderOf g)
  obtain ⟨m, hm⟩ := (IsPGroup.iff_orderOf.1 hR) r
  by_contra hcyc
  set H : Subgroup ↥R := Subgroup.zpowers r with hH
  have hlt : H < ⊤ := by
    refine lt_top_iff_ne_top.2 fun h => hcyc ?_
    exact isCyclic_iff_exists_zpowers_eq_top.2 ⟨r, h⟩
  have hnc := Group.normalizerCondition_of_isNilpotent (G := ↥R) H hlt
  obtain ⟨y₀, hy₀N, hy₀H⟩ := IsConcreteLE.exists_of_lt hnc
  obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.1 hR) y₀
  have hex : ∃ i : ℕ, y₀ ^ (3 ^ i) ∈ H := ⟨k, by rw [← hk, pow_orderOf_eq_one]; exact H.one_mem⟩
  set i := Nat.find hex with hi
  have hi0 : i ≠ 0 := by
    intro h0
    have := Nat.find_spec hex
    rw [← hi, h0] at this
    exact hy₀H (by simpa using this)
  obtain ⟨i', hi'⟩ : ∃ i', i = i' + 1 := ⟨i - 1, by omega⟩
  set y : ↥R := y₀ ^ (3 ^ i') with hy
  have hyH : y ∉ H := by
    have := Nat.find_min hex (show i' < i by omega)
    exact this
  have hy3 : y ^ 3 ∈ H := by
    have := Nat.find_spec hex
    rw [← hi, hi', pow_succ, pow_mul] at this
    exact this
  have hyN : y ∈ Subgroup.normalizer (H : Set ↥R) := pow_mem hy₀N _
  have hyr : y * r * y⁻¹ ∈ H := ((Subgroup.mem_normalizer_iff.1 hyN) r).1 (Subgroup.mem_zpowers r)
  obtain ⟨t, ht⟩ := Subgroup.mem_zpowers_iff.1 hyr
  obtain ⟨s, hs⟩ := Subgroup.mem_zpowers_iff.1 hy3
  have hmax : orderOf y ≤ 3 ^ m := hm ▸ hrmax y
  have hm1 : 1 ≤ m := by
    by_contra hm0
    have hm0' : m = 0 := by omega
    rw [hm0', pow_zero] at hmax
    have : orderOf y = 1 := le_antisymm hmax (orderOf_pos y)
    exact hyH (by rw [orderOf_eq_one_iff.1 this]; exact H.one_mem)
  obtain ⟨j, hj⟩ := exists_cube_eq_one hm1 hm (t := t) (s := s) ht.symm hs.symm hmax
  set w : ↥R := r ^ j * y with hw
  have hwH : w ∉ H := by
    intro hwH
    apply hyH
    have : y = (r ^ j)⁻¹ * w := by rw [hw]; group
    rw [this]
    exact mul_mem (inv_mem (zpow_mem (Subgroup.mem_zpowers r) j)) hwH
  have hw1 : w ≠ 1 := fun h => hwH (h ▸ H.one_mem)
  have hword : orderOf w = 3 := orderOf_eq_prime hj hw1
  have hwZ : (w : G) ∈ Z := h3 w w.2 (by rw [Subgroup.orderOf_coe]; exact hword)
  set z₁ : ↥R := r ^ (3 ^ (m - 1)) with hz₁
  have hz₁ord : orderOf z₁ = 3 := by
    have hpos : 3 ^ (m - 1) ≠ 0 := by positivity
    rw [hz₁, orderOf_pow' _ hpos, hm]
    have h1 : Nat.gcd (3 ^ m) (3 ^ (m - 1)) = 3 ^ (m - 1) := by
      apply Nat.gcd_eq_right
      exact pow_dvd_pow 3 (by omega)
    rw [h1]
    have : (3 : ℕ) ^ m = 3 * 3 ^ (m - 1) := by
      rw [← pow_succ']
      congr 1
      omega
    rw [this, Nat.mul_div_cancel _ (by positivity)]
  have hz₁Z : (z₁ : G) ∈ Z := h3 z₁ z₁.2 (by rw [Subgroup.orderOf_coe]; exact hz₁ord)
  have hz₁1 : (z₁ : G) ≠ 1 := by
    intro h
    have : z₁ = 1 := Subtype.ext h
    rw [this, orderOf_one] at hz₁ord
    omega
  have hZeq : Z = Subgroup.zpowers (z₁ : G) := by
    refine (Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.2 hz₁Z) ?_).symm
    rw [Nat.card_zpowers, Subgroup.orderOf_coe, hz₁ord, hZ]
  rw [hZeq] at hwZ
  obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.1 hwZ
  have hwz : w = z₁ ^ n := Subtype.ext (by rw [← hn]; rfl)
  apply hwH
  rw [hwz, hz₁]
  exact zpow_mem (pow_mem (Subgroup.mem_zpowers r) _) n

end Cyclic

end A318P

end CFSG.Quasithin

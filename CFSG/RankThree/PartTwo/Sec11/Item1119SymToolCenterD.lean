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

namespace CFSG.RankThree.PartTwo.Sec11.Item1119Sym

theorem aux_CenterD_comm_pow {G : Type*} [Group G] (a c d : G)
    (hac : a * c = c * a) (had : a * d = d * a) (hcd : c * d = d * c)
    (i j k i' j' k' : ℤ) :
    (a ^ i * c ^ j * d ^ k) * (a ^ i' * c ^ j' * d ^ k') =
      a ^ (i + i') * c ^ (j + j') * d ^ (k + k') := by
  have hac' : Commute a c := hac
  have had' : Commute a d := had
  have hcd' : Commute c d := hcd
  have hAC : Commute (a ^ i') (c ^ j) := hac'.zpow_zpow i' j
  have hAD : Commute (a ^ i') (d ^ k) := had'.zpow_zpow i' k
  have hCD : Commute (c ^ j') (d ^ k) := hcd'.zpow_zpow j' k
  have e1 : d ^ k * a ^ i' = a ^ i' * d ^ k := hAD.eq.symm
  have e2 : c ^ j * a ^ i' = a ^ i' * c ^ j := hAC.eq.symm
  have e3 : d ^ k * c ^ j' = c ^ j' * d ^ k := hCD.eq.symm
  rw [zpow_add, zpow_add, zpow_add]
  calc a ^ i * c ^ j * d ^ k * (a ^ i' * c ^ j' * d ^ k')
      = a ^ i * c ^ j * (d ^ k * a ^ i') * c ^ j' * d ^ k' := by simp only [mul_assoc]
    _ = a ^ i * c ^ j * (a ^ i' * d ^ k) * c ^ j' * d ^ k' := by rw [e1]
    _ = a ^ i * (c ^ j * a ^ i') * d ^ k * c ^ j' * d ^ k' := by simp only [mul_assoc]
    _ = a ^ i * (a ^ i' * c ^ j) * d ^ k * c ^ j' * d ^ k' := by rw [e2]
    _ = a ^ i * a ^ i' * c ^ j * d ^ k * c ^ j' * d ^ k' := by simp only [mul_assoc]
    _ = a ^ i * a ^ i' * c ^ j * (d ^ k * c ^ j') * d ^ k' := by simp only [mul_assoc]
    _ = a ^ i * a ^ i' * c ^ j * (c ^ j' * d ^ k) * d ^ k' := by rw [e3]
    _ = a ^ i * a ^ i' * (c ^ j * c ^ j') * (d ^ k * d ^ k') := by simp only [mul_assoc]

theorem aux_CenterD_normal_form {G : Type*} [Group G] (a c d : G)
    (hac : a * c = c * a) (had : a * d = d * a) (hcd : c * d = d * c) (z : G)
    (hz : z ∈ Subgroup.closure ({c, a, d} : Set G)) :
    ∃ i j k : ℤ, z = a ^ i * c ^ j * d ^ k := by
  let H : Subgroup G :=
    { carrier := {w | ∃ i j k : ℤ, w = a ^ i * c ^ j * d ^ k}
      mul_mem' := by
        rintro _ _ ⟨i, j, k, rfl⟩ ⟨i', j', k', rfl⟩
        exact ⟨i + i', j + j', k + k', aux_CenterD_comm_pow a c d hac had hcd i j k i' j' k'⟩
      one_mem' := ⟨0, 0, 0, by simp⟩
      inv_mem' := by
        rintro _ ⟨i, j, k, rfl⟩
        refine ⟨-i, -j, -k, ?_⟩
        apply inv_eq_of_mul_eq_one_right
        rw [aux_CenterD_comm_pow a c d hac had hcd i j k (-i) (-j) (-k)]
        simp }
  have hmem : ∀ w : G, w ∈ H ↔ ∃ i j k : ℤ, w = a ^ i * c ^ j * d ^ k := fun w => Iff.rfl
  have hsub : ({c, a, d} : Set G) ⊆ H := by
    intro w hw
    rcases hw with h | h | h
    · exact (hmem w).2 ⟨0, 1, 0, by simp [h]⟩
    · exact (hmem w).2 ⟨1, 0, 0, by simp [h]⟩
    · exact (hmem w).2 ⟨0, 0, 1, by simp [Set.mem_singleton_iff.mp h]⟩
  have hcl : Subgroup.closure ({c, a, d} : Set G) ≤ H := (Subgroup.closure_le H).2 hsub
  exact (hmem z).1 (hcl hz)

theorem mem_zpowers_d_of_central {G : Type*} [Group G] (x g a c d z : G) (m κ : ℤ)
    (hxa : x * a * x⁻¹ = d ^ m * a) (hm : ¬ (3 : ℤ) ∣ m)
    (hxc : x * c = c * x) (hxd : x * d = d * x)
    (hga : g * a = a * g) (hgc : g * c * g⁻¹ = d ^ κ * c) (hκ : ¬ (3 : ℤ) ∣ κ)
    (hgd : g * d = d * g)
    (hac : a * c = c * a) (had : a * d = d * a) (hcd : c * d = d * c)
    (ha3 : a ^ 3 = 1) (hc3 : c ^ 3 = 1) (hd3 : d ^ 3 = 1) (hd1 : d ≠ 1)
    (hz : z ∈ Subgroup.closure ({c, a, d} : Set G))
    (hzx : x * z = z * x) (hzg : g * z = z * g) : z ∈ Subgroup.zpowers d := by
  obtain ⟨i, j, k, rfl⟩ := aux_CenterD_normal_form a c d hac had hcd z hz
  have had' : Commute a d := had
  have hcd' : Commute c d := hcd
  have hdm_a : Commute (d ^ m) a := had'.symm.zpow_left m
  have hdk_c : Commute (d ^ κ) c := hcd'.symm.zpow_left κ
  have hφa : MulAut.conj x a = d ^ m * a := by rw [MulAut.conj_apply]; exact hxa
  have hφc : MulAut.conj x c = c := by rw [MulAut.conj_apply, hxc, mul_inv_cancel_right]
  have hφd : MulAut.conj x d = d := by rw [MulAut.conj_apply, hxd, mul_inv_cancel_right]
  have key1 : MulAut.conj x (a ^ i * c ^ j * d ^ k) = d ^ (m * i) * (a ^ i * c ^ j * d ^ k) := by
    simp only [map_mul, map_zpow, hφa, hφc, hφd]
    rw [hdm_a.mul_zpow i, ← zpow_mul]
    simp only [mul_assoc]
  have hxz : MulAut.conj x (a ^ i * c ^ j * d ^ k) = a ^ i * c ^ j * d ^ k := by
    rw [MulAut.conj_apply, hzx, mul_inv_cancel_right]
  have hdmi : d ^ (m * i) = 1 := by
    have h : d ^ (m * i) * (a ^ i * c ^ j * d ^ k) = a ^ i * c ^ j * d ^ k :=
      key1.symm.trans hxz
    exact mul_right_cancel (h.trans (one_mul _).symm)
  have hψa : MulAut.conj g a = a := by rw [MulAut.conj_apply, hga, mul_inv_cancel_right]
  have hψc : MulAut.conj g c = d ^ κ * c := by rw [MulAut.conj_apply]; exact hgc
  have hψd : MulAut.conj g d = d := by rw [MulAut.conj_apply, hgd, mul_inv_cancel_right]
  have key2 : MulAut.conj g (a ^ i * c ^ j * d ^ k) =
      a ^ i * (d ^ (κ * j) * c ^ j) * d ^ k := by
    simp only [map_mul, map_zpow, hψa, hψc, hψd]
    rw [hdk_c.mul_zpow j, ← zpow_mul]
  have hψz : MulAut.conj g (a ^ i * c ^ j * d ^ k) = a ^ i * c ^ j * d ^ k := by
    rw [MulAut.conj_apply, hzg, mul_inv_cancel_right]
  have hκj : d ^ (κ * j) = 1 := by
    have h : a ^ i * (d ^ (κ * j) * c ^ j) * d ^ k = a ^ i * c ^ j * d ^ k :=
      key2.symm.trans hψz
    have h2 : a ^ i * (d ^ (κ * j) * c ^ j) = a ^ i * c ^ j := mul_right_cancel h
    have h3 : d ^ (κ * j) * c ^ j = c ^ j := mul_left_cancel h2
    exact mul_right_cancel (h3.trans (one_mul _).symm)
  have hord : orderOf d = 3 := orderOf_eq_prime hd3 hd1
  have h3mi : (3 : ℤ) ∣ m * i := by
    have h := orderOf_dvd_iff_zpow_eq_one.mpr hdmi
    rw [hord] at h
    exact_mod_cast h
  have h3κj : (3 : ℤ) ∣ κ * j := by
    have h := orderOf_dvd_iff_zpow_eq_one.mpr hκj
    rw [hord] at h
    exact_mod_cast h
  have hi3 : (3 : ℤ) ∣ i := by
    rcases Int.prime_three.dvd_or_dvd h3mi with h | h
    · exact absurd h hm
    · exact h
  have hj3 : (3 : ℤ) ∣ j := by
    rcases Int.prime_three.dvd_or_dvd h3κj with h | h
    · exact absurd h hκ
    · exact h
  have ha3z : a ^ (3 : ℤ) = 1 := by simpa using ha3
  have hc3z : c ^ (3 : ℤ) = 1 := by simpa using hc3
  have hai : a ^ i = 1 := by
    obtain ⟨i', hi'⟩ := hi3
    rw [hi', zpow_mul, ha3z, one_zpow]
  have hcj : c ^ j = 1 := by
    obtain ⟨j', hj'⟩ := hj3
    rw [hj', zpow_mul, hc3z, one_zpow]
  rw [hai, hcj, one_mul, one_mul]
  exact zpow_mem (Subgroup.mem_zpowers d) k

end CFSG.RankThree.PartTwo.Sec11.Item1119Sym

end

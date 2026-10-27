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
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.GroupTheory.Nilpotent
public import Mathlib.GroupTheory.RegularWreathProduct
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

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open Subgroup

section Wreath

variable {A : Type*} [CommGroup A]

private theorem uc22p22qw_id_mul (y : A ≀ᵣ A) :
    (⟨fun q => q, 1⟩ : A ≀ᵣ A) * y = ⟨fun _ => y.right, 1⟩ * (y * ⟨fun q => q, 1⟩) := by
  ext q
  · simp only [RegularWreathProduct.mul_left, Pi.mul_apply, inv_one, one_mul]
    rw [mul_left_comm, mul_inv_cancel_left, mul_comm]
  · simp

private theorem uc22p22qw_const_mem_center (c : A) :
    (⟨fun _ => c, 1⟩ : A ≀ᵣ A) ∈ center (A ≀ᵣ A) := by
  rw [mem_center_iff]
  intro g
  ext q <;> simp [mul_comm]

private theorem uc22p22qw_id_mem_ucs_two :
    (⟨fun q => q, 1⟩ : A ≀ᵣ A) ∈ Subgroup.upperCentralSeries (A ≀ᵣ A) 2 := by
  rw [show (2 : ℕ) = 1 + 1 from rfl, Subgroup.mem_upperCentralSeries_succ_iff]
  intro y
  rw [Subgroup.upperCentralSeries_one, commutatorElement_def]
  have h := uc22p22qw_id_mul y
  generalize (⟨fun q => q, 1⟩ : A ≀ᵣ A) = x at h ⊢
  have : x * y * x⁻¹ * y⁻¹ = (⟨fun _ => y.right, 1⟩ : A ≀ᵣ A) := by
    rw [h]
    group
  rw [this]
  exact uc22p22qw_const_mem_center _

private theorem uc22p22qw_id_not_mem_center {s : A} (hs : s ≠ 1) :
    (⟨fun q => q, 1⟩ : A ≀ᵣ A) ∉ center (A ≀ᵣ A) := by
  intro h
  have h2 := congrArg (fun w : A ≀ᵣ A => w.left 1) (mem_center_iff.1 h ⟨1, s⟩)
  exact hs (by simpa using h2)

private theorem uc22p22qw_base_pow (f : A → A) (n : ℕ) :
    (⟨f, 1⟩ : A ≀ᵣ A) ^ n = ⟨fun q => f q ^ n, 1⟩ := by
  induction n with
  | zero => ext <;> simp
  | succ n ih =>
    rw [pow_succ, ih]
    ext <;> simp [pow_succ]

private theorem uc22p22qw_exists (hA3 : ∀ a : A, a ^ 3 = 1) {s : A} (hs : s ≠ 1) :
    ∃ x z : A ≀ᵣ A,
      x ∈ Subgroup.upperCentralSeries (A ≀ᵣ A) 2 ∧ z ∈ Subgroup.upperCentralSeries (A ≀ᵣ A) 2 ∧
      z ∈ center (A ≀ᵣ A) ∧ x ∉ center (A ≀ᵣ A) ∧ x ^ 3 = 1 ∧ z ^ 3 = 1 ∧ z ≠ 1 := by
  have hzc := uc22p22qw_const_mem_center s
  refine ⟨⟨fun q => q, 1⟩, ⟨fun _ => s, 1⟩, uc22p22qw_id_mem_ucs_two, ?_, hzc,
    uc22p22qw_id_not_mem_center hs, ?_, ?_, ?_⟩
  · rw [← Subgroup.upperCentralSeries_one] at hzc
    exact Subgroup.upperCentralSeries_mono _ (by norm_num : 1 ≤ 2) hzc
  · rw [uc22p22qw_base_pow]
    ext <;> simp [hA3]
  · rw [uc22p22qw_base_pow]
    ext <;> simp [hA3]
  · intro h
    exact hs (by simpa using congrArg (fun w : A ≀ᵣ A => w.left 1) h)

end Wreath

private theorem uc22p22qw_not_isCyclic {H : Type*} [Group H] [Finite H] {B : Subgroup H}
    {x z : H} (hxB : x ∈ B) (hzB : z ∈ B) (hz : z ∈ center H) (hxc : x ∉ center H)
    (hx3 : x ^ 3 = 1) (hz3 : z ^ 3 = 1) (hz1 : z ≠ 1) : ¬ IsCyclic ↥B := by
  intro hcyc
  have hx1 : x ≠ 1 := fun h => hxc (h ▸ one_mem _)
  have ox : orderOf (⟨x, hxB⟩ : B) = 3 :=
    orderOf_eq_prime (Subtype.ext (by simpa using hx3))
      (fun h => hx1 (by simpa using congrArg Subtype.val h))
  have oz : orderOf (⟨z, hzB⟩ : B) = 3 :=
    orderOf_eq_prime (Subtype.ext (by simpa using hz3))
      (fun h => hz1 (by simpa using congrArg Subtype.val h))
  have hEq : zpowers (⟨x, hxB⟩ : B) = zpowers (⟨z, hzB⟩ : B) := by
    rw [IsCyclic.subgroup_eq_iff_card_eq, Nat.card_zpowers, Nat.card_zpowers, ox, oz]
  obtain ⟨k, hk⟩ := mem_zpowers_iff.1 (hEq ▸ mem_zpowers (⟨x, hxB⟩ : B))
  apply hxc
  have hk' : z ^ k = x := by simpa using congrArg Subtype.val hk
  exact hk' ▸ zpow_mem hz k

private theorem uc22p22qw_mem_ucs_iff {H K : Type*} [Group H] [Group K] (e : H ≃* K) (n : ℕ)
    (x : H) :
    e x ∈ Subgroup.upperCentralSeries K n ↔ x ∈ Subgroup.upperCentralSeries H n := by
  rw [← Subgroup.comap_upperCentralSeries e n]
  exact Iff.rfl

private theorem uc22p22qw_mem_center_iff {H K : Type*} [Group H] [Group K] (e : H ≃* K) (x : H) :
    e x ∈ center K ↔ x ∈ center H := by
  rw [← Subgroup.upperCentralSeries_one K, ← Subgroup.upperCentralSeries_one H]
  exact uc22p22qw_mem_ucs_iff e 1 x

private theorem uc22p22qw_symm_pow {H K : Type*} [Group H] [Group K] (e : H ≃* K) {x : K}
    {n : ℕ} (h : x ^ n = 1) : e.symm x ^ n = 1 := by
  rw [← map_pow, h, map_one]

theorem uc22p22q_wreath_Z2 {G : Type} [Group G] {P : Subgroup G}
    (e : ↥P ≃* (Multiplicative (ZMod 3) ≀ᵣ Multiplicative (ZMod 3))) :
    ∃ B : Subgroup G, B ≤ (Subgroup.upperCentralSeries ↥P 2).map P.subtype ∧
      IsPGroup 3 ↥B ∧ ¬ IsCyclic ↥B := by
  have hcard : Nat.card (Multiplicative (ZMod 3)) = 3 := by
    rw [Nat.card_congr Multiplicative.toAdd]
    exact Nat.card_zmod 3
  have hA3 : ∀ a : Multiplicative (ZMod 3), a ^ 3 = 1 := fun a => by
    simpa [hcard] using pow_card_eq_one' (x := a)
  have hs : (Multiplicative.ofAdd (1 : ZMod 3)) ≠ 1 := by decide
  haveI : Finite ↥P := Finite.of_equiv _ e.symm.toEquiv
  have hWp : IsPGroup 3 (Multiplicative (ZMod 3) ≀ᵣ Multiplicative (ZMod 3)) := by
    rw [IsPGroup.iff_card]
    exact ⟨4, by rw [RegularWreathProduct.card, hcard]; norm_num⟩
  have hPp : IsPGroup 3 ↥P := hWp.of_equiv e.symm
  obtain ⟨x, z, hxZ, hzZ, hzc, hxc, hx3, hz3, hz1⟩ := uc22p22qw_exists hA3 hs
  let eB := Subgroup.equivMapOfInjective (Subgroup.upperCentralSeries ↥P 2) P.subtype
    P.subtype_injective
  refine ⟨(Subgroup.upperCentralSeries ↥P 2).map P.subtype, le_rfl,
    (hPp.to_subgroup _).of_equiv eB, fun hcyc => ?_⟩
  refine uc22p22qw_not_isCyclic (x := e.symm x) (z := e.symm z)
    ((uc22p22qw_mem_ucs_iff e.symm 2 x).2 hxZ) ((uc22p22qw_mem_ucs_iff e.symm 2 z).2 hzZ)
    ((uc22p22qw_mem_center_iff e.symm z).2 hzc)
    (fun h => hxc ((uc22p22qw_mem_center_iff e.symm x).1 h))
    (uc22p22qw_symm_pow e hx3) (uc22p22qw_symm_pow e hz3)
    (fun h => hz1 (e.symm.injective (h.trans (map_one e.symm).symm))) (eB.isCyclic.2 hcyc)

end CFSG.LocalAnalysis.UniquenessCase.UC22

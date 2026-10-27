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
public import Mathlib.RingTheory.ZMod.UnitsCyclic
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

namespace CFSG.Walter.J1Props

open scoped Pointwise

variable {L : Type*} [Group L]

abbrev normQuot (P : Subgroup L) : Type _ :=
  Subgroup.normalizer (P : Set L) ⧸
    (Subgroup.centralizer (P : Set L)).subgroupOf (Subgroup.normalizer (P : Set L))

noncomputable def normQuotEquiv (P : Subgroup L) : normQuot P ≃* P.normalizerMonoidHom.range :=
  (QuotientGroup.quotientMulEquivOfEq (Subgroup.normalizerMonoidHom_ker P).symm).trans
    (QuotientGroup.quotientKerEquivRange _)

theorem isCyclic_normQuot [Finite L] {p : ℕ} [hp : Fact p.Prime] (P : Subgroup L)
    (hP : Nat.card P = p) :
    IsCyclic (normQuot P) ∧ Nat.card (normQuot P) ∣ p - 1 ∧ Nat.card (normQuot P) ∣ Nat.card L := by
  have hPc : IsCyclic P := isCyclic_of_prime_card hP
  have hA : IsCyclic (MulAut P) := by
    have : IsCyclic (ZMod (Nat.card P))ˣ := by
      rw [hP]
      exact ZMod.isCyclic_units_prime hp.out
    exact isCyclic_of_surjective (IsCyclic.mulAutMulEquiv P).symm
      (IsCyclic.mulAutMulEquiv P).symm.surjective
  have hR : IsCyclic P.normalizerMonoidHom.range := Subgroup.isCyclic _
  refine ⟨isCyclic_of_surjective (normQuotEquiv P).symm (normQuotEquiv P).symm.surjective, ?_, ?_⟩
  · rw [Nat.card_congr (normQuotEquiv P).toEquiv]
    have h := Subgroup.card_subgroup_dvd_card P.normalizerMonoidHom.range
    rwa [IsCyclic.card_mulAut, hP, Nat.totient_prime hp.out] at h
  · have h1 : Nat.card (normQuot P) ∣ Nat.card (Subgroup.normalizer (P : Set L)) := by
      rw [← Subgroup.index_eq_card]
      exact Subgroup.index_dvd_card _
    exact h1.trans (Subgroup.card_subgroup_dvd_card _)

theorem mem_centralizer_zpowers_iff {y g : L} :
    g ∈ Subgroup.centralizer ((Subgroup.zpowers y : Subgroup L) : Set L) ↔ g * y = y * g := by
  rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure,
    Subgroup.mem_centralizer_singleton_iff]

theorem dvd_card_normQuot [Finite L] {y r : L}
    (hr : r ∈ Subgroup.normalizer ((Subgroup.zpowers y : Subgroup L) : Set L)) {e : ℕ}
    (he0 : 0 < e) (he : r ^ e * y = y * r ^ e)
    (hq : ∀ q : ℕ, q.Prime → q ∣ e → r ^ (e / q) * y ≠ y * r ^ (e / q)) :
    e ∣ Nat.card (normQuot (Subgroup.zpowers y)) := by
  set P := Subgroup.zpowers y
  set z : normQuot P := ((⟨r, hr⟩ : Subgroup.normalizer (P : Set L)) : normQuot P)
  have key : ∀ j : ℕ, z ^ j = 1 ↔ r ^ j * y = y * r ^ j := by
    intro j
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf,
      Subgroup.coe_pow, mem_centralizer_zpowers_iff]
  have hz : orderOf z = e :=
    orderOf_eq_of_pow_and_pow_div_prime he0 ((key e).mpr he)
      (fun q hq' hqe h => hq q hq' hqe ((key _).mp h))
  rw [← hz]
  exact orderOf_dvd_natCard z

theorem exists_inv_of_sylow [Finite L] {p : ℕ} [Fact p.Prime] {y i : L} (hi : orderOf i = 2)
    (hiy : i * y * i⁻¹ = y⁻¹) (P₀ : Sylow p L) (hP₀ : (P₀ : Subgroup L) = Subgroup.zpowers y)
    (P : Sylow p L) :
    ∃ x : L, orderOf x = 2 ∧ ∀ z ∈ (P : Subgroup L), x * z * x⁻¹ = z⁻¹ := by
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq L P₀ P
  refine ⟨g * i * g⁻¹, by rw [← MulAut.conj_apply, MulEquiv.orderOf_eq, hi], ?_⟩
  intro z hz
  rw [← hg, Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem,
    MulAut.smul_def, MulAut.conj_inv_apply, hP₀] at hz
  obtain ⟨k, hk⟩ := hz
  have hiyk : i * y ^ k * i⁻¹ = (y ^ k)⁻¹ := by rw [← conj_zpow, hiy, inv_zpow]
  have hz' : z = g * y ^ k * g⁻¹ := by
    have : z = g * (g⁻¹ * z * g) * g⁻¹ := by group
    rw [this, ← hk]
  rw [hz']
  calc g * i * g⁻¹ * (g * y ^ k * g⁻¹) * (g * i * g⁻¹)⁻¹ = g * (i * y ^ k * i⁻¹) * g⁻¹ := by
        group
    _ = (g * y ^ k * g⁻¹)⁻¹ := by rw [hiyk]; group

end CFSG.Walter.J1Props

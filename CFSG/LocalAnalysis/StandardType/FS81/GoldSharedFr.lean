module

import CFSG.GroupTheory.QuasiDihedralFusion.Basic
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

namespace CFSG.StandardType.FrameRoute.FS81

private theorem q2cN7fr_normalizer_inf_sylow_sup_eq_top {H : Type*} [Group H] [Finite H]
    (S : Sylow 2 H) (K : Subgroup H) [K.Normal] :
    Subgroup.normalizer (((S : Subgroup H) ⊓ K : Subgroup H) : Set H) ⊔ K = ⊤ := by
  have h := Sylow.normalizer_sup_eq_top
    (CFSG.QuasiDihedralFusion.sylowInfNormal S K)
  rwa [CFSG.QuasiDihedralFusion.sylowInfNormal_coe, Subgroup.subgroupOf_map_subtype] at h

theorem exists_mul_normalizer_inf_sylow {X : Type} [Group X] [Finite X] {N C S₀ : Subgroup X}
    (hCN : C ≤ N) (hC : ∀ n ∈ N, ∀ c ∈ C, n * c * n⁻¹ ∈ C) (hSN : S₀ ≤ N) (hS : IsPGroup 2 S₀)
    (hidx : Nat.Coprime 2 (S₀.subgroupOf N).index) :
    ∀ n ∈ N, ∃ c ∈ C, ∃ m ∈ N, n = c * m ∧
      m ∈ Subgroup.normalizer ((S₀ ⊓ C : Subgroup X) : Set X) := by
  haveI hCnormal : (C.subgroupOf N).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer hCN, Subgroup.le_normalizer_iff]
    exact hC
  have hS2 : IsPGroup 2 (S₀.subgroupOf N) := hS.comap_subtype
  have hSidx : ¬ 2 ∣ (S₀.subgroupOf N).index :=
    Nat.prime_two.coprime_iff_not_dvd.mp hidx
  let S : Sylow 2 ↥N := hS2.toSylow hSidx
  have hSK : ((S : Subgroup ↥N) ⊓ C.subgroupOf N : Subgroup ↥N) =
      (S₀ ⊓ C).subgroupOf N := by
    have hScoe : (S : Subgroup ↥N) = S₀.subgroupOf N := IsPGroup.toSylow_coe _ _
    rw [hScoe]
    ext x
    simp only [Subgroup.mem_inf, Subgroup.mem_subgroupOf]
  have hFr := q2cN7fr_normalizer_inf_sylow_sup_eq_top S (C.subgroupOf N)
  rw [hSK, sup_comm] at hFr
  intro n hn
  have hx : (⟨n, hn⟩ : ↥N) ∈ C.subgroupOf N ⊔
      Subgroup.normalizer ((S₀ ⊓ C).subgroupOf N) := by
    rw [hFr]
    trivial
  rw [Subgroup.mem_sup_of_normal_left] at hx
  obtain ⟨y, hy, z, hz, hyz⟩ := hx
  have hyC : (y : X) ∈ C := Subgroup.mem_subgroupOf.mp hy
  have hzNorm : (z : X) ∈ Subgroup.normalizer (S₀ ⊓ C : Subgroup X) := by
    have hz' := hz
    rw [← Subgroup.subgroupOf_normalizer_eq
      (show S₀ ⊓ C ≤ N from inf_le_left.trans hSN)] at hz'
    exact Subgroup.mem_subgroupOf.mp hz'
  exact ⟨(y : X), hyC, (z : X), z.property, (congrArg Subtype.val hyz).symm, hzNorm⟩

end CFSG.StandardType.FrameRoute.FS81

end

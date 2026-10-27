module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PCore.PCore
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

namespace CFSG.Sporadic.Co1Patterson

open Subgroup

theorem card_sq_pCore_eq {K K' : Type*} [Group K] [Group K'] (β : K ≃* K') (t : K) :
    Nat.card {x : CFSG.pCore 2 K // (x : K) ^ 2 = t} =
      Nat.card {x : CFSG.pCore 2 K' // (x : K') ^ 2 = β t} := by
  have hmap := CFSG.pCore_map_iso 2 β
  have hmap' := CFSG.pCore_map_iso 2 β.symm
  refine Nat.card_congr
    { toFun := fun x => ⟨⟨β x.1, hmap ▸ ⟨x.1.1, x.1.2, rfl⟩⟩, by
        rw [← map_pow, x.2]⟩
      invFun := fun y => ⟨⟨β.symm y.1, hmap' ▸ ⟨y.1.1, y.1.2, rfl⟩⟩, by
        rw [← map_pow, y.2, MulEquiv.symm_apply_apply]⟩
      left_inv := fun x => by
        apply Subtype.ext
        apply Subtype.ext
        exact β.symm_apply_apply _
      right_inv := fun y => by
        apply Subtype.ext
        apply Subtype.ext
        exact β.apply_symm_apply _ }

theorem card_sq_pCore_eq_of_aut {K : Type*} [Group K] (α : K ≃* K) (t : K) :
    Nat.card {x : CFSG.pCore 2 K // (x : K) ^ 2 = t} =
      Nat.card {x : CFSG.pCore 2 K // (x : K) ^ 2 = α t} :=
  card_sq_pCore_eq α t

theorem pCore_subgroupOf_eq {G : Type*} [Group G] {K R : Subgroup G}
    (hnorm : ∀ k ∈ K, ∀ r ∈ R, k * r * k⁻¹ ∈ R) (hR : IsPGroup 2 R)
    (hmax : ∀ N : Subgroup G, N ≤ K → (∀ k ∈ K, ∀ n ∈ N, k * n * k⁻¹ ∈ N) → IsPGroup 2 N →
      N ≤ R) :
    CFSG.pCore 2 K = R.subgroupOf K := by
  apply le_antisymm
  · intro x hx
    rw [mem_subgroupOf]
    refine hmax ((CFSG.pCore 2 K).map K.subtype) ?_ ?_ ?_ ⟨x, hx, rfl⟩
    · rintro _ ⟨y, -, rfl⟩
      exact y.2
    · rintro k hk _ ⟨y, hy, rfl⟩
      refine ⟨⟨k, hk⟩ * y * ⟨k, hk⟩⁻¹, (CFSG.pCore_normal (p := 2) (G := K)).conj_mem y hy _, ?_⟩
      simp
    · exact IsPGroup.map CFSG.pCore_isPGroup _
  · refine le_sSup ⟨⟨fun r hr k => ?_⟩, ?_⟩
    · rw [mem_subgroupOf] at hr ⊢
      simpa using hnorm k.1 k.2 r.1 hr
    · intro r
      obtain ⟨n, hn⟩ := hR ⟨r.1, r.2⟩
      exact ⟨n, Subtype.ext (Subtype.ext (by simpa using congrArg Subtype.val hn))⟩

end CFSG.Sporadic.Co1Patterson

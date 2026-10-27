module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.ElementaryAbelian
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
public import Mathlib.Order.CompletePartialOrder
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

namespace CFSG.Quasithin.SteinbergCB

open Subgroup
open scoped Pointwise

variable {G : Type*} [Group G]

theorem mem_conj_inv_smul_iff {V : Subgroup G} {m x : G} :
    x ∈ MulAut.conj m⁻¹ • V ↔ m * x * m⁻¹ ∈ V := by
  rw [mem_pointwise_smul_iff_inv_smul_mem, ← map_inv, inv_inv, MulAut.smul_def,
    MulAut.conj_apply]

theorem irreducible_local_module_is_TI_in_local_normalizer [Finite G] {L M V : Subgroup G}
    (hLM : L ≤ M) (hL : (L.subgroupOf M).Normal) (_hV1 : V ≠ ⊥)
    (_hVe : CFSG.IsElementaryAbelian 2 V) (hLV : L ≤ normalizer (V : Set G))
    (hirr : ∀ W : Subgroup G, W ≤ V → (∀ l ∈ L, ∀ w ∈ W, l * w * l⁻¹ ∈ W) → W = ⊥ ∨ W = V) :
    (∀ m ∈ M, V ⊓ MulAut.conj m⁻¹ • V = ⊥ ∨ MulAut.conj m⁻¹ • V = V) ∧
    (∀ U : Subgroup G, U ≠ ⊥ → U ≤ V →
      M ⊓ normalizer (U : Set G) ≤ M ⊓ normalizer (V : Set G)) ∧
    (normalizer (V : Set G) ≤ M → ∀ U : Subgroup G, U ≠ ⊥ → U ≤ V →
      ∀ H : Subgroup G, H ≤ normalizer (U : Set G) → H ⊓ M = H ⊓ normalizer (V : Set G)) := by
  have hconjL : ∀ m ∈ M, ∀ l ∈ L, m * l * m⁻¹ ∈ L := fun m hm l hl => by
    have h := hL.conj_mem ⟨l, hLM hl⟩ (by simpa [mem_subgroupOf] using hl) ⟨m, hm⟩
    simpa [mem_subgroupOf] using h
  have hTI : ∀ m ∈ M, V ⊓ MulAut.conj m⁻¹ • V = ⊥ ∨ MulAut.conj m⁻¹ • V = V := by
    intro m hm
    have hinv : ∀ l ∈ L, ∀ w ∈ V ⊓ MulAut.conj m⁻¹ • V, l * w * l⁻¹ ∈ V ⊓ MulAut.conj m⁻¹ • V := by
      intro l hl w hw
      rw [mem_inf] at hw ⊢
      refine ⟨(mem_normalizer_iff.1 (hLV hl) w).1 hw.1, ?_⟩
      rw [mem_conj_inv_smul_iff] at hw ⊢
      have hl' := hconjL m hm l hl
      have h := (mem_normalizer_iff.1 (hLV hl') (m * w * m⁻¹)).1 hw.2
      have heq : m * (l * w * l⁻¹) * m⁻¹ = m * l * m⁻¹ * (m * w * m⁻¹) * (m * l * m⁻¹)⁻¹ := by
        group
      rw [heq]
      exact h
    rcases hirr _ inf_le_left hinv with h | h
    · exact Or.inl h
    · right
      have hle : V ≤ MulAut.conj m⁻¹ • V := fun x hx => by
        rw [← h] at hx
        exact (mem_inf.1 hx).2
      symm
      refine Subgroup.eq_of_le_of_card_ge hle ?_
      rw [← Nat.card_congr (Subgroup.equivSMul (MulAut.conj m⁻¹) V).toEquiv]
  have hnorm : ∀ U : Subgroup G, U ≠ ⊥ → U ≤ V →
      M ⊓ normalizer (U : Set G) ≤ M ⊓ normalizer (V : Set G) := by
    intro U hU1 hUV m hm
    obtain ⟨hmM, hmU⟩ := mem_inf.1 hm
    refine mem_inf.2 ⟨hmM, ?_⟩
    have hUle : U ≤ V ⊓ MulAut.conj m⁻¹ • V := fun u hu =>
      mem_inf.2 ⟨hUV hu, mem_conj_inv_smul_iff.2 (hUV ((mem_normalizer_iff.1 hmU u).1 hu))⟩
    rcases hTI m hmM with h | h
    · exact absurd (le_bot_iff.1 (h ▸ hUle)) hU1
    · rw [mem_normalizer_iff]
      intro x
      constructor
      · intro hx
        rw [← h] at hx
        exact mem_conj_inv_smul_iff.1 hx
      · intro hx
        rw [← h]
        exact mem_conj_inv_smul_iff.2 hx
  refine ⟨hTI, hnorm, fun hNM U hU1 hUV H hHU => le_antisymm ?_ ?_⟩
  · intro h hh
    obtain ⟨hhH, hhM⟩ := mem_inf.1 hh
    exact mem_inf.2 ⟨hhH, (mem_inf.1 (hnorm U hU1 hUV (mem_inf.2 ⟨hhM, hHU hhH⟩))).2⟩
  · intro h hh
    obtain ⟨hhH, hhV⟩ := mem_inf.1 hh
    exact mem_inf.2 ⟨hhH, hNM hhV⟩

end CFSG.Quasithin.SteinbergCB

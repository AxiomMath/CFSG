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

namespace CFSG.RankThree.PartTwo.Sec21

theorem ffs_exists_conj_map_le {G : Type*} [Group G] [Finite G] {C : Subgroup G}
    (P : Sylow 3 C) {E : Subgroup G} (hEC : E ≤ C) (hE : IsPGroup 3 E) :
    ∃ c ∈ C, ∀ x ∈ E, c * x * c⁻¹ ∈ (P : Subgroup C).map C.subtype := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨Q, hQ⟩ := (hE.comap_subtype (K := C)).exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq ↥C Q P
  refine ⟨(g : G), g.2, ?_⟩
  intro x hx
  have hxE : (⟨x, hEC hx⟩ : C) ∈ E.comap C.subtype := Subgroup.mem_comap.mpr hx
  have hk : (⟨x, hEC hx⟩ : C) ∈ (Q : Subgroup C) := hQ hxE
  have hmem : g * (⟨x, hEC hx⟩ : C) * g⁻¹ ∈ (P : Subgroup C) := by
    rw [← hg, Sylow.coe_subgroup_smul, Subgroup.mem_smul_pointwise_iff_exists]
    exact ⟨⟨x, hEC hx⟩, hk, rfl⟩
  exact Subgroup.mem_map_of_mem C.subtype hmem

theorem ffs_exists_conj_mem_of_card_eq {G : Type*} [Group G] [Finite G] {C : Subgroup G}
    (P : Sylow 3 C) {B' : Subgroup G} (hB'C : B' ≤ C)
    (hcard : Nat.card B' = Nat.card (P : Subgroup C)) :
    ∃ c ∈ C, ∀ x ∈ (P : Subgroup C).map C.subtype, c * x * c⁻¹ ∈ B' := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hcardB : Nat.card (B'.subgroupOf C) = Nat.card (P : Subgroup C) :=
    (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hB'C).toEquiv).trans hcard
  have hB3 : IsPGroup 3 (B'.subgroupOf C) :=
    IsPGroup.of_card (hcardB.trans (Sylow.card_eq_multiplicity P))
  obtain ⟨Q, hQ⟩ := hB3.exists_le_sylow
  have hQP : Nat.card (Q : Subgroup C) = Nat.card (P : Subgroup C) :=
    (Sylow.card_eq_multiplicity Q).trans (Sylow.card_eq_multiplicity P).symm
  have hBQ : B'.subgroupOf C = (Q : Subgroup C) :=
    Subgroup.eq_of_le_of_card_ge hQ (hQP.trans hcardB.symm).le
  obtain ⟨c, hc⟩ := MulAction.exists_smul_eq ↥C P Q
  refine ⟨(c : G), c.2, ?_⟩
  intro x hx
  obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
  have hmem : c * y * c⁻¹ ∈ (Q : Subgroup C) := by
    rw [← hc, Sylow.coe_subgroup_smul, Subgroup.mem_smul_pointwise_iff_exists]
    exact ⟨y, hy, rfl⟩
  rw [← hBQ] at hmem
  exact Subgroup.mem_subgroupOf.mp hmem

end CFSG.RankThree.PartTwo.Sec21

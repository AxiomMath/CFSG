module

public import CFSG.GroupTheory.LocalCores.Components
public import CFSG.GroupTheory.LocalCores.PrimeSetCore
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

namespace CFSG.Sporadic.SuzOddCore

open CFSG CFSG.LocalCores Subgroup

theorem commutator_le_of_index_two {G : Type*} [Group G] {D : Subgroup G} (hD : D.index = 2) :
    ⁅(⊤ : Subgroup G), (⊤ : Subgroup G)⁆ ≤ D := by
  rw [Subgroup.commutator_le]
  intro x _ y _
  have h := fun a b => Subgroup.mul_mem_iff_of_index_two (H := D) hD (a := a) (b := b)
  rw [commutatorElement_def, h, h, inv_mem_iff (x := y), h, inv_mem_iff (x := x)]
  tauto

theorem center_map_le {E K : Type*} [Group E] [Group K] (f : E →* K) (B : Subgroup E)
    {z : B} (hz : z ∈ center B) : ∀ y ∈ B.map f, f z * y = y * f z := by
  rintro _ ⟨b, hb, rfl⟩
  have := Subgroup.mem_center_iff.1 hz ⟨b, hb⟩
  have := congrArg (fun w : B => f (w : E)) this
  simpa [map_mul] using this.symm

theorem center_eq_bot_of_simple' {G : Type*} [Group G] (hs : IsSimpleGroup G)
    (h : ∃ a b : G, a * b ≠ b * a) : Subgroup.center G = ⊥ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center G) with h1 | h1
  · exact h1
  · exfalso
    obtain ⟨a, b, hab⟩ := h
    have hb : b ∈ Subgroup.center G := h1 ▸ Subgroup.mem_top b
    exact hab (Subgroup.mem_center_iff.1 hb a)

theorem card_quotient_center_of_component {E K : Type*} [Group E] [Group K] [Finite E]
    (ρ : E →* K) (hρ : Function.Surjective ρ) (hker : Group.IsSolvable ρ.ker)
    (D : Subgroup K) (hDi : D.index = 2) (hDs : IsSimpleGroup D)
    (hDnc : ∃ a b : D, a * b ≠ b * a) {B : Subgroup E} (hB : IsComponent B) :
    Nat.card (B ⧸ center B) = Nat.card D := by
  obtain ⟨hq, hsub⟩ := hB
  have hperf : Group.IsPerfect B := hq.1
  have hnt : Nontrivial B := isQuasisimple_nontrivial hq
  have hBB : ⁅B, B⁆ = B := by
    rw [← Subgroup.map_subtype_commutator, hperf.commutator_eq_top, ← MonoidHom.range_eq_map,
      Subgroup.range_subtype]
  have hcomm : ⁅B.map ρ, B.map ρ⁆ = B.map ρ := by rw [← Subgroup.map_commutator, hBB]
  have hle : B.map ρ ≤ D := by
    rw [← hcomm]
    exact (Subgroup.commutator_mono le_top le_top).trans (commutator_le_of_index_two hDi)
  have hsubD : ((B.map ρ).subgroupOf D).IsSubnormal := (hsub.map hρ).subgroupOf
  rcases hsubD.eq_bot_or_top_of_isSimpleGroup hDs with h | h
  ·
    exfalso
    have hBk : B ≤ ρ.ker := by
      intro b hb
      rw [MonoidHom.mem_ker]
      have : (⟨ρ b, hle ⟨b, hb, rfl⟩⟩ : D) ∈ (B.map ρ).subgroupOf D := by
        rw [Subgroup.mem_subgroupOf]
        exact ⟨b, hb, rfl⟩
      rw [h, Subgroup.mem_bot] at this
      exact congrArg Subtype.val this
    have : Group.IsSolvable B :=
      Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hBk)
    exact Group.IsPerfect.not_isSolvable B this
  · have hBD : B.map ρ = D := by
      apply le_antisymm hle
      intro d hd
      have : (⟨d, hd⟩ : D) ∈ (B.map ρ).subgroupOf D := h ▸ Subgroup.mem_top _
      rwa [Subgroup.mem_subgroupOf] at this
    set ρB : B →* K := ρ.comp B.subtype
    have hrange : ρB.range = D := by
      rw [MonoidHom.range_comp, Subgroup.range_subtype, hBD]
    have hkerB : ρB.ker = center B := by
      apply le_antisymm
      · rcases quasisimple_normal_subgroups hq (ρB.normal_ker) with h1 | h1
        · exfalso
          obtain ⟨a, b, hab⟩ := hDnc
          obtain ⟨x, hx⟩ := (hrange ▸ a.2 : (a : K) ∈ ρB.range)
          have hx1 : x ∈ ρB.ker := h1 ▸ Subgroup.mem_top x
          rw [MonoidHom.mem_ker, hx] at hx1
          apply hab
          have : a = 1 := Subtype.ext hx1
          rw [this, one_mul, mul_one]
        · exact h1
      · intro z hz
        rw [MonoidHom.mem_ker]
        have hzD : ρB z ∈ D := by rw [← hrange]; exact ⟨z, rfl⟩
        have hc : (⟨ρB z, hzD⟩ : D) ∈ center D := by
          rw [Subgroup.mem_center_iff]
          intro g
          apply Subtype.ext
          have := center_map_le ρ B hz (g : K) (by rw [hBD]; exact g.2)
          exact this.symm
        rw [center_eq_bot_of_simple' hDs hDnc, Subgroup.mem_bot] at hc
        exact congrArg Subtype.val hc
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup ρB.ker
    rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange ρB).toEquiv, hrange, hkerB] at h1
    have h2 := Subgroup.card_eq_card_quotient_mul_card_subgroup (center B)
    have hpos : 0 < Nat.card (center B) := Nat.card_pos
    rw [h2] at h1
    exact Nat.eq_of_mul_eq_mul_right hpos h1

theorem not_isComponent_of_le_pgroup {E : Type*} [Group E] [Finite E] {p : ℕ} [Fact p.Prime]
    {Q B : Subgroup E} (hQ : IsPGroup p Q) (hBQ : B ≤ Q) : ¬ IsComponent B := by
  rintro ⟨hq, -⟩
  have : Nontrivial B := isQuasisimple_nontrivial hq
  have : Group.IsPerfect B := hq.1
  have hB : IsPGroup p B := hQ.to_le hBQ
  have : Group.IsNilpotent B := hB.isNilpotent
  have : Group.IsSolvable B := inferInstance
  exact Group.IsPerfect.not_isSolvable B this

end CFSG.Sporadic.SuzOddCore

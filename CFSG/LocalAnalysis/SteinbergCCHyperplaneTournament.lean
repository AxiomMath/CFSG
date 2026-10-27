module

public import Mathlib.Algebra.Module.StablyFree.Basic
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
public import Mathlib.GroupTheory.Nilpotent
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Coalgebra.IsFrobenius
public import Mathlib.RingTheory.HopfAlgebra.Basic
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.RingTheory.TotallySplit
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

namespace CFSG.LocalAnalysis

theorem exists_functional_ker_eq_of_finrank_quotient_eq_one {V : Type*} [AddCommGroup V]
    [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V] (U : Submodule (ZMod 2) V)
    (hU : Module.finrank (ZMod 2) (V ⧸ U) = 1) :
    ∃ f : V →ₗ[ZMod 2] ZMod 2, ∀ v, f v = 0 ↔ v ∈ U := by
  let e : (V ⧸ U) ≃ₗ[ZMod 2] ZMod 2 :=
    LinearEquiv.ofFinrankEq _ _ (by rw [hU, Module.finrank_self])
  refine ⟨e.toLinearMap ∘ₗ U.mkQ, fun v => ?_⟩
  rw [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.map_eq_zero_iff,
    Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]

theorem binary_hyperplane_tournament_dimension_obstruction {V : Type*} [AddCommGroup V]
    [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V] (U : V → Submodule (ZMod 2) V)
    (hhyp : ∀ x : V, x ≠ 0 → Module.finrank (ZMod 2) (V ⧸ U x) = 1)
    (hxor : ∀ x y : V, x ≠ 0 → y ≠ 0 → x ≠ y → Xor (y ∈ U x) (x ∈ U y)) :
    Module.finrank (ZMod 2) V ≤ 3 := by
  classical
  by_cases hdim : Module.finrank (ZMod 2) V ≤ 2
  · omega
  have hf : ∀ x : V, ∃ f : V →ₗ[ZMod 2] ZMod 2, x ≠ 0 → ∀ v, f v = 0 ↔ v ∈ U x := by
    intro x
    by_cases hx : x = 0
    · exact ⟨0, fun h => absurd hx h⟩
    · obtain ⟨f, hf⟩ := exists_functional_ker_eq_of_finrank_quotient_eq_one (U x) (hhyp x hx)
      exact ⟨f, fun _ => hf⟩
  choose f hfker using hf
  have hval : ∀ a : ZMod 2, a ≠ 0 → a = 1 := by decide
  have hrec : ∀ x y : V, x ≠ 0 → y ≠ 0 → x ≠ y → f x y = 1 + f y x := by
    intro x y hx hy hxy
    rcases hxor x y hx hy hxy with ⟨hyx, hxy'⟩ | ⟨hxy', hyx⟩
    · rw [(hfker x hx y).mpr hyx, hval _ (fun h => hxy' ((hfker y hy x).mp h))]
      decide
    · rw [(hfker y hy x).mpr hxy', hval _ (fun h => hyx ((hfker x hx y).mp h))]
      decide
  have hlt : 1 < Module.finrank (ZMod 2) V := by omega
  let b := Module.finBasis (ZMod 2) V
  let x : V := b ⟨0, by omega⟩
  let y : V := b ⟨1, hlt⟩
  have hx : x ≠ 0 := b.ne_zero _
  have hy : y ≠ 0 := b.ne_zero _
  have hxy : x ≠ y := fun h => by
    have := b.injective h
    simp [Fin.ext_iff] at this
  set z : V := x + y with hz
  have hz0 : z ≠ 0 := fun h => hxy (by
    have h' : x = -y := eq_neg_of_add_eq_zero_left h
    rw [h', ZModModule.neg_eq_self])
  set E : Submodule (ZMod 2) V := Submodule.span (ZMod 2) (Set.range ![x, y]) with hE
  have hxE : x ∈ E := Submodule.subset_span ⟨0, rfl⟩
  have hyE : y ∈ E := Submodule.subset_span ⟨1, rfl⟩
  let g : V →ₗ[ZMod 2] ZMod 2 := f x + f y + f z
  have hgt : ∀ t : V, t ∉ E → g t = 1 := by
    intro t htE
    have ht0 : t ≠ 0 := fun h => htE (h ▸ E.zero_mem)
    have htx : x ≠ t := fun h => htE (h ▸ hxE)
    have hty : y ≠ t := fun h => htE (h ▸ hyE)
    have htz : z ≠ t := fun h => htE (h ▸ E.add_mem hxE hyE)
    change f x t + f y t + f z t = 1
    rw [hrec x t hx ht0 htx, hrec y t hy ht0 hty, hrec z t hz0 ht0 htz, hz, map_add]
    generalize f t x = a
    generalize f t y = c
    revert a c
    decide
  have hE2 : Module.finrank (ZMod 2) E ≤ 2 := by
    have h := finrank_range_le_card (R := ZMod 2) (b := ![x, y])
    rwa [Fintype.card_fin] at h
  obtain ⟨w, hw⟩ : ∃ w : V, w ∉ E := by
    by_contra h
    simp only [not_exists, not_not] at h
    have hEtop : E = ⊤ := eq_top_iff.mpr fun v _ => h v
    have htop := finrank_top (ZMod 2) V
    rw [← hEtop] at htop
    omega
  have hw0 : w ≠ 0 := fun h => hw (h ▸ E.zero_mem)
  have hsup : E ⊔ Submodule.span (ZMod 2) {w} = ⊤ := by
    refine eq_top_iff.mpr fun v _ => ?_
    by_cases hv : v ∈ E
    · exact Submodule.mem_sup_left hv
    · have hvw : v - w ∈ E := by
        by_contra hvw
        have h1 := hgt _ hvw
        rw [map_sub, hgt v hv, hgt w hw] at h1
        revert h1
        decide
      rw [← sub_add_cancel v w]
      exact Submodule.add_mem_sup hvw (Submodule.mem_span_singleton_self w)
  have hle := Submodule.finrank_add_le_finrank_add_finrank E (Submodule.span (ZMod 2) {w})
  rw [hsup, finrank_top, finrank_span_singleton hw0] at hle
  omega

end CFSG.LocalAnalysis

module

public import CFSG.LocalAnalysis.StandardType.KGLangS1EFixedLiftFin
import CFSG.LocalAnalysis.StandardType.GGLieM6cDescent

public section

set_option linter.unusedSectionVars false

namespace CFSG.StandardType

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Minuscule
  CFSG.LieType.Steinberg.Isogeny CFSG.HardMathSupport.Timmesfeld.CrossChar


theorem kgLangS1EFixedLift_descent (k : Type) [Field k] [Finite k] (L : Type) [Field L]
    [CharP L 2] [Algebra k L] [Algebra.IsAlgebraic k L] {c g : ModGL Tag.E6 L}
    (hc : c ∈ adjointGroup Tag.E6 L) (hg : g ∈ adjointGroup Tag.E6 L) :
    ∃ (k' : Type) (_ : Field k') (_ : Finite k') (κ : k →+* k') (ι : k' →+* L)
      (c' g' : ModGL Tag.E6 k'), ι.comp κ = algebraMap k L ∧ c' ∈ adjointGroup Tag.E6 k' ∧
        g' ∈ adjointGroup Tag.E6 k' ∧ baseChangeGL ι c' = c ∧ baseChangeGL ι g' = g := by
  classical
  haveI : CharP k 2 := RingHom.charP (algebraMap k L) (algebraMap k L).injective 2
  letI : Algebra (ZMod 2) k := ZMod.algebra k 2
  letI : Algebra (ZMod 2) L := ZMod.algebra L 2
  haveI : IsScalarTower (ZMod 2) k L := IsScalarTower.of_algebraMap_eq' (RingHom.ext_zmod _ _)
  haveI : Algebra.IsAlgebraic (ZMod 2) k := Algebra.IsAlgebraic.of_finite (ZMod 2) k
  haveI : Algebra.IsAlgebraic (ZMod 2) L := Algebra.IsAlgebraic.trans (ZMod 2) k L
  have hS : (↑({c, g} : Finset (ModGL Tag.E6 L)) : Set (ModGL Tag.E6 L)) ⊆
      ↑(adjointGroup Tag.E6 L) := by
    intro s hs
    simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
      Set.mem_singleton_iff] at hs
    rcases hs with rfl | rfl <;> assumption
  obtain ⟨k', hF, hFin, κ, ι, hcomp, hlift⟩ :=
    LieCore.M6c.exists_finite_subfield_lift_adjoint ({c, g} : Finset (ModGL Tag.E6 L)) hS k
      (algebraMap k L)
  obtain ⟨c', hc', hcc⟩ := hlift c (Finset.mem_insert_self _ _)
  obtain ⟨g', hg', hgg⟩ := hlift g (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
  exact ⟨k', hF, hFin, κ, ι, c', g', hcomp, hc', hg', hcc, hgg⟩

theorem kgLangS1EFixedLift_core (k : Type) [Field k] [Finite k] (L : Type) [Field L] [CharP L 2]
    [Algebra k L] [Algebra.IsAlgebraic k L] {U : Type} [Group U] [Group.IsPerfect U]
    (j : U →* ↥(e6Data_valid.minGroup k)) (hj : Function.Injective j) (αU : MulAut U)
    {c g : ModGL Tag.E6 L} (hc : c ∈ adjointGroup Tag.E6 L) (hg : g ∈ adjointGroup Tag.E6 L)
    (hconj : ∀ u : U,
      baseChangeGL (τ := Tag.E6) (algebraMap k L)
          ((e6Isogeny k (j (αU u)) : ↥(adjointGroup Tag.E6 k)) : ModGL Tag.E6 k) =
        g * baseChangeGL (τ := Tag.E6) (algebraMap k L)
          ((e6Isogeny k (j u) : ↥(adjointGroup Tag.E6 k)) : ModGL Tag.E6 k) * g⁻¹)
    (hgT : c * g * c⁻¹ ∈ torusGroup Tag.E6 L) {u₀ : U}
    (hu₀ : c * baseChangeGL (τ := Tag.E6) (algebraMap k L)
        ((e6Isogeny k (j u₀) : ↥(adjointGroup Tag.E6 k)) : ModGL Tag.E6 k) * c⁻¹ ∈
      torusGroup Tag.E6 L) :
    αU u₀ = u₀ := by
  obtain ⟨k', hF, hFin, κ, ι, c', g', hcomp, hc', hg', hcc, hgg⟩ :=
    kgLangS1EFixedLift_descent k L hc hg
  have hbc : ∀ x : ↥(e6Data_valid.minGroup k),
      baseChangeGL ι ((e6Isogeny k' (minBC e6Data_valid κ x) : ↥(adjointGroup Tag.E6 k')) :
          ModGL Tag.E6 k') =
        baseChangeGL (algebraMap k L) ((e6Isogeny k x : ↥(adjointGroup Tag.E6 k)) :
          ModGL Tag.E6 k) := by
    intro x
    rw [e6Isogeny_minBC κ x, baseChangeGL_baseChangeGL, hcomp]
  refine kgLangS1EFixedLift_finiteCore κ j hj αU hc' hg' ?_ ?_ ?_
  · intro u
    apply baseChangeGL_injective ι
    rw [map_mul, map_mul, map_inv, hgg, hbc, hbc, hconj u]
  · refine kgLangS1EFixedLift_mem_torus_of_baseChange ι
      (mul_mem (mul_mem hc' hg') (inv_mem hc')) ?_
    rw [map_mul, map_mul, map_inv, hcc, hgg]
    exact hgT
  · refine kgLangS1EFixedLift_mem_torus_of_baseChange ι
      (mul_mem (mul_mem hc' (e6Isogeny k' (minBC e6Data_valid κ (j u₀))).2) (inv_mem hc')) ?_
    rw [map_mul, map_mul, map_inv, hcc, hbc]
    exact hu₀

end CFSG.StandardType

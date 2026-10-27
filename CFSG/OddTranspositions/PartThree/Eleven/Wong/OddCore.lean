module

public import CFSG.OddTranspositions.PartThree.Eleven.Wong.Hyp
public import Mathlib.GroupTheory.Commutator.Basic
import CFSG.OddTranspositions.PartThree.Eleven.Wong.Central
import CFSG.LocalAnalysis.ComponentClassification.OddCore
import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionGeometryZStarFactorization
import Mathlib.GroupTheory.FixedPointFree
import TauCeti.Algebra.Group.Subgroup.ZPowers
import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section3.Basic
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter2.Basic

public section

namespace CFSG.OddTranspositions.PartThree.Wong

open Subgroup

variable {G : Type} [Group G]

theorem mem_of_relIndex_eq_two_of_odd {K C : Subgroup G} (hidx : K.relIndex C = 2) {x : G}
    (hxC : x ∈ C) (hx : Odd (orderOf x)) : x ∈ K := by
  have h2 : (K.subgroupOf C).index = 2 := hidx
  have hsq : x ^ 2 ∈ K := by
    simpa [mem_subgroupOf] using sq_mem_of_index_two h2 ⟨x, hxC⟩
  obtain ⟨j, hj⟩ := hx
  have hx' : x = (x ^ 2) ^ (j + 1) := by
    rw [← pow_mul, show 2 * (j + 1) = orderOf x + 1 by omega, pow_succ, pow_orderOf_eq_one,
      one_mul]
  rw [hx']
  exact K.pow_mem hsq _

theorem conj_mem_of_relIndex_eq_two {K C : Subgroup G} (hKC : K ≤ C) (hidx : K.relIndex C = 2)
    {s : G} (hs : s ∈ C) {k : G} (hk : k ∈ K) : s * k * s⁻¹ ∈ K := by
  have h2 : (K.subgroupOf C).index = 2 := hidx
  have := (normal_of_index_eq_two h2).conj_mem ⟨k, hKC hk⟩ (mem_subgroupOf.mpr hk) ⟨s, hs⟩
  simpa [mem_subgroupOf] using this

theorem centralizer_sup_oddCore_eq_top [Finite G] {t : G} (ht : orderOf t = 2)
    (hiso : ∀ g : G, g⁻¹ * t * g ∈ centralizer ({t} : Set G) → g⁻¹ * t * g = t) :
    centralizer ({t} : Set G) ⊔ CFSG.oddCore G = ⊤ := by
  obtain ⟨-, hfac⟩ :=
    CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry.native_zStar_of_isolated_involution ht
      fun g hg => hiso g (mem_centralizer_singleton_iff.mpr hg.eq)
  rw [eq_top_iff]
  intro g _
  obtain ⟨c, hc, x, hx, rfl⟩ := hfac g
  exact mul_mem (mem_sup_left hc) (mem_sup_right hx)

theorem exists_conj_mem_centralizer_ne [Finite G] {t : G} (ht : orderOf t = 2)
    (hO : centralizer ({t} : Set G) ⊔ CFSG.oddCore G ≠ ⊤) :
    ∃ g : G, g⁻¹ * t * g ∈ centralizer ({t} : Set G) ∧ g⁻¹ * t * g ≠ t := by
  by_contra h
  exact hO (centralizer_sup_oddCore_eq_top ht fun g hg => not_not.mp fun hne => h ⟨g, hg, hne⟩)

end CFSG.OddTranspositions.PartThree.Wong

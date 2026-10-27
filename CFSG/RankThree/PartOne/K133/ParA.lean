module

public import CFSG.RankThree.PartOne.S13K.Pair134Basic
import CFSG.RankThree.PartOne.S10.ThetaNodesUnconditional
import CFSG.RankThree.PartOne.S10.EmbeddingFixedResidual
public import CFSG.RankThree.PartOne.S12.Sec12A

public section

namespace CFSG.RankThree.PartOne.K133

open CFSG CFSG.Assembly CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.GroupTheory
  CFSG.RankThree.PartOne CFSG.LocalAnalysis.ComponentInitial
open scoped commutatorElement

variable {G : Type} [Group G]

theorem commutator_zpowers_le_theta {p : ℕ} {E I : Subgroup G} {c : G}
    (hc : c ∈ thetaQuotientCentralizer p E I) :
    ⁅I, Subgroup.zpowers c⁆ ≤ inSubgroup (aschbacherSolvableCore p) I := by
  rw [Subgroup.commutator_le]
  intro y hy z hz
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hz
  have hcn : c ^ n ∈ thetaQuotientCentralizer p E I := Subgroup.zpow_mem _ hc n
  obtain ⟨-, -, hθ⟩ := mem_thetaQuotientCentralizer_iff.1 hcn
  have e1 : ⁅y, c ^ n⁆ = (c ^ n * y * (c ^ n)⁻¹ * y⁻¹)⁻¹ := by
    rw [commutatorElement_def]
    group
  rw [e1]
  exact (inSubgroup (aschbacherSolvableCore p) I).inv_mem (hθ y hy)

variable [Finite G]

theorem sectionTenRel_of_trivial_action (hS : SchreierFor InCatalog) {p : ℕ} {A : Subgroup G}
    {c : G} {L E : Subgroup G} (h : Sec12Hyp G p A c L E) {K : Subgroup G}
    (hKperf : Group.IsPerfect ↥K) (hK0 : K ≠ ⊥) (hKL : K ≤ L) {e : G} (he1 : e ≠ 1) (heE : e ∈ E)
    {I : Subgroup G} (hI : I ∈ thetaComponentsAt p e) (hKI : K ≤ I)
    (hKθ : K ≤ Subgroup.centralizer
      (inSubgroup (aschbacherSolvableCore p) (Subgroup.centralizer ({e} : Set G)) : Set G))
    (hc : ⁅I, Subgroup.zpowers c⁆ ≤ inSubgroup (aschbacherSolvableCore p) I) :
    sectionTenRel p I L := by
  have hp := h.prime
  have hp3 := h.three_lt
  have : IsSimpleGroup G := h.setup.1
  have hIfam : I ∈ thetaComponentFamily p E := mem_thetaComponentFamily_iff.2 ⟨e, heE, he1, hI⟩
  obtain ⟨K', hK'c, hIK'⟩ := section_ten_trivial_actor_component_supplement hS G h.setup.2.1
    h.setup.2.2.1 (sectionTenSetup_evenRank_eq h.setup).le p hp hp3 E h.E_elem c
    (h.A_le_E h.c_mem) h.c_ne_one I hIfam hc
  have hθI : inSubgroup (aschbacherSolvableCore p) I ≤
      inSubgroup (aschbacherSolvableCore p) (Subgroup.centralizer ({e} : Set G)) := by
    rw [theta_eq_inf_of_mem_thetaComponentsAt hp hI]
    exact inf_le_right
  have hKθI : K ≤ Subgroup.centralizer (inSubgroup (aschbacherSolvableCore p) I : Set G) :=
    fun x hx y hy => hKθ hx y (hθI hy)
  have hKK' : K ≤ K' := S13K.le_of_sectionTenRel hp hKperf hKI hKθI hIK'
  have hK'L : K' = L :=
    EmbeddingFixedResidual.eq_of_perfect_le_of_mem_thetaComponentsAt hp hK'c h.L_mem.2 hK0 hKperf hKK' hKL
  rw [← hK'L]
  exact hIK'

end CFSG.RankThree.PartOne.K133

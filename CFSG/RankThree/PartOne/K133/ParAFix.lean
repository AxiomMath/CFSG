module

public import CFSG.RankThree.PartOne.S13K.ThetaFixed
import CFSG.RankThree.PartOne.S10.ThetaNodesUnconditional
import CFSG.RankThree.PartOne.S10.EmbeddingFixedResidual
import CFSG.RankThree.PartOne.S10.SelectedPrimeNormalizeThetaComponents
public import CFSG.RankThree.PartOne.S12.Sec12A

public section

set_option linter.unusedSectionVars false

namespace CFSG.RankThree.PartOne.K133

open CFSG CFSG.Assembly CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.GroupTheory
  CFSG.RankThree.PartOne CFSG.LocalAnalysis.ComponentInitial
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem sectionTenRel_of_trivial_action_fix (hS : SchreierFor InCatalog) {p : ℕ} {A : Subgroup G}
    {c : G} {L E : Subgroup G} (h : Sec12Hyp G p A c L E) {K : Subgroup G}
    (hKperf : Group.IsPerfect ↥K) (hK0 : K ≠ ⊥) (hKL : K ≤ L) {e : G} (he1 : e ≠ 1) (heE : e ∈ E)
    {I : Subgroup G} (hI : I ∈ thetaComponentsAt p e) (hKI : K ≤ I) {P : Subgroup G} (hPE : P ≤ E)
    (hKP : K ≤ Subgroup.centralizer (P : Set G))
    (hKθ : K ≤ Subgroup.centralizer ((inSubgroup (aschbacherSolvableCore p)
      (Subgroup.centralizer ({e} : Set G)) ⊓ Subgroup.centralizer (P : Set G) : Subgroup G) : Set G))
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
  have hKθI : K ≤ Subgroup.centralizer ((inSubgroup (aschbacherSolvableCore p) I ⊓
      Subgroup.centralizer (P : Set G) : Subgroup G) : Set G) :=
    hKθ.trans (Subgroup.centralizer_le (inf_le_inf_right _ hθI))
  have hEI : E ≤ Subgroup.normalizer (I : Set G) :=
    h.E_normalizes_thetaComponentsAt selected_prime_elements_normalize_theta_components heE hI
  have hEK' : E ≤ Subgroup.normalizer (K' : Set G) :=
    h.E_normalizes_thetaComponentsAt selected_prime_elements_normalize_theta_components
      (h.A_le_E h.c_mem) hK'c
  have hKK' : K ≤ K' :=
    S13K.le_of_sectionTenRel_fixed hp hKperf hKI hIK' (S13K.isPGroup_of_le_elementaryAbelian h.E_elem hPE)
      (hPE.trans hEI) (hPE.trans hEK') hKP hKθI
  have hK'L : K' = L :=
    EmbeddingFixedResidual.eq_of_perfect_le_of_mem_thetaComponentsAt hp hK'c h.L_mem.2 hK0 hKperf
      hKK' hKL
  rw [← hK'L]
  exact hIK'

end CFSG.RankThree.PartOne.K133

module

import CFSG.RankThree.PartOne.S10.FiveSuccessorChoice
import CFSG.RankThree.PartOne.S10.FiveSuccessorComponent
import CFSG.RankThree.PartOne.S10.FiveSuccessorQuasisimple
import CFSG.RankThree.PartOne.S10.FiveSuccessorActor
import CFSG.RankThree.PartOne.S10.FiveSuccessorTheta
import CFSG.RankThree.PartOne.S10.SelectedPrimeNormalizeThetaComponents
import CFSG.RankThree.PartOne.S10.EmbeddingFixedResidual
public import CFSG.LocalAnalysis.ComponentInitial.KProperPumpUpStatement
public import CFSG.RankThree.GroupTheory.SteinbergCEQuotientKernelMonotonicity
public import CFSG.RankThree.PartOne.S10.Defs

public section

namespace CFSG.RankThree.PartOne

open CFSG CFSG.Assembly CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.GroupTheory
  CFSG.LocalAnalysis.ComponentInitial

theorem sectionTenRel_of_oddThetaCore_sup_le {G : Type} [Group G] {L K P : Subgroup G} {p : ℕ}
    (hP : P ≤ L ⊓ K) (hL : L = oddThetaCore p L ⊔ P) : sectionTenRel p L K := by
  refine le_antisymm ?_ (sup_le inf_le_left (Subgroup.map_subtype_le _))
  calc L = oddThetaCore p L ⊔ P := hL
    _ ≤ inSubgroup (aschbacherSolvableCore p) L ⊔ (L ⊓ K) :=
      sup_le_sup (Subgroup.map_subtype_le _) hP
    _ = (L ⊓ K) ⊔ inSubgroup (aschbacherSolvableCore p) L := sup_comm _ _

theorem not_mem_centralizer_of_not_sectionTenRel {G : Type*} [Group G] [Finite G]
    {L K P : Subgroup G} {c : G} (hKq : CFSG.IsQuasisimple K) (hPK : P ≤ K) (hPL : P ≤ L)
    (hP1 : P ≠ ⊥) (hPperf : Group.IsPerfect P)
    (hPsn : (P.subgroupOf (K ⊓ Subgroup.centralizer ({c} : Set G))).IsSubnormal)
    (hnotKL : ¬ sectionTenRel 5 K L) : c ∉ Subgroup.centralizer (K : Set G) := by
  intro hcK
  have hKC : K ⊓ Subgroup.centralizer ({c} : Set G) = K := inf_eq_left.mpr fun k hk =>
    Subgroup.mem_centralizer_singleton_iff.mpr (Subgroup.mem_centralizer_iff.mp hcK k hk)
  rw [hKC] at hPsn
  have hPK' : P = K :=
    eq_of_isSubnormal_of_isPerfect_of_isQuasisimple hKq hPK hPperf hP1 hPsn
  have hKL : K ⊓ L = K := inf_eq_left.mpr (hPK' ▸ hPL)
  refine hnotKL ?_
  rw [sectionTenRel, hKL]
  exact (sup_eq_left.mpr (Subgroup.map_subtype_le _)).symm

theorem exists_five_successor (hS : SchreierFor InCatalog) {G : Type} [Group G] [Finite G]
    {A L : Subgroup G} {c : G} {q : ℕ} {D R : Subgroup G}
    (hS10 : SteinbergBM.SectionTenSetup G 5 A)
    (hmax : ∀ Y ∈ sectionTenZero 5 A, ¬ CFSG.IsQuasisimple Y → sectionTenRel 5 L Y →
      sectionTenRel 5 Y L)
    (hcrit : FiveCriticalData A L c q D R) :
    ∃ (e : G) (K : Subgroup G), FiveSuccessorData A L c q D R e K := by
  have hp : (5 : ℕ).Prime := by norm_num
  obtain ⟨hsimple, hnonab, hKP, -, -, -, hAe, -, -, -⟩ := id hS10
  have : IsSimpleGroup G := hsimple
  have he3 : evenRank G ≤ 3 := (sectionTenSetup_evenRank_eq hS10).le
  have hcA : c ∈ A := hcrit.c_mem
  have hc1 : c ≠ 1 := hcrit.c_ne_one
  have hLc : L ∈ thetaComponentsAt 5 c := hcrit.mem_family.2
  have hAL : A ≤ Subgroup.normalizer (L : Set G) := hcrit.A_normalizes
  obtain ⟨e, heE, he1, hec, hbad⟩ := exists_five_actor_with_bad_local_residual hS10 hcrit
  have heA : e ∈ A := (inf_le_left : thetaQuotientCentralizer 5 A L ≤ A) heE
  have htriv : ∀ l ∈ L, e * l * e⁻¹ * l⁻¹ ∈ inSubgroup (aschbacherSolvableCore 5) L :=
    (((sectionTen_quotient_action_kernel 5 hAL).2 e).mp heE).2
  obtain ⟨K, hKe, hPK, hPM, hPmem⟩ :=
    exists_theta_component_containing_five_residual hS hS10 hcA hc1 heA he1 hLc hAL htriv
  have hPL : fiveResidual L e ≤ L := (Subgroup.map_subtype_le _).trans inf_le_left
  have hRP : R ≤ fiveResidual L e := hcrit.R_le_residual e heE he1
  have hLsup : L = oddThetaCore 5 L ⊔ fiveResidual L e := hcrit.residual_supplement e heE he1
  have hLK : sectionTenRel 5 L K := sectionTenRel_of_oddThetaCore_sup_le (le_inf hPL hPK) hLsup
  have hnotKL : ¬ sectionTenRel 5 K L := fun hKL => hbad (by
    rw [inSubgroup_perfectResidual_local_sup_eq hp hKe hLK hKL]
    exact hKe)
  have hKF : K ∈ thetaComponentFamily 5 A := mem_thetaComponentFamily_iff.mpr ⟨e, heA, he1, hKe⟩
  have hAK : A ≤ Subgroup.normalizer (K : Set G) :=
    selected_prime_elements_normalize_theta_components.2 G he3 5 hp (by norm_num) A hAe K hKF
  have hKZ : K ∈ sectionTenZero 5 A :=
    ⟨hKF, R, hRP.trans hPK, hcrit.R_ne_bot, hcrit.R_two, hcrit.R_invariant, hcrit.R_comm.symm⟩
  have hKq : CFSG.IsQuasisimple K := by
    by_contra hKnq
    exact hnotKL (hmax K hKZ hKnq hLK)
  have hKC : K ≤ Subgroup.centralizer ({e} : Set G) := (mem_thetaComponentsAt_iff.mp hKe).1
  have hPmem' : (fiveResidual L e).subgroupOf (K ⊓ Subgroup.centralizer ({c} : Set G)) ∈
      thetaComponents 5 ↥(K ⊓ Subgroup.centralizer ({c} : Set G)) :=
    subgroupOf_mem_thetaComponents_of_le hp (le_inf hPK (hPM.trans inf_le_right))
      (inf_le_inf_right _ hKC) hPmem
  have hEK := (solvable_prime_complement_supplement_quotient_kernel_monotonicity hp hAL hAK
    hLK).2
  have hEKeq := thetaQuotientCentralizer_eq_inf_centralizer_of_isQuasisimple hp hAK hKq
  have heCK : e ∈ Subgroup.centralizer (K : Set G) := fun k hk =>
    Subgroup.mem_centralizer_singleton_iff.mp (hKC hk)
  have hcCK : c ∉ Subgroup.centralizer (K : Set G) :=
    not_mem_centralizer_of_not_sectionTenRel hKq hPK hPL
      (fun h => hcrit.R_ne_bot (le_bot_iff.mp (h ▸ hRP)))
      (EmbeddingFixedResidual.isPerfect_inSubgroup_perfectResidual _) hPmem'.2.1 hnotKL
  have hordc : orderOf c = 5 :=
    EmbeddingFixedResidual.orderOf_eq_of_isElementaryAbelian hp hcA hc1
  have hordE : orderOf e = 5 :=
    EmbeddingFixedResidual.orderOf_eq_of_isElementaryAbelian hp heA he1
  have hAC : A ≤ Subgroup.centralizer ({e} : Set G) := fun a ha =>
    Subgroup.mem_centralizer_singleton_iff.mpr
      (congrArg Subtype.val (hAe.is_comm.comm ⟨a, ha⟩ ⟨e, heA⟩))
  have hJC : K ⊔ A ≤ Subgroup.centralizer ({e} : Set G) := sup_le hKC hAC
  have hCprop : Subgroup.centralizer ({e} : Set G) ≠ ⊤ :=
    EmbeddingFixedResidual.centralizer_ne_top_of_simple hnonab he1
  refine ⟨e, K, {
    critical := hcrit
    maximal := hmax
    e_mem := heE
    e_notMem := hec
    K_mem := ⟨hKZ, hKe⟩
    L_le_K := hLK
    not_K_le_L := hnotKL
    K_quasisimple := hKq
    R_le_P := hRP
    P_le := le_inf hPL hPK
    L_eq := hLsup
    P_mem := hPmem'
    A_normalizes_K := hAK
    E_eq := ?_
    CA_K := ?_
    c_order := ?_
    K_normal_J := ?_
    J_le := hJC
    centralizer_proper := hCprop
    J_kGroup := ?_
    J_evenRank := ?_ }⟩
  · exact eq_zpowers_sup_of_card_eq_sq hp hcrit.E_card hcrit.c_mem_E heE hordc hec
  · have hWE : A ⊓ Subgroup.centralizer (K : Set G) ≤ thetaQuotientCentralizer 5 A L := by
      rw [← hEKeq]
      exact hEK
    exact eq_zpowers_of_le_of_card_eq_sq hp hWE hcrit.E_card hcrit.c_mem_E (fun h => hcCK h.2)
      ⟨heA, heCK⟩ hordE
  · intro hc
    exact orderOf_normalizerMonoidHom_eq hp hc hordc hcCK
  · exact (Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).mpr
      (sup_le Subgroup.le_normalizer hAK)
  · exact hKP _ (lt_top_iff_ne_top.mp (lt_of_le_of_lt hJC (lt_top_iff_ne_top.mpr hCprop)))
  · exact (Sec9A.evenRank_subgroup_le _).trans he3

end CFSG.RankThree.PartOne

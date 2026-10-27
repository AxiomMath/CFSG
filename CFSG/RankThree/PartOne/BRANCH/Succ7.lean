module

public import CFSG.RankThree.PartOne.S10.FiveSuccessorConstruction
public import CFSG.RankThree.PartOne.S10.FiveSuccessorChoice
import CFSG.RankThree.PartOne.S10.FiveCriticalResidual
import CFSG.RankThree.PartOne.S10.SectionTenHyperplaneLocalResidualObstruction
import CFSG.RankThree.PartOne.S10.ThetaNodesUnconditional
import CFSG.RankThree.PartOne.S10.SelectedPrimeNormalizeThetaComponents
import CFSG.RankThree.PartOne.S10.EmbeddingFixedResidual
public import CFSG.RankThree.PartOne.S10.FiveCriticalOddCore

public section

namespace CFSG.RankThree.PartOne.BRANCH

open Subgroup CFSG CFSG.Assembly CFSG.RankThree CFSG.RankThree.LocalRank
  CFSG.RankThree.GroupTheory CFSG.RankThree.PartOne.FiveCritical
open CFSG.LocalAnalysis.ComponentInitial (SchreierFor)
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem fixed_residual_fields {p : ℕ} (hp : p.Prime) {A L : Subgroup G} {x : G}
    (hAL : A ≤ normalizer (L : Set G)) (hAe : IsElementaryAbelian p A)
    (hLperf : Group.IsPerfect L)
    (hLq : CFSG.IsQuasisimple (L ⧸ aschbacherSolvableCore p L))
    (hLO : haveI := oddThetaCore_subgroupOf_normal p L;
      CFSG.IsQuasisimple (L ⧸ (oddThetaCore p L).subgroupOf L))
    (hcomm : ⁅inSubgroup (aschbacherSolvableCore p) L, L⁆ ≤ oddThetaCore p L)
    (hxE : x ∈ thetaQuotientCentralizer p A L) (hx1 : x ≠ 1) :
    (fiveResidual L x).subgroupOf (L ⊓ centralizer ({x} : Set G)) ∈
        thetaComponents p ↥(L ⊓ centralizer ({x} : Set G)) ∧
    L = oddThetaCore p L ⊔ fiveResidual L x ∧
    (∀ R : Subgroup G, R ≤ L → IsPGroup 2 R → R ≤ centralizer ({x} : Set G) →
      R ≤ fiveResidual L x) := by
  have hxA : x ∈ A := (mem_thetaQuotientCentralizer_iff.mp hxE).1
  have hxp : orderOf x = p :=
    EmbeddingFixedResidual.orderOf_eq_of_isElementaryAbelian hp hxA hx1
  have hzE : zpowers x ≤ thetaQuotientCentralizer p A L := Subgroup.zpowers_le.mpr hxE
  have hzA : zpowers x ≤ A := hzE.trans inf_le_left
  have hUN : zpowers x ≤ normalizer (L : Set G) := hzA.trans hAL
  have hUp : IsPGroup p (zpowers x) := IsPGroup.of_card (n := 1) (by
    rw [Nat.card_zpowers, hxp]
    simp)
  have hUO : zpowers x ≤ normalizer (oddThetaCore p L : Set G) :=
    hzA.trans (le_normalizer_oddThetaCore hp hAL)
  have hUtriv : ∀ u ∈ zpowers x, ∀ l ∈ L, u * l * u⁻¹ * l⁻¹ ∈ oddThetaCore p L :=
    fun u hu l hl => five_E_trivial_mod_O hp hAL hLperf hcomm (hzE hu) l hl
  have hUtrivθ : ∀ u ∈ zpowers x, ∀ l ∈ L,
      u * l * u⁻¹ * l⁻¹ ∈ inSubgroup (aschbacherSolvableCore p) L :=
    fun u hu l hl => (((sectionTen_quotient_action_kernel p hAL).2 u).mp (hzE hu)).2 l hl
  obtain ⟨h1, h2, h3, -⟩ := odd_core_fixed_residual_ambient hp hUN hLperf hLO hUp hUO hUtriv
  have h5 := theta_component_fixed_residual_ambient hp hUN hLq hUp hUtrivθ
  have hC : centralizer ({x} : Set G) = centralizer (zpowers x : Set G) :=
    SteinbergBY.centralizer_singleton_eq_centralizer_zpowers x
  unfold fiveResidual
  rw [hC]
  exact ⟨h5, h1, fun R hRL hR2 hRC => h3 R (le_inf hRL hRC) hR2⟩

theorem exists_actor_with_bad_local_residual {A L : Subgroup G} {c : G}
    (hS10 : SteinbergBM.SectionTenSetup G 7 A) (hcA : c ∈ A) (hc1 : c ≠ 1)
    (hLZ : L ∈ thetaComponentFamily 7 A) (hLc : L ∈ thetaComponentsAt 7 c)
    (hAL : A ≤ normalizer (L : Set G))
    (hEcard : Nat.card (thetaQuotientCentralizer 7 A L) = 7 ^ 2) :
    ∃ e ∈ thetaQuotientCentralizer 7 A L, e ≠ 1 ∧ e ∉ zpowers c ∧
      inSubgroup perfectResidual ((L ⊓ centralizer ({e} : Set G)) ⊔
        inSubgroup (aschbacherSolvableCore 7) (centralizer ({e} : Set G))) ∉
          thetaComponentsAt 7 e := by
  have hp : (7 : ℕ).Prime := by norm_num
  obtain ⟨-, -, -, -, -, -, hAe, -, -, -⟩ := id hS10
  have hEA : thetaQuotientCentralizer 7 A L ≤ A := inf_le_left
  obtain ⟨e, heE, he1, hnot⟩ := section_ten_hyperplane_local_residual_obstruction G 7 A hS10 L hLZ
    (thetaQuotientCentralizer 7 A L) hEA hEcard
    (commutator_le_theta_of_thetaQuotientCentralizer 7 hAL)
  refine ⟨e, heE, he1, fun hec => hnot ?_, hnot⟩
  have hordc : orderOf c = 7 :=
    EmbeddingFixedResidual.orderOf_eq_of_isElementaryAbelian hp hcA hc1
  have hordE : orderOf e = 7 :=
    EmbeddingFixedResidual.orderOf_eq_of_isElementaryAbelian hp (hEA heE) he1
  have hzp : zpowers e = zpowers c :=
    Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hec)
      (by rw [Nat.card_zpowers, Nat.card_zpowers, hordc, hordE])
  have hcent : centralizer ({e} : Set G) = centralizer ({c} : Set G) := by
    rw [SteinbergBY.centralizer_singleton_eq_centralizer_zpowers e,
      SteinbergBY.centralizer_singleton_eq_centralizer_zpowers c, hzp]
  have hLe : L ∈ thetaComponentsAt 7 e := by
    have h : thetaComponentsAt 7 e = thetaComponentsAt 7 c := by
      unfold thetaComponentsAt
      rw [hcent]
    rw [h]
    exact hLc
  rw [inSubgroup_perfectResidual_local_sup_eq hp hLe (sectionTenRel_refl 7 L)
    (sectionTenRel_refl 7 L)]
  exact hLe

theorem exists_theta_component_containing_residual (hS : SchreierFor InCatalog) {A L : Subgroup G}
    {c e : G} (hS10 : SteinbergBM.SectionTenSetup G 7 A) (hcA : c ∈ A) (hc1 : c ≠ 1)
    (heA : e ∈ A) (he1 : e ≠ 1) (hLc : L ∈ thetaComponentsAt 7 c)
    (hAL : A ≤ normalizer (L : Set G))
    (htriv : ∀ l ∈ L, e * l * e⁻¹ * l⁻¹ ∈ inSubgroup (aschbacherSolvableCore 7) L) :
    ∃ K ∈ thetaComponentsAt 7 e, fiveResidual L e ≤ K := by
  have hp : (7 : ℕ).Prime := by norm_num
  obtain ⟨hsimple, hnonab, hKP, -, -, -, hAe, -, -, -⟩ := id hS10
  have : IsSimpleGroup G := hsimple
  have he : evenRank G ≤ 3 := (sectionTenSetup_evenRank_eq hS10).le
  have hac : c * e = e * c := congrArg Subtype.val (hAe.is_comm.comm ⟨c, hcA⟩ ⟨e, heA⟩)
  have hordc : orderOf c = 7 :=
    EmbeddingFixedResidual.orderOf_eq_of_isElementaryAbelian hp hcA hc1
  have hordE : orderOf e = 7 :=
    EmbeddingFixedResidual.orderOf_eq_of_isElementaryAbelian hp heA he1
  obtain ⟨-, P', hP', hP'eq⟩ := EmbeddingFixedResidual.fixed_residual_ambient hp hac
    ⟨1, by rw [pow_one]; exact hordE⟩ hLc (hAL heA) htriv
  have hHK : CFSG.IsKGroup (centralizer ({e} : Set G)) :=
    hKP _ (EmbeddingFixedResidual.centralizer_ne_top_of_simple hnonab he1)
  have hHE : evenRank (centralizer ({e} : Set G)) ≤ 3 :=
    (Sec9A.evenRank_subgroup_le _).trans he
  have hc'ord : orderOf (⟨c, EmbeddingFixedResidual.commute_mem_centralizer hac⟩ :
      centralizer ({e} : Set G)) = 7 := by
    rw [← Subgroup.orderOf_coe]
    exact hordc
  obtain ⟨K₀, hK₀, hPK⟩ := local_theta_component_embedding_frontier hS _ hHK hHE 7 hp
    (by norm_num) _ hc'ord P' hP'
  have hres : fiveResidual L e = P'.map (centralizer ({e} : Set G)).subtype := hP'eq.symm
  exact ⟨K₀.map (centralizer ({e} : Set G)).subtype, ⟨K₀, hK₀, rfl⟩,
    hres ▸ Subgroup.map_mono hPK⟩

theorem exists_seven_successor (hS : SchreierFor InCatalog) {A L : Subgroup G} {c : G}
    {R : Subgroup G} (hS10 : SteinbergBM.SectionTenSetup G 7 A) (hcA : c ∈ A) (hc1 : c ≠ 1)
    (hL : L ∈ sectionTenAt 7 (sectionTenZero 7 A) c)
    (hmax : ∀ Y ∈ sectionTenZero 7 A, ¬ CFSG.IsQuasisimple Y → sectionTenRel 7 L Y →
      sectionTenRel 7 Y L)
    (hEcard : Nat.card (thetaQuotientCentralizer 7 A L) = 7 ^ 2)
    (hR2 : IsPGroup 2 R) (hRL : R ≤ L) (hRinv : A ≤ normalizer (R : Set G))
    (hRcomm : ⁅R, A⁆ = R) (hRne : R ≠ ⊥)
    (hker : A ⊓ centralizer (R : Set G) = thetaQuotientCentralizer 7 A L) :
    ∃ (e : G) (K : Subgroup G), e ∈ thetaQuotientCentralizer 7 A L ∧ e ≠ 1 ∧
      K ∈ thetaComponentsAt 7 e ∧ K ∈ sectionTenZero 7 A ∧ CFSG.IsQuasisimple K ∧
      A ≤ normalizer (K : Set G) ∧ R ≤ fiveResidual L e ∧ fiveResidual L e ≤ K := by
  have hp : (7 : ℕ).Prime := by norm_num
  obtain ⟨hsimple, hnonab, hKP, -, -, -, hAe, hAcard, -, -⟩ := id hS10
  have : IsSimpleGroup G := hsimple
  have he3 : evenRank G ≤ 3 := (sectionTenSetup_evenRank_eq hS10).le
  have hvan := sectionTenSetup_vanishing hS10
  have hLfam : L ∈ thetaComponentFamily 7 A := hL.1.1
  have hLc : L ∈ thetaComponentsAt 7 c := hL.2
  have hAL : A ≤ normalizer (L : Set G) :=
    selected_prime_elements_normalize_theta_components.2 G he3 7 hp (by norm_num) A hAe L hLfam
  have hLperf : Group.IsPerfect L := isPerfect_of_mem_thetaComponentsAt hLc
  have hLq := isQuasisimple_thetaQuotient_of_mem_thetaComponentsAt hp hLc
  obtain ⟨-, -, hcomm, hOq, -⟩ :=
    moving_theta_component_quasisimplicity_reduces_to_odd_core_centralization G he3 7 hp
      (by norm_num) hvan A hAe hAcard L hL.1
  have hOn := oddThetaCore_subgroupOf_normal 7 L
  have hOq' : haveI := hOn; CFSG.IsQuasisimple (L ⧸ (oddThetaCore 7 L).subgroupOf L) := hOq
  obtain ⟨e, heE, he1, hec, hbad⟩ :=
    exists_actor_with_bad_local_residual hS10 hcA hc1 hLfam hLc hAL hEcard
  have heA : e ∈ A := (inf_le_left : thetaQuotientCentralizer 7 A L ≤ A) heE
  have htriv : ∀ l ∈ L, e * l * e⁻¹ * l⁻¹ ∈ inSubgroup (aschbacherSolvableCore 7) L :=
    (((sectionTen_quotient_action_kernel 7 hAL).2 e).mp heE).2
  obtain ⟨K, hKe, hPK⟩ :=
    exists_theta_component_containing_residual hS hS10 hcA hc1 heA he1 hLc hAL htriv
  obtain ⟨-, hLsup, hRfix⟩ := fixed_residual_fields hp hAL hAe hLperf hLq hOq' hcomm heE he1
  have hPL : fiveResidual L e ≤ L := (Subgroup.map_subtype_le _).trans inf_le_left
  have hRC : R ≤ centralizer ({e} : Set G) := by
    intro r hr
    rw [Subgroup.mem_centralizer_singleton_iff]
    have heR : e ∈ A ⊓ centralizer (R : Set G) := by
      rw [hker]
      exact heE
    exact Subgroup.mem_centralizer_iff.mp heR.2 r hr
  have hRP : R ≤ fiveResidual L e := hRfix R hRL hR2 hRC
  have hLK : sectionTenRel 7 L K := sectionTenRel_of_oddThetaCore_sup_le (le_inf hPL hPK) hLsup
  have hnotKL : ¬ sectionTenRel 7 K L := fun hKL => hbad (by
    rw [inSubgroup_perfectResidual_local_sup_eq hp hKe hLK hKL]
    exact hKe)
  have hKF : K ∈ thetaComponentFamily 7 A := mem_thetaComponentFamily_iff.mpr ⟨e, heA, he1, hKe⟩
  have hAK : A ≤ normalizer (K : Set G) :=
    selected_prime_elements_normalize_theta_components.2 G he3 7 hp (by norm_num) A hAe K hKF
  have hKZ : K ∈ sectionTenZero 7 A := ⟨hKF, R, hRP.trans hPK, hRne, hR2, hRinv, hRcomm.symm⟩
  have hKq : CFSG.IsQuasisimple K := by
    by_contra hKnq
    exact hnotKL (hmax K hKZ hKnq hLK)
  exact ⟨e, K, heE, he1, hKe, hKZ, hKq, hAK, hRP, hPK⟩

end CFSG.RankThree.PartOne.BRANCH

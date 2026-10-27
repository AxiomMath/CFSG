module

public import CFSG.RankThree.PartOne.F106.Defs
public import CFSG.RankThree.PartOne.F106.KFact
public import CFSG.RankThree.PartOne.F106.NcInvolution
public import CFSG.RankThree.PartOne.F106.NcGood
public import CFSG.RankThree.PartOne.F106.NcSuccessor
public import CFSG.RankThree.PartOne.N143.SectionListBound
import CFSG.RankThree.PartOne.F106.ZeroStar
import CFSG.RankThree.PartOne.S10.EmbeddingTransport
import CFSG.RankThree.PartOne.S10.EmbeddingFixedResidual

public section

namespace CFSG.RankThree.PartOne.F106

open Subgroup CFSG CFSG.Assembly CFSG.RankThree CFSG.RankThree.LocalRank
  CFSG.RankThree.GroupTheory CFSG.RankThree.PartOne
open CFSG.LocalAnalysis.ComponentInitial (SchreierFor)
open CFSG.RankThree.PartOne.N143 (SectionListBound)
open scoped commutatorElement

theorem noncentral_false (hS : SchreierFor InCatalog) (hTwo : TwoActionInputs)
    (hI : InSec10Seven) (hSLB : SectionListBound) (hK : KFactFive) {G : Type} [Group G]
    [Finite G] {A L : Subgroup G} {c : G} {q : ℕ} {D R : Subgroup G} {e : G} {K : Subgroup G}
    (hsucc : FiveSuccessorData A L c q D R e K)
    (hnc : ⁅thetaQuotientCentralizer 5 A L, D⁆ ≠ ⊥) : False := by
  have hp : (5 : ℕ).Prime := by norm_num
  have hcrit := hsucc.critical
  have hS10 := hcrit.setup
  obtain ⟨hsimple, hnonab, hKP, -, -, -, hAe, hAcard, -, -⟩ := id hS10
  obtain ⟨-, -, -, -, -, -, -, -, -, -, z, hzR, hz1, hz2, -, -, hzinv, -⟩ :=
    hcrit.branch_noncentral hnc
  set E := thetaQuotientCentralizer 5 A L with hE
  have hEA : E ≤ A := inf_le_left
  have hcA : c ∈ A := hcrit.c_mem
  have hc1 : c ≠ 1 := hcrit.c_ne_one
  have hLc : L ∈ thetaComponentsAt 5 c := hcrit.mem_family.2
  have hLperf : Group.IsPerfect L := isPerfect_of_mem_thetaComponentsAt hLc
  have hLC : L ≤ Subgroup.centralizer ({c} : Set G) := (mem_thetaComponentsAt_iff.mp hLc).1
  have hordc : orderOf c = 5 :=
    EmbeddingFixedResidual.orderOf_eq_of_isElementaryAbelian hp hcA hc1
  have key : ∀ x ∈ E, x ≠ 1 →
      z ∈ inSubgroup (aschbacherSolvableCore 5) (Subgroup.centralizer ({x} : Set G)) := by
    intro x hxE hx1
    have hxA : x ∈ A := hEA hxE
    have hPL : fiveResidual L x ≤ L := (Subgroup.map_subtype_le _).trans inf_le_left
    have hzP : z ∈ fiveResidual L x := hcrit.R_le_residual x hxE hx1 hzR
    have hzθ : z ∈ inSubgroup (aschbacherSolvableCore 5) (fiveResidual L x) :=
      z_mem_core_of_le hcrit hzR hz1 hz2 hzinv hPL hzP
    by_cases hxc : x ∈ Subgroup.zpowers c
    ·
      have hordx : orderOf x = 5 :=
        EmbeddingFixedResidual.orderOf_eq_of_isElementaryAbelian hp hxA hx1
      have hzp : Subgroup.zpowers x = Subgroup.zpowers c :=
        Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hxc)
          (by rw [Nat.card_zpowers, Nat.card_zpowers, hordc, hordx])
      have hcent : Subgroup.centralizer ({x} : Set G) = Subgroup.centralizer ({c} : Set G) := by
        rw [SteinbergBY.centralizer_singleton_eq_centralizer_zpowers x,
          SteinbergBY.centralizer_singleton_eq_centralizer_zpowers c, hzp]
      have hLx : L ∈ thetaComponentsAt 5 x := by
        have h : thetaComponentsAt 5 x = thetaComponentsAt 5 c := by
          unfold thetaComponentsAt
          rw [hcent]
        rw [h]
        exact hLc
      have hLCx : L ≤ Subgroup.centralizer ({x} : Set G) := hcent ▸ hLC
      have hPL' : fiveResidual L x = L := by
        unfold fiveResidual
        rw [inf_eq_left.mpr hLCx]
        exact inSubgroup_perfectResidual_of_isPerfect hLperf
      rw [hPL'] at hzθ
      rw [theta_eq_inf_of_mem_thetaComponentsAt hp hLx] at hzθ
      exact hzθ.2
    · by_cases hgood : inSubgroup perfectResidual ((L ⊓ Subgroup.centralizer ({x} : Set G)) ⊔
          inSubgroup (aschbacherSolvableCore 5) (Subgroup.centralizer ({x} : Set G))) ∈
            thetaComponentsAt 5 x
      ·
        refine core_le_of_decomposition hp hgood ?_ ?_ hzθ
        · refine EmbeddingTransport.le_inSubgroup_perfectResidual_of_isPerfect
            ((Subgroup.map_subtype_le _).trans le_sup_left)
            (EmbeddingFixedResidual.isPerfect_inSubgroup_perfectResidual _)
        · exact perfectResidual_sup_core_decomposition (inf_le_right :
            L ⊓ Subgroup.centralizer ({x} : Set G) ≤ Subgroup.centralizer ({x} : Set G))
      ·
        obtain ⟨K₁, hsucc₁⟩ :=
          exists_five_successor_at hS hS10 hsucc.maximal hcrit hxE hx1 hxc hgood
        have hK₁ : K₁ ∈ sectionTenZeroStar 5 A := successor_mem_zeroStar hS hsucc₁
        have hK₁e : K₁ ∈ thetaComponentsAt 5 x := hsucc₁.K_mem.2
        have hcK : c ∈ Subgroup.normalizer (K₁ : Set G) := hsucc₁.A_normalizes_K hcA
        have hPle : fiveResidual L x ≤ K₁ ⊓ Subgroup.centralizer ({c} : Set G) :=
          le_inf (hsucc₁.P_le.trans inf_le_right) (hPL.trans hLC)
        have hcomm := hK G K₁ c hcK hsucc₁.K_quasisimple (hI G 5 A hS10 K₁ hK₁)
          (zeroStar_quotient_list hS hTwo hSLB hS10 hK₁) (hsucc₁.c_order hcK) (fiveResidual L x)
          hPle hsucc₁.P_mem z hzθ hz2
        have hzK : z ∈ K₁ := (hsucc₁.P_le.trans inf_le_right) hzP
        have hz' : (⟨z, hzK⟩ : ↥K₁) ∈ aschbacherSolvableCore 5 ↥K₁ := by
          refine mem_aschbacherSolvableCore_of_commutator_mem hp _ ?_ fun g => ?_
          · rw [Subgroup.orderOf_mk, orderOf_eq_prime hz2 hz1]
            norm_num
          · have h : ⁅(⟨z, hzK⟩ : ↥K₁), g⁆ = 1 := by
              apply Subtype.ext
              have := hcomm (g : G) g.2
              simp [commutatorElement_def, this]
            rw [h]
            exact one_mem _
        have hzθK : z ∈ inSubgroup (aschbacherSolvableCore 5) K₁ := ⟨_, hz', rfl⟩
        rw [theta_eq_inf_of_mem_thetaComponentsAt hp hK₁e] at hzθK
        exact hzθK.2
  have hzT : z ∈ thetaT 5 E := by
    simp only [thetaT, Subgroup.mem_iInf]
    exact fun b hb hb1 => key b hb hb1
  have hEcard : Nat.card E = 5 ^ 2 := by
    rw [hcrit.E_card]
    norm_num
  obtain ⟨-, -, hodd⟩ := sectionTenSetup_vanishing hS10 A hAe hAcard E hEA hEcard c hcA hc1
  have h2 : 2 ∣ Nat.card (thetaT 5 E) := by
    have := Subgroup.orderOf_dvd_natCard (thetaT 5 E) hzT
    rwa [orderOf_eq_prime hz2 hz1] at this
  exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr h2)

theorem fiveNoncentralExcluded_of_kFactFive (hS : SchreierFor InCatalog) (hTwo : TwoActionInputs)
    (hI : InSec10Seven) (hSLB : SectionListBound) (hK : KFactFive) : FiveNoncentralExcluded :=
  fun _ _ _ _ _ _ _ _ _ _ _ hsucc hnc _ _ _ _ _ => noncentral_false hS hTwo hI hSLB hK hsucc hnc

end CFSG.RankThree.PartOne.F106

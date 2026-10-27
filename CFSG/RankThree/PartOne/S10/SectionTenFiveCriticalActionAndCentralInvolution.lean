module

public import CFSG.RankThree.PartOne.S10.ThetaContract
import CFSG.RankThree.PartOne.S10.ThetaNodesUnconditional
import CFSG.RankThree.PartOne.S10.SelectedPrimeNormalizeThetaComponents
import CFSG.RankThree.PartOne.S10.AmbientTheta
import CFSG.RankThree.PartOne.S10.FiveCriticalFixedResidual
import CFSG.RankThree.PartOne.S10.FiveCriticalFrattini
import CFSG.RankThree.PartOne.S10.FiveCriticalCentralInvolution
import CFSG.RankThree.PartOne.S10.FiveCriticalCentralBranch
import CFSG.RankThree.PartOne.S10.FiveCriticalActors
import CFSG.RankThree.PartOne.S9.OddCore.RecognitionBasic

public section

namespace CFSG.RankThree.PartOne

open Subgroup CFSG CFSG.Assembly CFSG.RankThree CFSG.RankThree.LocalRank
  CFSG.RankThree.GroupTheory FiveCritical
open scoped commutatorElement

theorem section_ten_five_critical_action_and_central_involution_of
    (hF4 : NonquasisimpleMovingThetaComponentScalarKernelHyperplane) :
    SectionTenFiveCriticalActionAndCentralInvolution := by
  intro hT G _ _ A c L hcA hc1 hS hL hnq
  have hp5 : Nat.Prime 5 := by norm_num
  have he : evenRank G ≤ 3 := (sectionTenSetup_evenRank_eq hS).le
  have hvan := sectionTenSetup_vanishing hS
  obtain ⟨-, -, -, -, -, -, hAe, hAcard, -, -⟩ := id hS
  have hLfam : L ∈ thetaComponentFamily 5 A := hL.1.1
  have hLc : L ∈ thetaComponentsAt 5 c := hL.2
  have hAL : A ≤ normalizer (L : Set G) :=
    selected_prime_elements_normalize_theta_components.2 G he 5 hp5 (by norm_num) A hAe L hLfam
  have hLperf : Group.IsPerfect L := isPerfect_of_mem_thetaComponentsAt hLc
  have hLq := isQuasisimple_thetaQuotient_of_mem_thetaComponentsAt hp5 hLc
  obtain ⟨-, -, hcomm, hOq, -⟩ :=
    moving_theta_component_quasisimplicity_reduces_to_odd_core_centralization G he 5 hp5
      (by norm_num) hvan A hAe hAcard L hL.1
  have hOn := oddThetaCore_subgroupOf_normal 5 L
  have hOq' : haveI := hOn; CFSG.IsQuasisimple (L ⧸ (oddThetaCore 5 L).subgroupOf L) := hOq
  obtain ⟨-, hrel, q, hq, hq2, hq5, D, R, hD0, hDL, hDchar, hDO, hDexp, hDcl, hR2, hRL, hAR, hRA,
    hR0, hRact, hker, hmin, hrank, hscal⟩ := hF4 hT G 5 A hS L hL.1 hnq
  have hEA : thetaQuotientCentralizer 5 A L ≤ A := inf_le_left
  have hEcard : Nat.card (thetaQuotientCentralizer 5 A L) = 25 := by
    rw [card_eq_sq_of_relIndex_eq_prime hp5 hAcard hEA hrel]
    norm_num
  have hcL : L ≤ centralizer ({c} : Set G) := (mem_thetaComponentsAt_iff.mp hLc).1
  have hcE : c ∈ thetaQuotientCentralizer 5 A L :=
    mem_thetaQuotientCentralizer_of_le_centralizer hcA hcL
  have hDn : (D.subgroupOf L).Normal := inferInstance
  have hDq : IsPGroup q D := fun g => ⟨1, Subtype.ext (by simpa using hDexp g g.2)⟩
  have hDsolv : Group.IsSolvable D := by
    have : Fact q.Prime := ⟨hq⟩
    have := hDq.isNilpotent
    infer_instance
  have hRN : R ≤ normalizer (D : Set G) :=
    hRL.trans ((Subgroup.normal_subgroupOf_iff_le_normalizer hDL).mp hDn)
  have hAD : A ≤ normalizer (D : Set G) :=
    le_normalizer_of_characteristic_subgroupOf hAL hDL hDchar
  have hres := fun x (hx : x ∈ thetaQuotientCentralizer 5 A L) (hx1 : x ≠ 1) =>
    five_fixed_residual_fields hAL hAe hLperf hLq hOq' hcomm hx hx1
  have hRC : ∀ x ∈ thetaQuotientCentralizer 5 A L, R ≤ centralizer ({x} : Set G) := by
    intro x hx r hr
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hxR : x ∈ centralizer (R : Set G) := by
      rw [← hker] at hx
      exact hx.2
    exact Subgroup.mem_centralizer_iff.mp hxR r hr
  have hRP : ∀ x ∈ thetaQuotientCentralizer 5 A L, x ≠ 1 → R ≤ fiveResidual L x :=
    fun x hx hx1 => (hres x hx hx1).2.2.2.1 R hRL hR2 (hRC x hx)
  have hEN : thetaQuotientCentralizer 5 A L ≤ normalizer (D : Set G) := hEA.trans hAD
  refine ⟨q, D, R, hDL, hRL, ?_⟩
  refine
    { setup := hS, c_mem := hcA, c_ne_one := hc1, mem_family := hL, nonquasisimple := hnq,
      A_normalizes := hAL, q_prime := hq, q_ne_two := hq2, q_ne_five := hq5, D_le_L := hDL,
      D_char := hDchar, D_ne_bot := hD0, D_le_O := hDO, D_exponent := hDexp, D_class := hDcl,
      R_two := hR2, R_le_L := hRL, R_invariant := hAR, R_comm := hRA, R_ne_bot := hR0,
      R_acts := hRact, kernel_R := hker, fixed_rank := hrank, relative_minimal := hmin,
      E_card := hEcard, c_mem_E := hcE, odd_normal := hOn, odd_quotient_quasisimple := hOq',
      E_trivial_mod_O := fun e he l hl => five_E_trivial_mod_O hp5 hAL hLperf hcomm he l hl,
      E_scalar := hscal, residual_theta := fun x hx hx1 => (hres x hx hx1).1,
      residual_supplement := fun x hx hx1 => (hres x hx hx1).2.1,
      residual_fixed := fun x hx hx1 => (hres x hx hx1).2.2.1, R_le_residual := hRP,
      branch_central := ?_, branch_noncentral := ?_, actors := ?_ }
  ·
    intro hED x hx hx1
    have hxD : D ≤ centralizer ({x} : Set G) := fun d hd => by
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact Subgroup.mem_centralizer_iff.mp
        ((Subgroup.commutator_eq_bot_iff_le_centralizer.mp hED) hx) d hd
    exact five_not_quasisimple_residual_of_centralizes hDL hDn hDsolv hxD (hRP x hx hx1) hRact
  ·
    intro hED
    have hmin' : ∀ U : Subgroup G, U < R → A ≤ normalizer (U : Set G) → ⁅U, A⁆ = U →
        U ≤ centralizer (D : Set G) := fun U h1 h2 h3 =>
      Subgroup.commutator_eq_bot_iff_le_centralizer.mp (hmin U h1 h2 h3)
    obtain ⟨-, hdisj⟩ := hT.2.1 G (sectionTenSetup_evenRank_eq hS) 5 hp5
      (sectionTenSetup_mem_sigmaA hS) (by norm_num) q hq hq2 hq5 A R D hAe hAR hR2 hRA hR0
      (sup_le hRN hAD) hDq hDexp hDcl hRact (by rw [hker]; exact hrel)
      (by rw [hker, hEcard]; norm_num) hmin' (fun h => absurd h (by norm_num))
    rcases hdisj with hcd | ⟨-, hQD, hRDtriv, hDR, hDE, hq1, hloc, hshape⟩
    · rw [hker] at hcd
      exact absurd hcd hED
    · rw [hker] at hDE
      have hrel4 : (inSubgroup frattini D).relIndex D = q ^ 4 :=
        OddCore37.isQDShape_relIndex_frattini hq hshape
      obtain ⟨hfaith, -⟩ :=
        five_faithful_and_central_involution_inverts hq hq2 hDq hRN hRDtriv hrel4 hQD
      obtain ⟨z, hzR, hz1, hz2, hzc, hzA, hzinv, hzscal⟩ :=
        exists_five_central_involution hq hq2 hDq hDexp hRN hAR hRDtriv hrel4 hQD
      have hE5 : ∀ t ∈ thetaQuotientCentralizer 5 A L, t ^ 5 = 1 := fun t ht =>
        elemPow_eq_one_of_isElementaryAbelian t (hEA ht)
      have hcD : c ∈ centralizer (D : Set G) := Subgroup.mem_centralizer_iff.mpr fun d hd =>
        Subgroup.mem_centralizer_singleton_iff.mp (hcL (hDL hd))
      obtain ⟨χ, hχscal, hχcard, hχker, hχcent⟩ := exists_frattini_scalar_character hq hq5 hDq
        hEN hE5 hEcard hrel4 hscal hcE hc1 hcD hED
      refine ⟨hq1, hloc, hQD, hRDtriv, hfaith, hDR, hDE, hshape, hrel4,
        ⟨χ, hχscal, hχcard, hχker, hχcent⟩, z, hzR, hz1, hz2, hzc, hzA, hzinv, ?_⟩
      intro x hx hx1 hxq
      obtain ⟨-, -, -, -, hcen⟩ := hres x hx hx1
      have hLD : ⁅L, D⁆ ≠ ⊥ := fun h =>
        hRact (le_bot_iff.mp (h ▸ Subgroup.commutator_mono hRL le_rfl))
      refine ⟨?_, hRP x hx hx1 hzR, ?_⟩
      · intro hxc
        apply hnq
        have hLx : L ≤ centralizer ({x} : Set G) := by
          intro l hl
          obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hxc
          rw [Subgroup.mem_centralizer_singleton_iff]
          exact (Commute.zpow_right
            (show Commute l c from Subgroup.mem_centralizer_singleton_iff.mp (hcL hl)) n).eq
        have hPL : fiveResidual L x = L := by
          unfold fiveResidual
          rw [inf_eq_left.mpr hLx]
          exact inSubgroup_perfectResidual_of_isPerfect hLperf
        rw [hPL] at hxq
        exact hxq
      · exact hcen hxq hq D hDL hDn hDq hLD z (hRP x hx hx1 hzR) hzscal
  · intro a ha haE b hb hbc
    exact five_actors hAe hEA hrel hker hAR hAD hRA ha haE hb
      (fun h => hbc (h ▸ Subgroup.one_mem _))

end CFSG.RankThree.PartOne

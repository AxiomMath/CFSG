module

public import CFSG.RankThree.PartTwo.Sec4.Item41Narrow
public import CFSG.RankThree.PartTwo.KFacts.OutFixCentralThreeProof
public import CFSG.RankThree.PartTwo.Sec4.Item422Proof
import CFSG.RankThree.PartTwo.KFacts.OutFixCentralThreeCover
import CFSG.RankThree.PartTwo.Sec4.Census.Cover46
import CFSG.RankThree.PartTwo.Sec4.Item47Native
import CFSG.RankThree.PartTwo.Sec4.Item47Kinds
import CFSG.Sporadic.ONOddCore.OuterOrder
import CFSG.RankThree.GroupTheory.ThetaQuotientTransport
import CFSG.Milestones.LC_GL_local_rank_bounds
public import CFSG.GroupTheory.LocalCores.Components
public import CFSG.RankThree.PartTwo.KFacts.OutFixCentralThree46
import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.RankThree.PartTwo.Sec4

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open Item422Proof

theorem Item41Narrow.sectionFourHyp_component (h1 : Item4_1LargePrime) {G : Type} [Group G]
    [Finite G] (hS4 : SectionFourHyp G) {K : Subgroup (G ⧸ aschbacherSolvableCore 3 G)}
    (hK : IsComponent K) : SectionFourHyp K := by
  set e := comapQuotientEquiv (aschbacherSolvableCore 3 G) K
  have hq := CFSG.LocalCores.isQuasisimple_of_mulEquiv e.symm hK.1
  exact Census.sectionFourHyp_of_mulEquiv e (Item41Narrow.sectionFourHyp_section h1 hS4 _ _
    (fun h => three_not_dvd_card_aschbacherSolvableCore
      (h.trans (Item41Narrow.card_subgroupOf_dvd _ _))) hq)

section Main

theorem rank3II_4_22_of_rank_narrow41 (h45 : Item4_5) (h1 : Item4_1LargePrime)
    (hKF : KFacts.OutFixCentralThreeAbelian46Rank) : Item4_22 := by
  refine rank3II_4_22_of_fixComm h45 fun G _ _ hS4 K L hK hL hKL => ?_
  have hrankX : CFSG.Assembly.RankThreeEven.localRank 3 (G ⧸ aschbacherSolvableCore 3 G) ≤ 3 :=
    (theta_quotient_core_and_ranks (G := G)).2.2.1.2.1.trans
      ((((CFSG.Milestones.lc_gl_local_rank_bounds G).1 3 Nat.prime_three (by norm_num)).2).trans
        hS4.evenRank_le)
  have hKcL : K ≤ Subgroup.centralizer (L : Set (G ⧸ aschbacherSolvableCore 3 G)) := by
    rcases CFSG.LocalCores.distinct_components_commute hK hL with h | h
    · exact absurd h hKL
    · exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp h
  exact hKF K (Item41Narrow.sectionFourHyp_component h1 hS4 hK) hK.1
    ((pRank_top_le_localRank_of_le_centralizer hL.1 hKcL).trans hrankX)

end Main

end CFSG.RankThree.PartTwo.Sec4

namespace CFSG.RankThree.PartTwo.KFacts

open CFSG CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4
open CFSG.ComponentClassification.OuterAutomorphisms (Outer equivalence)
open CFSG.Assembly.RankThreeEven (projSU localRank)
open CFSG.ComponentClassification.CatalogueSchreierAlternating
  (DegreeSix.outer_card_le_four_of_equiv outer_card_dvd_two_of_equiv_outside_six)
open OutFixCentralThree

namespace OutFixCentralThree

theorem fixCommInner_of_item43_narrow41
    (h1 : Item4_1LargePrime) (h2 : Item4_1ThreeCover) (h43 : Item4_3) {X : Type} [Group X]
    [Finite X] (hS4 : SectionFourHyp X) (hq : IsQuasisimple X) {z : X}
    (hz : z ∈ Subgroup.center X) (hz3 : orderOf z = 3)
    (hU : X ⧸ Subgroup.center X ≃* projSU 4 3 1 → FixCommInner X z) : FixCommInner X z := by
  have : Group.IsPerfect X := hq.1
  have h3 : 3 ∣ Nat.card (Subgroup.center X) := by
    have h := orderOf_dvd_natCard (⟨z, hz⟩ : Subgroup.center X)
    rwa [Subgroup.orderOf_mk, hz3] at h
  rcases h43 X hS4 hq h3 with ⟨p, e, _, he, hpi⟩ | hA6 | hA7 | hG2 | hU' | hM22 | hJ3 | hMcL | hON
  · exact fixCommInner_of_isoLThreePi hq hz hz3 he
      (Sec4.Census.two_or_le_two_of_isoLThreePi
        (Sec4.Item41Narrow.sectionFourHyp_quotient_center h1 h2 hS4 hq) he hpi) hpi
  · obtain ⟨fA6⟩ := hA6
    exact fixCommInner_of_card_outer_le_four fA6
      (DegreeSix.outer_card_le_four_of_equiv (MulEquiv.refl _)) z
  · obtain ⟨fA7⟩ := hA7
    have h2 := outer_card_dvd_two_of_equiv_outside_six (n := 7) (Or.inr le_rfl) (MulEquiv.refl _)
    exact fixCommInner_of_card_outer_le_four fA7
      ((Nat.le_of_dvd (by norm_num) h2).trans (by norm_num)) z
  · exact fixCommInner_of_card_outer_le_four (MulEquiv.refl _)
      (by rw [card_outer_G2_three _ hG2]; norm_num) z
  · obtain ⟨fU⟩ := hU'
    exact hU fU
  · obtain ⟨fM22⟩ := hM22
    have h2 : Nat.card (Outer Blueprint.NativeSporadic.M22) ≤ 2 :=
      Sec4.card_outer_le_two_of_card_mulAut_le CFSG.Sporadic.Schreier.m22_center_eq_bot'
        CFSG.Sporadic.Schreier.m22_mulAut_card
    exact fixCommInner_of_card_outer_le_four fM22 (h2.trans (by norm_num)) z
  · obtain ⟨fJ3⟩ := hJ3
    exact @fixCommInner_of_card_outer_le_four X _ _ Units.instGroup _ _ fJ3
      (Sec4.card_outer_J3.trans (by norm_num)) z
  · obtain ⟨fMcL⟩ := hMcL
    exact @fixCommInner_of_card_outer_le_four X _ _ Units.instGroup _ _ fMcL
      (Sec4.card_outer_McL.trans (by norm_num)) z
  · obtain ⟨fON⟩ := hON
    exact @fixCommInner_of_card_outer_le_four X _ _ Units.instGroup _ _ fON
      (Nat.le_of_dvd (by norm_num) CFSG.Sporadic.ONOddCore.r3e_on_outer_order_divides_four.1) z

end OutFixCentralThree

theorem outFixCentralThreeAbelian46Rank_of_narrow41
    (h1 : Item4_1LargePrime) (h2 : Item4_1ThreeCover) (h43 : Item4_3) :
    OutFixCentralThreeAbelian46Rank := by
  intro X _ _ hS4 hq hrk z hz hz3 σ τ hσ hτ
  exact fixCommInner_of_item43_narrow41 h1 h2 h43 hS4 hq hz hz3
    (fun f => (false_of_U43_of_pRank_le hS4 hq hrk hz hz3 f).elim) σ τ hσ hτ

theorem rank3II_4_22_of_items_narrow41
    (h45 : Item4_5) (h1 : Item4_1LargePrime) (h2 : Item4_1ThreeCover) (h43 : Item4_3) :
    Item4_22 :=
  Sec4.rank3II_4_22_of_rank_narrow41 h45 h1 (outFixCentralThreeAbelian46Rank_of_narrow41 h1 h2 h43)

end CFSG.RankThree.PartTwo.KFacts

module

public import CFSG.RankThree.PartTwo.Sec15.Gagen155BigHostDefs
public import CFSG.RankThree.PartTwo.Sec15.Sylow155E0Step
import CFSG.RankThree.PartTwo.Sec15.Sylow155F1W
import CFSG.RankThree.PartTwo.Sec15.Sylow155T52Case2
import CFSG.RankThree.PartTwo.Sec15.Gagen155BXW
import CFSG.RankThree.PartTwo.Sec15.Gagen155Y1Close
import CFSG.RankThree.PartTwo.Sec15.Gagen155Y1Chain
import CFSG.RankThree.PartTwo.Sec14.Item148Res7ProofPoint
import CFSG.RankThree.PartTwo.Sec13.Item13Sporadic
import CFSG.RankThree.PartTwo.Sec13.Item13NotSLTwo
import CFSG.RankThree.PartTwo.KFacts.KS14Orders
public import CFSG.RankThree.PartTwo.Sec15.Sylow155CD
public import CFSG.RankThree.PartTwo.Sec15.Sylow155Switch
public import CFSG.RankThree.PartTwo.Sec4.Census.Open46
public import CFSG.RankThree.PartTwo.Sec4.Item41Narrow

public section

namespace CFSG.RankThree.PartTwo.Sec15

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank CFSG.GH74.GLS

variable {G : Type} [Group G] [Finite G]

theorem step155HostE0WBig_of_y1 (h1 : Sec4.Item4_1LargePrime) (h2 : Sec4.Item4_1ThreeCover)
    (h43 : Sec4.Item4_3) (hin : Sec4.Census.CoverInputs46) (h142 : Concl142S14)
    (h1444 : Item1444S14) (h143 : Y1SecondFormExcl) {A L : Subgroup G} {c : G}
    (hR : Sec15R G A c L)
    (hW : Subgroup.normalizer (A : Set G) ≤ Subgroup.normalizer (Subgroup.zpowers c : Set G))
    (h9 : Nat.card (A ⊓ L : Subgroup G) = 9) (hcL : c ∉ L) (hres : Step155HostE0WRes1Big A c L) :
    Step155HostE0WBig A c L := by
  intro h X K Y M T P hC hXb hmax hab hE h146 hRP hIX
  have h3L : 3 ∣ Nat.card L :=
    Sec14.three_dvd_card_of_types148
      (hR.chosen136.2 c hR.zpowers_mem_omegaA L hR.mem_lA).1
  have hNL : Subgroup.normalizer (Subgroup.zpowers c : Set G) ≤
      Subgroup.normalizer (L : Set G) :=
    Sec14.Res7Point.normalizer_zpowers_le148 hR.toSec14Std hR.zpowers_mem_omegaA hR.mem_lA h3L
  have hWL : Subgroup.normalizer (A : Set G) ≤
      Subgroup.normalizer ((A ⊓ L : Subgroup G) : Set G) :=
    (le_inf le_rfl (hW.trans hNL)).trans Subgroup.inf_normalizer_le_normalizer_inf
  by_cases hres1 : Res1At A c L M
  · exact hres h X K Y M T P hC hXb hmax hab hE h146 hRP hIX hres1
  · refine Gagen155Y1.layerOddPreimage_le_of_balComp (h142 G A c L h) (h1444 G A c L h) h hC
      hE h146 hRP hIX ?_
    intro g hg hgZ hodd B hBA hfree hcon
    by_contra hcomm
    obtain ⟨hBeq, Yc, hYcomp, hcY, hYbot⟩ :=
      Gagen155Y1.eq_inf_of_not_isPConstrained h1 h2 h43 hin h143 hR hW h9 hcL hWL
        hBA hfree hcon
    subst B
    exact hres1 ⟨hBA, hfree, hcon, ⟨Yc, hYcomp, hcY, hYbot⟩, g, hg, hgZ, hodd, hcomm⟩

theorem step155HostE0WBig_of_switch (h137 : Item137) (hcl : Claim1515M12)
    (h1511 : Item1511StarR) (hpt : Step1513MeetsPoint) {A L : Subgroup G} {c : G}
    (h : Sec15R G A c L)
    (hJ : ∀ (b : G) (Lb : Subgroup G), Sec15R G A b Lb →
      Nonempty (↥Lb ⧸ aschbacherSolvableCore 3 ↥Lb ≃* CFSG.Blueprint.NativeSporadic.J2) →
      Step155HostE0WBig A b Lb)
    (hgood : ∀ (b : G) (Lb : Subgroup G), Sec15R G A b Lb →
      ¬ Sec8.IsZ3PGLThreePi (lBarA b Lb A) →
      IsEmpty (↥Lb ⧸ aschbacherSolvableCore 3 ↥Lb ≃* CFSG.Blueprint.NativeSporadic.M12) →
      Step155HostE0WBig A b Lb) :
    Step155HostE0WBig A c L := by
  intro _ X K Y M T P hC hXb hmax hab hE h146 hRP hIX
  rcases Sylow155Switch.exists_point_j2_or_good h137 hcl h1511 hpt h hC.mem_k with
    ⟨b, Lb, hb, hJb⟩ | ⟨b, Lb, hb, hPb, hMb⟩
  · exact hJ b Lb hb hJb hb.toSec14Std X K Y M T P hC hXb hmax hab hE h146 hRP hIX
  · exact hgood b Lb hb hPb hMb hb.toSec14Std X K Y M T P hC hXb hmax hab hE h146 hRP hIX

theorem step155HostE0WBig_of_t52_switch
    (h1 : Sec4.Item4_1LargePrime) (h2 : Sec4.Item4_1ThreeCover) (h43 : Sec4.Item4_3)
    (hin : Sec4.Census.CoverInputs46) (h131 : Item131) (h132 : Item132) (h134 : Item134)
    (h48 : Sec4.Item4_8) (h142 : Concl142S14) (h1444 : Item1444S14) (h137 : Item137)
    (hcl : Claim1515M12) (h1511 : Item1511StarR) (hpt : Step1513MeetsPoint)
    {A L : Subgroup G} {c : G} (h : Sec15R G A c L)
    (hJ : ∀ (b : G) (Lb : Subgroup G), Sec15R G A b Lb → (omegaA A).ncard ≤ 3 →
      Nonempty (↥Lb ⧸ aschbacherSolvableCore 3 ↥Lb ≃* CFSG.Blueprint.NativeSporadic.J2) →
      Step155HostE0WBig A b Lb)
    (hgood : ∀ (b : G) (Lb : Subgroup G), Sec15R G A b Lb → (omegaA A).ncard ≤ 9 →
      ¬ Sec8.IsZ3PGLThreePi (lBarA b Lb A) →
      IsEmpty (↥Lb ⧸ aschbacherSolvableCore 3 ↥Lb ≃* CFSG.Blueprint.NativeSporadic.M12) →
      IsEmpty (↥Lb ⧸ aschbacherSolvableCore 3 ↥Lb ≃* CFSG.Blueprint.NativeSporadic.J2) →
      Subgroup.normalizer (A : Set G) ≤ Subgroup.normalizer (Subgroup.zpowers b : Set G) →
      Step155HostE0WBig A b Lb) :
    Step155HostE0WBig A c L := by
  have hM12p : Group.IsPerfect CFSG.Blueprint.NativeSporadic.M12 :=
    (Sec13.isPerfect_center_of_isSimpleGroup CFSG.Sporadic.Mathieu.fam_m12_simplicity.2.2
      (by rw [KFacts.KS14.card_nativeM12]; norm_num)).1
  have hJ2p : Group.IsPerfect CFSG.Blueprint.NativeSporadic.J2 :=
    (Sec13.isPerfect_center_of_isSimpleGroup CFSG.Sporadic.J2.isSimpleGroup_J2
      (by rw [KFacts.KS14.card_nativeJ2]; norm_num)).1
  have hbal : ∀ {b : G} {Lb : Subgroup G}, Step155BalCompW A b Lb → Step155HostE0WBig A b Lb :=
    fun hB => step155HostE0WBig_of
      (step155HostE0W_of_hostCharSup (step155HostCharSupW_of_balComp h142 h1444 hB))
  by_cases h10 : 10 ≤ (omegaA A).ncard
  · exact step155HostE0WBig_of
      (step155HostE0W_of_hostCharSup (step155HostCharSupW_of_ten_le_ncard h142 h1444 h10))
  have h9 : (omegaA A).ncard ≤ 9 := by omega
  have hj2 : ∀ (b : G) (Lb : Subgroup G), Sec15R G A b Lb →
      Nonempty (↥Lb ⧸ aschbacherSolvableCore 3 ↥Lb ≃* CFSG.Blueprint.NativeSporadic.J2) →
      Step155HostE0WBig A b Lb := fun b Lb hb hJb => by
    by_cases h3 : (omegaA A).ncard ≤ 3
    · exact hJ b Lb hb h3 hJb
    · exact hbal (step155BalCompW_of_j2 h134 h48 hb hJb (by omega) h9)
  refine step155HostE0WBig_of_switch h137 hcl h1511 hpt h hj2 fun b Lb hb hpgl hm12 => ?_
  by_cases hJb : Nonempty (↥Lb ⧸ aschbacherSolvableCore 3 ↥Lb ≃*
      CFSG.Blueprint.NativeSporadic.J2)
  · exact hj2 b Lb hb hJb
  have hj2' := not_nonempty_iff.mp hJb
  by_cases hW : Subgroup.normalizer (A : Set G) ≤ Subgroup.normalizer (Subgroup.zpowers b : Set G)
  · exact hgood b Lb hb h9 hpgl hm12 hj2' hW
  · have hD : Sec13Data G A b Lb := hb.toSec14Std.toSec13Data
    exact hbal (step155BalCompW_of_not_le_normalizer h1 h2 h43 hin h131 h132
      Sec13.sporadicModels131 Sec13.slTwoCenter
      (Sec13.notSLTwoOfHypT_of h131 Sec13.sporadicModels131) hW hpgl
      ⟨fun ψ => hm12.false (Sec13.nonempty_thetaQuot_equiv hD hM12p ψ).some⟩
      ⟨fun ψ => hj2'.false (Sec13.nonempty_thetaQuot_equiv hD hJ2p ψ).some⟩)

theorem step155HostE0WRBig_of_t52_switch
    (h1 : Sec4.Item4_1LargePrime) (h2 : Sec4.Item4_1ThreeCover) (h43 : Sec4.Item4_3)
    (hin : Sec4.Census.CoverInputs46) (h131 : Item131) (h132 : Item132) (h134 : Item134)
    (h48 : Sec4.Item4_8) (h142 : Concl142S14) (h1444 : Item1444S14) (h137 : Item137)
    (hcl : Claim1515M12) (h1511 : Item1511StarR) (hpt : Step1513MeetsPoint)
    (hJ : RouteHostJ2SmallBig) (hgood : RouteHostGoodBig) : Step155HostE0WRBig :=
  fun G _ _ A _ _ hR => step155HostE0WBig_of_t52_switch h1 h2 h43 hin h131 h132 h134 h48 h142
    h1444 h137 hcl h1511 hpt hR (hJ G A) (hgood G A)

section Proof


theorem step155FrattiniNWPBig_of_hostE0 (hst : StellmacherKP)
    {A : Subgroup G} {c : G} {L : Subgroup G} (h134 : Item134) (h48 : Sec4.Item4_8)
    (h143 : Ronan148Q.Item143Q A (lB A)) (h146 : Item146 A (lB A)) (h148 : Item148 A (lB A))
    (h149 : Item149 A (lB A)) (hE0 : Step155HostE0WBig A c L) : Step155FrattiniNWPBig A c L :=
  fun h X K Y M T P hC hXb hmax hab hE hRP hBN =>
    have hIX : delta A (lB A) M ≤ Subgroup.normalizer (X : Set G) :=
      Sylow155T.delta_le_normalizer_x h hC hE
        (Sylow155T.card_center_le_three_of_ctx155 h h148 h134 h48 hC)
    Sylow155E0.delta_le_n155_of_cases_of_host h h134 h48 h143 h146 h148 h149 hC hE hRP hIX
      (step155BXW_of h148 h149 h X K Y M T P hC hmax hab hE)
      (Sylow155E0.delta_sup_le_n155_of_e0 hst h h146 hC hE hRP
        (hE0 h X K Y M T P hC hXb hmax hab hE h146 hRP hIX)) hBN

theorem step155FrattiniNWPRBig_of_hostE0R (hst : StellmacherKP)
    (h134 : Item134) (h48 : Sec4.Item4_8) (h143 : Ronan148Q.Item143QS14) (h146 : Item146S14)
    (h148 : Item148R) (h149 : Sec16.Item149S14) (hE0 : Step155HostE0WRBig) :
    Step155FrattiniNWPRBig := fun G _ _ A c L hR =>
  step155FrattiniNWPBig_of_hostE0 hst h134 h48 (h143 G A c L hR.toSec14Std)
    (h146 G A c L hR.toSec14Std) (h148 G A c L hR) (h149 G A c L hR.toSec14Std) (hE0 G A c L hR)

end Proof

end CFSG.RankThree.PartTwo.Sec15

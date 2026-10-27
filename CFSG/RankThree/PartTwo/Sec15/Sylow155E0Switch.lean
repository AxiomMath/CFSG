module

public import CFSG.RankThree.PartTwo.Sec15.Sylow155E0Defs
public import CFSG.RankThree.PartTwo.Sec15.Sylow155CD
import CFSG.RankThree.PartTwo.Sec15.Sylow155E0
import CFSG.RankThree.PartTwo.Sec15.Sylow155F1W
import CFSG.RankThree.PartTwo.Sec15.Sylow155T52Case2
import CFSG.RankThree.PartTwo.Sec13.Item13Sporadic
import CFSG.RankThree.PartTwo.Sec13.Item13NotSLTwo
import CFSG.RankThree.PartTwo.KFacts.KS14Orders
public import CFSG.RankThree.PartTwo.Sec15.Sylow155Switch
public import CFSG.RankThree.PartTwo.Sec4.Census.Open46
public import CFSG.RankThree.PartTwo.Sec4.Item41Narrow

public section

namespace CFSG.RankThree.PartTwo.Sec15

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank CFSG.GH74.GLS

variable {G : Type} [Group G] [Finite G]

theorem step155HostE0W_of_switch (h137 : Item137) (hcl : Claim1515M12)
    (h1511 : Item1511StarR) (hpt : Step1513MeetsPoint) {A L : Subgroup G} {c : G}
    (h : Sec15R G A c L)
    (hJ : ∀ (b : G) (Lb : Subgroup G), Sec15R G A b Lb →
      Nonempty (↥Lb ⧸ aschbacherSolvableCore 3 ↥Lb ≃* CFSG.Blueprint.NativeSporadic.J2) →
      Step155HostE0W A b Lb)
    (hgood : ∀ (b : G) (Lb : Subgroup G), Sec15R G A b Lb →
      ¬ Sec8.IsZ3PGLThreePi (lBarA b Lb A) →
      IsEmpty (↥Lb ⧸ aschbacherSolvableCore 3 ↥Lb ≃* CFSG.Blueprint.NativeSporadic.M12) →
      Step155HostE0W A b Lb) :
    Step155HostE0W A c L := by
  intro _ X K Y M T P hC hmax hab hE h146 hRP hIX
  rcases Sylow155Switch.exists_point_j2_or_good h137 hcl h1511 hpt h hC.mem_k with
    ⟨b, Lb, hb, hJb⟩ | ⟨b, Lb, hb, hPb, hMb⟩
  · exact hJ b Lb hb hJb hb.toSec14Std X K Y M T P hC hmax hab hE h146 hRP hIX
  · exact hgood b Lb hb hPb hMb hb.toSec14Std X K Y M T P hC hmax hab hE h146 hRP hIX

theorem step155HostE0W_of_t52_switch
    (h1 : Sec4.Item4_1LargePrime) (h2 : Sec4.Item4_1ThreeCover) (h43 : Sec4.Item4_3)
    (hin : Sec4.Census.CoverInputs46) (h131 : Item131) (h132 : Item132) (h134 : Item134)
    (h48 : Sec4.Item4_8) (h142 : Concl142S14) (h1444 : Item1444S14) (h137 : Item137)
    (hcl : Claim1515M12) (h1511 : Item1511StarR) (hpt : Step1513MeetsPoint)
    {A L : Subgroup G} {c : G} (h : Sec15R G A c L)
    (hJ : ∀ (b : G) (Lb : Subgroup G), Sec15R G A b Lb → (omegaA A).ncard ≤ 3 →
      Nonempty (↥Lb ⧸ aschbacherSolvableCore 3 ↥Lb ≃* CFSG.Blueprint.NativeSporadic.J2) →
      Step155HostE0W A b Lb)
    (hgood : ∀ (b : G) (Lb : Subgroup G), Sec15R G A b Lb → (omegaA A).ncard ≤ 9 →
      ¬ Sec8.IsZ3PGLThreePi (lBarA b Lb A) →
      IsEmpty (↥Lb ⧸ aschbacherSolvableCore 3 ↥Lb ≃* CFSG.Blueprint.NativeSporadic.M12) →
      IsEmpty (↥Lb ⧸ aschbacherSolvableCore 3 ↥Lb ≃* CFSG.Blueprint.NativeSporadic.J2) →
      Subgroup.normalizer (A : Set G) ≤ Subgroup.normalizer (Subgroup.zpowers b : Set G) →
      Step155HostE0W A b Lb) :
    Step155HostE0W A c L := by
  have hM12p : Group.IsPerfect CFSG.Blueprint.NativeSporadic.M12 :=
    (Sec13.isPerfect_center_of_isSimpleGroup CFSG.Sporadic.Mathieu.fam_m12_simplicity.2.2
      (by rw [KFacts.KS14.card_nativeM12]; norm_num)).1
  have hJ2p : Group.IsPerfect CFSG.Blueprint.NativeSporadic.J2 :=
    (Sec13.isPerfect_center_of_isSimpleGroup CFSG.Sporadic.J2.isSimpleGroup_J2
      (by rw [KFacts.KS14.card_nativeJ2]; norm_num)).1
  have hbal : ∀ {b : G} {Lb : Subgroup G}, Step155BalCompW A b Lb → Step155HostE0W A b Lb :=
    fun hB => step155HostE0W_of_hostCharSup (step155HostCharSupW_of_balComp h142 h1444 hB)
  by_cases h10 : 10 ≤ (omegaA A).ncard
  · exact step155HostE0W_of_hostCharSup (step155HostCharSupW_of_ten_le_ncard h142 h1444 h10)
  have h9 : (omegaA A).ncard ≤ 9 := by omega
  have hj2 : ∀ (b : G) (Lb : Subgroup G), Sec15R G A b Lb →
      Nonempty (↥Lb ⧸ aschbacherSolvableCore 3 ↥Lb ≃* CFSG.Blueprint.NativeSporadic.J2) →
      Step155HostE0W A b Lb := fun b Lb hb hJb => by
    by_cases h3 : (omegaA A).ncard ≤ 3
    · exact hJ b Lb hb h3 hJb
    · exact hbal (step155BalCompW_of_j2 h134 h48 hb hJb (by omega) h9)
  refine step155HostE0W_of_switch h137 hcl h1511 hpt h hj2 fun b Lb hb hpgl hm12 => ?_
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

theorem step155HostE0WR_of_t52_switch
    (h1 : Sec4.Item4_1LargePrime) (h2 : Sec4.Item4_1ThreeCover) (h43 : Sec4.Item4_3)
    (hin : Sec4.Census.CoverInputs46) (h131 : Item131) (h132 : Item132) (h134 : Item134)
    (h48 : Sec4.Item4_8) (h142 : Concl142S14) (h1444 : Item1444S14) (h137 : Item137)
    (hcl : Claim1515M12) (h1511 : Item1511StarR) (hpt : Step1513MeetsPoint)
    (hJ : ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (b : G) (Lb : Subgroup G),
      Sec15R G A b Lb → (omegaA A).ncard ≤ 3 →
      Nonempty (↥Lb ⧸ aschbacherSolvableCore 3 ↥Lb ≃* CFSG.Blueprint.NativeSporadic.J2) →
      Step155HostE0W A b Lb)
    (hgood : ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (b : G) (Lb : Subgroup G),
      Sec15R G A b Lb → (omegaA A).ncard ≤ 9 → ¬ Sec8.IsZ3PGLThreePi (lBarA b Lb A) →
      IsEmpty (↥Lb ⧸ aschbacherSolvableCore 3 ↥Lb ≃* CFSG.Blueprint.NativeSporadic.M12) →
      IsEmpty (↥Lb ⧸ aschbacherSolvableCore 3 ↥Lb ≃* CFSG.Blueprint.NativeSporadic.J2) →
      Subgroup.normalizer (A : Set G) ≤ Subgroup.normalizer (Subgroup.zpowers b : Set G) →
      Step155HostE0W A b Lb) :
    Step155HostE0WR :=
  fun G _ _ A _ _ hR => step155HostE0W_of_t52_switch h1 h2 h43 hin h131 h132 h134 h48 h142
    h1444 h137 hcl h1511 hpt hR (hJ G A) (hgood G A)

end CFSG.RankThree.PartTwo.Sec15

module

import CFSG.RankThree.PartTwo.Sec14.Concl142HJPoint
import CFSG.RankThree.PartTwo.Sec14.Item145BotNo135
import CFSG.RankThree.PartTwo.Sec4.Sporadic.Item415
import CFSG.RankThree.PartTwo.KFacts.KS14HJBasic
public import CFSG.RankThree.PartTwo.Sec15.Item1515StepsProofPoints

public section

namespace CFSG.RankThree.PartTwo.Sec15.Proof1523Res3

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank CFSG.GH74.GLS

variable {G : Type} [Group G] [Finite G]

theorem eq_deltaZero_of_mem_scriptY4
    (h134 : Item134) (h48 : Sec4.Item4_8) {A L : Subgroup G}
    {c : G} (h : Sec15R G A c L) {Y : Subgroup G} (hY : Y ∈ scriptY4 A (lB A)) :
    Y = deltaZero A (lB A) Y :=
  Proof1515.eq_deltaZero_of_mem_scriptY4
    (forall_exists_isHyperplane_lB_eq_bot h134 h48 Sec4.Sporadic.rank3II_4_15) h hY

theorem lA_j2_of_j2
    (h134 : Item134)
    (h48 : Sec4.Item4_8) {A L : Subgroup G} {c : G} (h : Sec15R G A c L)
    (hJ : Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* CFSG.Blueprint.NativeSporadic.J2))
    {c' : G} {L' : Subgroup G} (hc' : Subgroup.zpowers c' ∈ omegaA A) (hL' : L' ∈ lA A c') :
    Nonempty (↥L' ⧸ aschbacherSolvableCore 3 ↥L' ≃* CFSG.Blueprint.NativeSporadic.J2) := by
  have h3J : 3 ∣ Nat.card CFSG.Blueprint.NativeSporadic.J2 := by
    rw [KFacts.KS14.card_nativeJ2]
    norm_num
  obtain ⟨Le, hLe, ⟨φe⟩⟩ := allPointsHJ_of_j2 h134 h48 h.toSec14Std hJ c' hc'
  have h3e : 3 ∣ Nat.card Le :=
    Proof1515.three_dvd_card_of_thetaQuot ((Nat.card_congr φe.toEquiv).symm ▸ h3J)
  have heq := (h.chosen136.2 c' hc' L' hL').2 Le hLe.1 h3e
  rw [← heq]
  exact ⟨φe⟩

theorem card_lA_of_j2
    (h134 : Item134)
    (h48 : Sec4.Item4_8) {A L : Subgroup G} {c : G} (h : Sec15R G A c L)
    (hJ : Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* CFSG.Blueprint.NativeSporadic.J2))
    {c' : G} {L' : Subgroup G} (hc' : Subgroup.zpowers c' ∈ omegaA A) (hL' : L' ∈ lA A c') :
    Nat.card (↥L' ⧸ aschbacherSolvableCore 3 ↥L') = 604800 := by
  obtain ⟨φ⟩ := lA_j2_of_j2 h134 h48 h hJ hc' hL'
  rw [Nat.card_congr φ.toEquiv, KFacts.KS14.card_nativeJ2]

end CFSG.RankThree.PartTwo.Sec15.Proof1523Res3

module

public import CFSG.LocalAnalysis.StandardType.GGTablePThreeRank
import CFSG.LocalAnalysis.StandardType.GGTablePThreeDatum
import CFSG.LocalAnalysis.StandardType.GGTablePThreeTwoGroup
import CFSG.LocalAnalysis.StandardType.GGTablePThreeUnitaryRank
import CFSG.LocalAnalysis.StandardType.GGD4OddCentLSide
import CFSG.LocalAnalysis.StandardType.GGSixLayerCXNonsplitMarking

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

private theorem ggMarkingAll_not_of_not {X : Type*} [Group X] {S : LargeEvenLabel → Prop}
    (h : ¬ LargeEvenMarking X fun lab _ _ _ _ _ => S lab) :
    GGMarkingAll (K := X) fun lab _ _ _ _ _ => ¬ S lab := by
  intro P hP
  obtain ⟨hX, lab, hlab, hraw⟩ := hP
  by_cases hS : S lab
  · exact absurd ⟨hX, lab, hlab, largeEvenRawDatum_mono
      (fun _ _ _ _ ⟨hs, hna, θ, _⟩ => ⟨hs, hna, θ, hS⟩) hraw⟩ h
  · refine ⟨hX, lab, hlab, largeEvenRawDatum_mono ?_ hraw⟩
    rintro R _ I F ⟨hs, hna, θ, hθ⟩
    exact ⟨hs, hna, θ, hθ, hS⟩

section Unitary

theorem ggStdSubTwA2ScalarInput_of_tablePThree
    (hS : GGTablePThreeTwA2ScalarKnown)
    (hU5 : GGTablePThreeU5NoTwoGroupKnown) : GGStdSubTwA2ScalarInput := by
  intro G _ _ B x L D J hI hDJ hm hJA2 hZ
  have hst : LargeEvenStandardType 3 B x L := hI.2.2.2.2.2.2.2
  obtain ⟨hNL, δ, hdat⟩ := exists_ggTablePThree_datum hI hDJ
  have hJL : J ≤ L := le_of_stdSub_left hDJ
  have hcomm : commutator ↥L = ⊤ := hst.1.1
  have hJA2' : LargeEvenMarking ↥(J.subgroupOf L)
      (fun lab _ _ _ _ _ => GGLabelA2 lab ∧ lab.tag = .twA) :=
    GGTablePThree.largeEvenMarking_subgroupOf hJL hJA2
  have hZ' : Subgroup.center ↥(J.subgroupOf L) ≠ ⊥ := by
    intro h
    exact hZ ((GGTablePThree.center_subgroupOf_eq_bot_iff hJL).1 h)
  have hKG := hS ↥L hcomm (ggAutsOf L B hNL) δ (J.subgroupOf L) hdat hJA2' hZ'
  have hNd : GGMarkingAll (K := ↥L) fun lab _ _ _ _ _ =>
      ¬ (lab.tag = .twA ∧ lab.rank = 8 ∧ 3 ∣ 2 ^ lab.n + 1) :=
    ggMarkingAll_not_of_not (fun hM => by
      have := seven_le_twoLocalRank_of_tablePThree_twA8 hI hM
      omega)
  have hNc : GGMarkingAll (K := ↥L) fun lab _ _ _ _ _ =>
      ¬ (lab.tag = .twA ∧ lab.rank = 4 ∧ 3 ∣ 2 ^ lab.n + 1 ∧
        Nat.card ↥(ggAutsOf L B hNL) = 3 ^ 3) := by
    by_cases hAcard : Nat.card ↥(ggAutsOf L B hNL) = 3 ^ 3
    · have hnotc : ¬ LargeEvenMarking ↥L (fun lab _ _ _ _ _ =>
          lab.tag = .twA ∧ lab.rank = 4 ∧ 3 ∣ 2 ^ lab.n + 1) := by
        intro hM
        have hm4 : LargeEvenTwoLocalRank 3 G = 4 := by
          have hc := ggD4OddCent_card_lAuts hI hNL
          rw [hAcard] at hc
          have h3 : 3 = LargeEvenTwoLocalRank 3 G - 1 :=
            Nat.pow_right_injective (by norm_num : 2 ≤ 3) hc
          omega
        have hUmark : LargeEvenMarking ↥L (fun lab _ _ _ _ _ =>
            lab.tag = .twA ∧ (lab.rank = 4 ∨ lab.rank = 5) ∧ 3 ∣ 2 ^ lab.n + 1) :=
          largeEvenMarking_mono (fun lab R _ I F θ hh => ⟨hh.1, Or.inl hh.2.1, hh.2.2⟩) hM
        obtain ⟨E, hE, hEcard, hEZ⟩ := ggTablePThree_unitaryThreeRank hUmark
        have hU := ggTablePThree_twoGroup (k := 4) hI (by norm_num) hm4.le hNL hE
          (Or.inr ⟨hEcard, hEZ⟩)
        exact (hU5 ↥L hcomm (ggAutsOf L B hNL) δ (J.subgroupOf L) hdat hAcard hM hJA2' hZ') hU
      exact ggMarkingAll_mono (fun lab R _ I F θ hh hc => hh ⟨hc.1, hc.2.1, hc.2.2.1⟩)
        (ggMarkingAll_not_of_not hnotc)
    · refine fun P hP => largeEvenMarking_mono (fun lab R _ I F θ hh => ⟨hh, fun hc => ?_⟩) hP
      exact hAcard hc.2.2.2
  have hAll := ggMarkingAll_and hKG (ggMarkingAll_and hNc hNd)
  refine ggMarkingAll_mono (fun lab R _ I F θ hh hsp => ?_) hAll
  rcases hh.1 hsp with h | h | h | h
  · exact Or.inl h
  · exact Or.inr h
  · exact absurd h hh.2.1
  · exact absurd h hh.2.2

theorem ggStdSubNotA1Input_of_tablePThree
    (hA1 : GGTablePThreeA1Known)
    (hU6 : GGTablePThreeU6NoTwoGroupKnown) : GGStdSubNotA1Input := by
  intro G _ _ B x L D J hI hDJ hm hA1mark
  have hst : LargeEvenStandardType 3 B x L := hI.2.2.2.2.2.2.2
  obtain ⟨hNL, δ, hdat⟩ := exists_ggTablePThree_datum hI hDJ
  have hJL : J ≤ L := le_of_stdSub_left hDJ
  have hcomm : commutator ↥L = ⊤ := hst.1.1
  have hA1' : LargeEvenMarking ↥(J.subgroupOf L)
      (fun lab _ _ _ _ _ => lab.tag = .A ∧ lab.rank = 1) :=
    GGTablePThree.largeEvenMarking_subgroupOf hJL hA1mark
  obtain ⟨hcardA, hKG⟩ := hA1 ↥L hcomm (ggAutsOf L B hNL) δ (J.subgroupOf L) hdat hA1'
  have hm4 : LargeEvenTwoLocalRank 3 G = 4 := by
    have hc := ggD4OddCent_card_lAuts hI hNL
    rw [hcardA] at hc
    have h3 : 3 = LargeEvenTwoLocalRank 3 G - 1 :=
      Nat.pow_right_injective (by norm_num : 2 ≤ 3) hc
    omega
  have hR : LargeEvenMarking ↥L (fun lab _ _ _ _ _ =>
      (lab.tag = .A ∧ lab.rank = 5 ∧ 3 ∣ 2 ^ lab.n - 1) ∨
      (lab.tag = .twA ∧ lab.rank = 5 ∧ 3 ∣ 2 ^ lab.n + 1)) :=
    largeEvenMarking_mono (fun lab R _ I F θ hh => hh.1)
      (ggD4OddCent_lMarking hst hNL
        (fun lab => (lab.tag = .A ∧ lab.rank = 5 ∧ 3 ∣ 2 ^ lab.n - 1) ∨
          (lab.tag = .twA ∧ lab.rank = 5 ∧ 3 ∣ 2 ^ lab.n + 1)) hKG)
  rcases largeEvenMarking_or hR with hA5 | htwA5
  · exact absurd (five_le_twoLocalRank_of_tablePThree_A5 hI hA5) (by omega)
  · have hUmark : LargeEvenMarking ↥L (fun lab _ _ _ _ _ =>
        lab.tag = .twA ∧ (lab.rank = 4 ∨ lab.rank = 5) ∧ 3 ∣ 2 ^ lab.n + 1) :=
      largeEvenMarking_mono (fun lab R _ I F θ hh => ⟨hh.1, Or.inr hh.2.1, hh.2.2⟩) htwA5
    obtain ⟨E, hE, hEcard, hEZ⟩ := ggTablePThree_unitaryThreeRank hUmark
    have hU := ggTablePThree_twoGroup (k := 4) hI (by norm_num) hm4.le hNL hE
      (Or.inr ⟨hEcard, hEZ⟩)
    exact (hU6 ↥L hcomm (ggAutsOf L B hNL) δ (J.subgroupOf L) hdat hcardA htwA5 hA1') hU

end Unitary

end CFSG.StandardType

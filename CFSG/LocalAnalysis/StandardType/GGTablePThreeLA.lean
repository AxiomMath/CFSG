module

public import CFSG.LocalAnalysis.StandardType.GGTablePThreeRank
import CFSG.LocalAnalysis.StandardType.GGTablePThreeDatum
import CFSG.LocalAnalysis.StandardType.GGD4OddCentLSide
import CFSG.LocalAnalysis.StandardType.GGSixLayerCXNonsplitMarking

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

section LA

theorem ggStdSubNotG2Input_of_tablePThree (h : ∀ (X : Type) [Group X] [Finite X], commutator X = ⊤ →
    ∀ (A : Subgroup (MulAut X)) (δ : MulAut X) (J : Subgroup X), GGTablePThreeDatum A δ J → ¬
    LargeEvenMarking J (fun lab _ _ _ _ _ => GGLabelG2 lab)) : GGStdSubNotG2Input := by
  intro G _ _ B x L D J hI hDJ hG2
  have hst : LargeEvenStandardType 3 B x L := hI.2.2.2.2.2.2.2
  obtain ⟨hNL, δ, hdat⟩ := exists_ggTablePThree_datum hI hDJ
  exact h ↥L hst.1.1 (ggAutsOf L B hNL) δ (J.subgroupOf L) hdat
    (GGTablePThree.largeEvenMarking_subgroupOf (le_of_stdSub_left hDJ) hG2)

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

theorem ggStdSubA2CentreInput_of_tablePThree
    (h : GGTablePThreeA2CentrelessKnown) :
    GGStdSubA2CentreInput := by
  intro G _ _ B x L D J hI hDJ hm hA2 hZ
  have hst : LargeEvenStandardType 3 B x L := hI.2.2.2.2.2.2.2
  obtain ⟨hNL, δ, hdat⟩ := exists_ggTablePThree_datum hI hDJ
  have hJL : J ≤ L := le_of_stdSub_left hDJ
  have hA2' : LargeEvenMarking ↥(J.subgroupOf L) (fun lab _ _ _ _ _ => GGLabelA2 lab) :=
    GGTablePThree.largeEvenMarking_subgroupOf hJL hA2
  have hZ' : Subgroup.center ↥(J.subgroupOf L) = ⊥ :=
    (GGTablePThree.center_subgroupOf_eq_bot_iff hJL).2 hZ
  have hKG : GGMarkingAll (K := ↥L) fun lab _ _ _ _ _ =>
      LargeEvenSplit 3 lab →
        (lab.tag = .E6 ∧ 3 ∣ 2 ^ lab.n - 1) ∨ (lab.tag = .twE6 ∧ 3 ∣ 2 ^ lab.n + 1) ∨
          (lab.tag = .A ∧ lab.rank = 8 ∧ 3 ∣ 2 ^ lab.n - 1) ∨
          (lab.tag = .twA ∧ lab.rank = 8 ∧ 3 ∣ 2 ^ lab.n + 1) :=
    h ↥L hst.1.1 (ggAutsOf L B hNL) δ (J.subgroupOf L) hdat hA2' hZ'
  have hR : LargeEvenMarking ↥L (fun lab _ _ _ _ _ =>
      (lab.tag = .E6 ∧ 3 ∣ 2 ^ lab.n - 1) ∨
      ((lab.tag = .twE6 ∧ LargeEvenSplit 3 lab) ∨
        ((lab.tag = .A ∧ lab.rank = 8 ∧ 3 ∣ 2 ^ lab.n - 1) ∨
         (lab.tag = .twA ∧ lab.rank = 8 ∧ 3 ∣ 2 ^ lab.n + 1)))) := by
    refine largeEvenMarking_mono (fun lab R _ I F θ hh => ?_) (hKG _ hst.1)
    have hsp : LargeEvenSplit 3 lab := hh.1.1
    rcases hh.2 hsp with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Or.inl ⟨h1, h2⟩
    · exact Or.inr (Or.inl ⟨h1, hsp⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨h1, h2⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨h1, h2⟩))
  rcases largeEvenMarking_or hR with hE6 | hrest
  · exact absurd (six_le_twoLocalRank_of_tablePThree_E6 hI hE6) (by omega)
  · rcases largeEvenMarking_or hrest with htwE6 | hrest2
    · exact htwE6
    · rcases largeEvenMarking_or hrest2 with hA8 | htwA8
      · exact absurd (eight_le_twoLocalRank_of_tablePThree_A8 hI hA8) (by omega)
      · exact absurd (seven_le_twoLocalRank_of_tablePThree_twA8 hI htwA8) (by omega)

theorem ggStdSubTwA2CentreInput_of_tablePThree
    (h : GGTablePThreeA2CentrelessKnown) :
    GGStdSubTwA2CentreInput := by
  intro G _ _ B x L D J hI hDJ hm hA2 hZ
  have hst : LargeEvenStandardType 3 B x L := hI.2.2.2.2.2.2.2
  obtain ⟨hNL, δ, hdat⟩ := exists_ggTablePThree_datum hI hDJ
  have hJL : J ≤ L := le_of_stdSub_left hDJ
  have hA2' : LargeEvenMarking ↥(J.subgroupOf L) (fun lab _ _ _ _ _ => GGLabelA2 lab) :=
    GGTablePThree.largeEvenMarking_subgroupOf hJL
      (largeEvenMarking_mono (fun _ _ _ _ _ _ hh => hh.1) hA2)
  have hZ' : Subgroup.center ↥(J.subgroupOf L) = ⊥ :=
    (GGTablePThree.center_subgroupOf_eq_bot_iff hJL).2 hZ
  have hKG : GGMarkingAll (K := ↥L) fun lab _ _ _ _ _ =>
      LargeEvenSplit 3 lab →
        (lab.tag = .E6 ∧ 3 ∣ 2 ^ lab.n - 1) ∨ (lab.tag = .twE6 ∧ 3 ∣ 2 ^ lab.n + 1) ∨
          (lab.tag = .A ∧ lab.rank = 8 ∧ 3 ∣ 2 ^ lab.n - 1) ∨
          (lab.tag = .twA ∧ lab.rank = 8 ∧ 3 ∣ 2 ^ lab.n + 1) :=
    h ↥L hst.1.1 (ggAutsOf L B hNL) δ (J.subgroupOf L) hdat hA2' hZ'
  have hNa : GGMarkingAll (K := ↥L) fun lab _ _ _ _ _ =>
      ¬ (lab.tag = .E6 ∧ 3 ∣ 2 ^ lab.n - 1) :=
    ggMarkingAll_not_of_not (fun hM => by
      have := six_le_twoLocalRank_of_tablePThree_E6 hI hM
      omega)
  have hNc : GGMarkingAll (K := ↥L) fun lab _ _ _ _ _ =>
      ¬ (lab.tag = .A ∧ lab.rank = 8 ∧ 3 ∣ 2 ^ lab.n - 1) :=
    ggMarkingAll_not_of_not (fun hM => by
      have := eight_le_twoLocalRank_of_tablePThree_A8 hI hM
      omega)
  have hNd : GGMarkingAll (K := ↥L) fun lab _ _ _ _ _ =>
      ¬ (lab.tag = .twA ∧ lab.rank = 8 ∧ 3 ∣ 2 ^ lab.n + 1) :=
    ggMarkingAll_not_of_not (fun hM => by
      have := seven_le_twoLocalRank_of_tablePThree_twA8 hI hM
      omega)
  have hAll := ggMarkingAll_and hKG (ggMarkingAll_and hNa (ggMarkingAll_and hNc hNd))
  exact ggMarkingAll_mono (fun lab R _ I F θ hh => by
    intro hsp
    rcases hh.1 hsp with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact absurd ⟨h1, h2⟩ hh.2.1
    · exact h1
    · exact absurd ⟨h1, h2⟩ hh.2.2.1
    · exact absurd ⟨h1, h2⟩ hh.2.2.2) hAll

end LA

end CFSG.StandardType

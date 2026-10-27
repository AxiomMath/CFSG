module

public import CFSG.LocalAnalysis.StandardType.GGD4OddCentLSide

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

section Cases

variable {G : Type} [Group G] [Finite G] {B : Subgroup G} {x y : G} {L D J : Subgroup G}

theorem ggD4OddCent_absurd_graph (hNG2 : GGStdSubNotG2Input) (hNT : GGStdSubNotTriD4Input)
    (hP1c : GGStdSubTwA2CentreInput) (hKG7 : GGTwE6InnerDiagInput)
    (hTR : GGTwE6ThreeRankInput) (hE6 : GGTwE6LocalRankInput)
    (hI : GGThmIHyp 3 B x L) (hDJ : LargeEvenStdSub 3 B x L D J)
    (hm : LargeEvenTwoLocalRank 3 G ≤ 5) (hD : D = Subgroup.closure {x, y}) (hyB : y ∈ B)
    (hJ : LargeEvenMarking ↥J fun lab _ _ I _ θ => GGLabelG2 lab ∨ lab.tag = .triD4 ∨
      (GGLabelA2 lab ∧ lab.tag = .twA ∧ Subgroup.center ↥J = ⊥ ∧
        (LargeEvenTwoLocalRank 3 G = 5 → ¬ GGConjInducesOn B J θ I))) : False := by
  have hst := hI.2.2.2.2.2.2.2
  have hNL := le_normalizer_of_largeEvenStandardType hst
  have hS := hI.2.2.2.2.2.2.1
  have hxL : L ≤ Subgroup.centralizer ({x} : Set G) := hS.2.2.2.1.1
  have hx1 : x ≠ 1 := hS.2.2.1
  have hx3 : x ^ 3 = 1 := (hS.1.1).2 x hS.2.1
  have hm4 : 4 ≤ LargeEvenTwoLocalRank 3 G := hI.2.2.2.2.2.1.2.2.2
  rcases largeEvenMarking_or hJ with hG2 | hrest
  · exact hNG2 G B x L D J hI hDJ hG2
  rcases largeEvenMarking_or hrest with hT | hA
  · exact hNT G B x L D J hI hDJ hm (largeEvenMarking_mono (fun _ _ _ _ _ _ h => h) hT)
  obtain ⟨-, lab, R, _, I, F, θ, -, hlabA, htw, hcenter, hact⟩ := largeEvenMarking_exists' hA
  have hJA2 : LargeEvenMarking ↥J fun lab _ _ _ _ _ => GGLabelA2 lab ∧ lab.tag = .twA :=
    largeEvenMarking_mono (fun _ _ _ _ _ _ h => ⟨h.1, h.2.1⟩) hA
  have hE := hP1c G B x L D J hI hDJ hm hJA2 hcenter
  have hLE := ggD4OddCent_lMarking hst hNL (fun lab => lab.tag = .twE6) hE
  rcases (by omega : LargeEvenTwoLocalRank 3 G = 4 ∨ LargeEvenTwoLocalRank 3 G = 5) with h4 | h5
  · have := five_le_twoLocalRank_of_twE6 hE6 hxL hx1 hx3
      (largeEvenMarking_mono (fun _ _ _ _ _ _ h => ⟨h.1, h.2.1⟩) hLE)
    omega
  · have hall := ggD4OddCent_jInduce_of_twE6 hKG7 hTR hI hDJ hD hyB hNL h5
      (largeEvenMarking_mono (fun _ _ _ _ _ _ h => ⟨h.1, h.2.1, h.2.2⟩) hLE)
    obtain ⟨-, lab', R', _, I', F', θ', -, ⟨⟨-, -, -, hnot⟩, hind⟩⟩ :=
      largeEvenMarking_exists' (ggMarkingAll_apply hall hA)
    exact hnot h5 hind

theorem ggD4OddCent_absurd_field (hP2 : GGStdSubD4Input) (hLT : GGLieInnerDiagInput)
    (hKG7 : GGTwE6InnerDiagInput) (hTR : GGTwE6ThreeRankInput)
    (hI : GGThmIHyp 3 B x L) (hDJ : LargeEvenStdSub 3 B x L D J)
    (hm : LargeEvenTwoLocalRank 3 G ≤ 5) (hm5 : LargeEvenTwoLocalRank 3 G = 5)
    (hD : D = Subgroup.closure {x, y}) (hyB : y ∈ B)
    (hJ : LargeEvenMarking ↥J fun lab _ _ I _ θ => lab.tag = .D ∧ lab.rank = 4 ∧ Odd lab.n ∧
      ¬ GGConjInducesOn B J θ I) : False := by
  have hst := hI.2.2.2.2.2.2.2
  have hNL := le_normalizer_of_largeEvenStandardType hst
  have hJD : LargeEvenMarking ↥J fun lab _ _ _ _ _ => lab.tag = .D ∧ lab.rank = 4 ∧ Odd lab.n :=
    largeEvenMarking_mono (fun _ _ _ _ _ _ h => ⟨h.1, h.2.1, h.2.2.1⟩) hJ
  have hL := hP2 G B x L D J hI hDJ hm hJD
  have hLM := ggD4OddCent_lMarking hst hNL
    (fun lab => (lab.tag = .twD ∧ lab.rank = 5) ∨ lab.tag = .twE6) hL
  have hLM' : LargeEvenMarking ↥L fun lab _ _ I _ θ =>
      ((lab.tag = .twD ∧ lab.rank = 5) ∧ LargeEvenSplit 3 lab ∧
        GGInducedInn (ggAutsOf L B hNL) θ I) ∨
      (lab.tag = .twE6 ∧ LargeEvenSplit 3 lab ∧ GGInducedInn (ggAutsOf L B hNL) θ I) :=
    largeEvenMarking_mono (fun lab R _ I F θ h => by tauto) hLM
  rcases largeEvenMarking_or hLM' with hD5 | hE6
  · have hcl : LargeEvenMarking ↥L fun lab _ _ I _ θ =>
        GGLabelTwClassical lab ∧ GGInducedInn (ggAutsOf L B hNL) θ I :=
      largeEvenMarking_mono (fun lab _ _ I _ θ h => ⟨Or.inl h.1.1, h.2.2⟩) hD5
    have hall := ggD4OddCent_jInduce_of_classical hLT hI hDJ hD hyB hNL hcl
    obtain ⟨-, lab', R', _, I', F', θ', -, ⟨⟨-, -, -, hnot⟩, hind⟩⟩ :=
      largeEvenMarking_exists' (ggMarkingAll_apply hall hJ)
    exact hnot hind
  · have hall := ggD4OddCent_jInduce_of_twE6 hKG7 hTR hI hDJ hD hyB hNL hm5 hE6
    obtain ⟨-, lab', R', _, I', F', θ', -, ⟨⟨-, -, -, hnot⟩, hind⟩⟩ :=
      largeEvenMarking_exists' (ggMarkingAll_apply hall hJ)
    exact hnot hind

theorem ggD4OddCent_absurd_inner (hNA1 : GGStdSubNotA1Input) (hP1s : GGStdSubTwA2ScalarInput)
    (hLT : GGLieInnerDiagInput) (hLTs : GGLieSU3FixedInput)
    (hI : GGThmIHyp 3 B x L) (hDJ : LargeEvenStdSub 3 B x L D J)
    (hm : LargeEvenTwoLocalRank 3 G ≤ 5) (hD : D = Subgroup.closure {x, y}) (hyB : y ∈ B)
    (hJ : LargeEvenMarking ↥J fun lab _ _ I _ θ =>
      (GGLabelA2 lab ∧ lab.tag = .twA ∧ Subgroup.center ↥J ≠ ⊥ ∧
        (GGConjFixedInCenter B J ∨ ¬ GGConjInducesOn B J θ I)) ∨ (lab.tag = .A ∧ lab.rank = 1)) :
    False := by
  have hst := hI.2.2.2.2.2.2.2
  have hNL := le_normalizer_of_largeEvenStandardType hst
  rcases largeEvenMarking_or hJ with hA2 | hA1
  · obtain ⟨-, lab, R, _, I, F, θ, -, h⟩ := largeEvenMarking_exists' hA2
    have hZ : Subgroup.center ↥J ≠ ⊥ := h.2.2.1
    have hJA2 : LargeEvenMarking ↥J fun lab _ _ _ _ _ => GGLabelA2 lab ∧ lab.tag = .twA :=
      largeEvenMarking_mono (fun _ _ _ _ _ _ h => ⟨h.1, h.2.1⟩) hA2
    have hL := hP1s G B x L D J hI hDJ hm hJA2 hZ
    have hLM := ggD4OddCent_lMarking hst hNL
      (fun lab => (lab.tag = .twA ∧ lab.rank = 3) ∨
        (lab.tag = .twD ∧ (lab.rank = 3 ∨ lab.rank = 4))) hL
    have hcl : LargeEvenMarking ↥L fun lab _ _ I _ θ =>
        GGLabelTwClassical lab ∧ GGInducedInn (ggAutsOf L B hNL) θ I :=
      largeEvenMarking_mono (fun lab _ _ I _ θ h => ⟨by unfold GGLabelTwClassical; tauto, h.2.2⟩) hLM
    have hall := ggD4OddCent_jInduce_of_classical hLT hI hDJ hD hyB hNL hcl
    have hnf := ggD4OddCent_not_fixed_of_classical hLTs hI hDJ hD hyB hNL hcl hJA2 hZ
    obtain ⟨-, lab', R', _, I', F', θ', -, ⟨⟨-, -, -, hcase⟩, hind⟩⟩ :=
      largeEvenMarking_exists' (ggMarkingAll_apply hall hA2)
    rcases hcase with hfix | hnind
    · exact hnf hfix
    · exact hnind hind
  · exact hNA1 G B x L D J hI hDJ hm (largeEvenMarking_mono (fun _ _ _ _ _ _ h => h) hA1)

end Cases

end CFSG.StandardType

module

public import CFSG.LocalAnalysis.StandardType.GGD4OddCentCounting
public import CFSG.LocalAnalysis.StandardType.GGD4OddCentKLocal
public import CFSG.LocalAnalysis.StandardType.GGD4OddCentCases

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

section Glue

variable {G : Type} [Group G] [Finite G] {B : Subgroup G} {x y : G} {L D J K : Subgroup G}

theorem ggD4OddCent_false_of_graph (hNG2 : GGStdSubNotG2Input) (hNT : GGStdSubNotTriD4Input)
    (hP1c : GGStdSubTwA2CentreInput) (hKG7 : GGTwE6InnerDiagInput)
    (hTR : GGTwE6ThreeRankInput) (hE6 : GGTwE6LocalRankInput)
    (hI : GGThmIHyp 3 B x L) (hDJ : LargeEvenStdSub 3 B x L D J)
    (hm : LargeEvenTwoLocalRank 3 G ≤ 5) (hD : D = Subgroup.closure {x, y}) (hyB : y ∈ B)
    (hJK : J ≤ K) (hN : B ≤ Subgroup.normalizer (K : Set G))
    (h : LargeEvenMarking ↥(J.subgroupOf K) fun lab _ _ I _ θ' =>
      GGLabelG2 lab ∨ lab.tag = .triD4 ∨ (GGLabelA2 lab ∧ lab.tag = .twA ∧
        Subgroup.center ↥(J.subgroupOf K) = ⊥ ∧
        (LargeEvenTwoLocalRank 3 G = 5 →
          ¬ GGAutsInduceOn (ggAutsOf K B hN) (J.subgroupOf K) θ' I))) : False :=
  ggD4OddCent_absurd_graph hNG2 hNT hP1c hKG7 hTR hE6 hI hDJ hm hD hyB
    (ggD4OddCent_jMarking_of_kMarking hJK hN
      (fun lab cb ind _ => GGLabelG2 lab ∨ lab.tag = .triD4 ∨ (GGLabelA2 lab ∧ lab.tag = .twA ∧
        cb ∧ (LargeEvenTwoLocalRank 3 G = 5 → ¬ ind))) h)

theorem ggD4OddCent_false_of_field (hP2 : GGStdSubD4Input) (hLT : GGLieInnerDiagInput)
    (hKG7 : GGTwE6InnerDiagInput) (hTR : GGTwE6ThreeRankInput)
    (hI : GGThmIHyp 3 B x L) (hDJ : LargeEvenStdSub 3 B x L D J)
    (hm : LargeEvenTwoLocalRank 3 G ≤ 5) (hm5 : LargeEvenTwoLocalRank 3 G = 5)
    (hD : D = Subgroup.closure {x, y}) (hyB : y ∈ B)
    (hJK : J ≤ K) (hN : B ≤ Subgroup.normalizer (K : Set G))
    (h : LargeEvenMarking ↥(J.subgroupOf K) fun lab _ _ I _ θ' =>
      lab.tag = .D ∧ lab.rank = 4 ∧ Odd lab.n ∧
        ¬ GGAutsInduceOn (ggAutsOf K B hN) (J.subgroupOf K) θ' I) : False :=
  ggD4OddCent_absurd_field hP2 hLT hKG7 hTR hI hDJ hm hm5 hD hyB
    (ggD4OddCent_jMarking_of_kMarking hJK hN
      (fun lab _ ind _ => lab.tag = .D ∧ lab.rank = 4 ∧ Odd lab.n ∧ ¬ ind) h)

theorem ggD4OddCent_false_of_inner (hNA1 : GGStdSubNotA1Input) (hP1s : GGStdSubTwA2ScalarInput)
    (hLT : GGLieInnerDiagInput) (hLTs : GGLieSU3FixedInput)
    (hI : GGThmIHyp 3 B x L) (hDJ : LargeEvenStdSub 3 B x L D J)
    (hm : LargeEvenTwoLocalRank 3 G ≤ 5) (hD : D = Subgroup.closure {x, y}) (hyB : y ∈ B)
    (hJK : J ≤ K) (hN : B ≤ Subgroup.normalizer (K : Set G))
    (h : LargeEvenMarking ↥(J.subgroupOf K) fun lab _ _ I _ θ' =>
      (GGLabelA2 lab ∧ lab.tag = .twA ∧ Subgroup.center ↥(J.subgroupOf K) ≠ ⊥ ∧
        (GGAutsFixedInCenter (ggAutsOf K B hN) (J.subgroupOf K) ∨
          ¬ GGAutsInduceOn (ggAutsOf K B hN) (J.subgroupOf K) θ' I)) ∨
      (lab.tag = .A ∧ lab.rank = 1)) : False :=
  ggD4OddCent_absurd_inner hNA1 hP1s hLT hLTs hI hDJ hm hD hyB
    (ggD4OddCent_jMarking_of_kMarking hJK hN
      (fun lab cb ind fix => (GGLabelA2 lab ∧ lab.tag = .twA ∧ ¬ cb ∧ (fix ∨ ¬ ind)) ∨
        (lab.tag = .A ∧ lab.rank = 1)) h)

end Glue

section Main

theorem ggNbrGraphD4OddCentInput_of_known (hsub : GGNbrSubcomponentInput)
    (hG : GGD4OddCentGraphInput) (hF : GGD4OddCentFieldInput) (hInner : GGD4OddCentInnerInput)
    (hNG2 : GGStdSubNotG2Input) (hNT : GGStdSubNotTriD4Input) (hNA1 : GGStdSubNotA1Input)
    (hP1s : GGStdSubTwA2ScalarInput) (hP1c : GGStdSubTwA2CentreInput) (hP2 : GGStdSubD4Input)
    (hLT : GGLieInnerDiagInput) (hLTs : GGLieSU3FixedInput) (hKG7 : GGTwE6InnerDiagInput)
    (hTR : GGTwE6ThreeRankInput) (hE6 : GGTwE6LocalRankInput) :
    GGNbrGraphD4OddCentInput := by
  intro G _ _ B Bs x L D J hC hm y K hK hN hcent
  have hI : GGThmIHyp 3 B x L := hC.1
  have hDJ : LargeEvenStdSub 3 B x L D J := hC.2.2
  have hxB : x ∈ B := hI.2.2.2.2.2.2.1.2.1
  have hx : x ∈ Subgroup.normalizer (K : Set G) := hN (hC.2.1.1 hxB)
  have hJK : J ≤ K := hsub G 3 B x L D J hI hDJ y K hK
  have hD : D = Subgroup.closure {x, y} := hK.2.1
  have hyB : y ∈ B := hK.1.2.1
  have hm4 : 4 ≤ LargeEvenTwoLocalRank 3 G := hI.2.2.2.2.2.1.2.2.2
  intro P hP
  have hperf : commutator K = ⊤ := hP.1
  have hMG := ggMarkingAll_imp
    (GGKLocal (ggAutsOf K Bs hN) (K.normalizerMonoidHom ⟨x, hx⟩) (J.subgroupOf K) ∧
      (Nat.card ↥(ggAutsOf K Bs hN) = 3 ^ 3 ∨ Nat.card ↥(ggAutsOf K Bs hN) = 3 ^ 4))
    (fun hh => hG ↥K hperf _ _ _ hh.1 hh.2)
  have hMF := ggMarkingAll_imp
    (GGKLocal (ggAutsOf K Bs hN) (K.normalizerMonoidHom ⟨x, hx⟩) (J.subgroupOf K) ∧
      (Nat.card ↥(ggAutsOf K Bs hN) = 3 ^ 3 ∨ Nat.card ↥(ggAutsOf K Bs hN) = 3 ^ 4))
    (fun hh => hF ↥K hperf _ _ _ hh.1 hh.2)
  have hMI := ggMarkingAll_imp
    (GGKLocal (ggAutsOf K Bs hN) (K.normalizerMonoidHom ⟨x, hx⟩) (J.subgroupOf K) ∧
      (Nat.card ↥(ggAutsOf K Bs hN) = 3 ^ 3 ∨ Nat.card ↥(ggAutsOf K Bs hN) = 3 ^ 4))
    (fun hh => hInner ↥K hperf _ _ _ hh.1 hh.2)
  obtain ⟨-, lab, hlab, hraw⟩ := hMI _ (hMF _ (hMG P hP))
  by_cases hD4 : lab.tag = .D ∧ lab.rank = 4 ∧ Odd lab.n
  swap
  · refine ⟨hperf, lab, hlab, largeEvenRawDatum_mono ?_ hraw⟩
    rintro R _ I F ⟨hs, hna, θ, ⟨⟨hθP, -⟩, -⟩, -⟩
    exact ⟨hs, hna, θ, hθP, fun h1 h2 h3 => absurd ⟨h1, h2, h3⟩ hD4⟩
  obtain ⟨htag, hrank, hodd⟩ := hD4
  have hraw' := largeEvenLabelAll_d4TrialityAutRankInn htag hrank _
    (largeEvenLabelAll_d4TrialityAutRank htag hrank hlab.1 _ hraw)
  refine ⟨hperf, lab, hlab, largeEvenRawDatum_mono ?_ hraw'⟩
  rintro R _ I F ⟨⟨⟨hs, hna, θ, ⟨⟨hθP, hQG⟩, hQF⟩, hQI⟩, hAR⟩, hARI⟩
  refine ⟨hs, hna, θ, hθP, fun _ _ _ h5 h4 => ?_⟩
  by_contra hout
  obtain ⟨hBsB, hcardA, hdat⟩ := ggOddCentDatum_of_config hC hm hK hN hcent hperf θ htag hrank
    hodd hAR hARI h5 h4 hout
  have hloc := ggD4OddCent_kLocal hC hK hJK hN hcent hBsB hx
  have hcard : Nat.card ↥(ggAutsOf K Bs hN) = 3 ^ 3 ∨ Nat.card ↥(ggAutsOf K Bs hN) = 3 ^ 4 := by
    rw [hcardA]
    rcases Nat.lt_or_ge (LargeEvenTwoLocalRank 3 G) 5 with h | h
    · left
      rw [show LargeEvenTwoLocalRank 3 G = 4 by omega]
    · right
      rw [show LargeEvenTwoLocalRank 3 G = 5 by omega]
  have hσ : ggInducedAut θ (K.normalizerMonoidHom ⟨x, hx⟩) = ggLAut K θ ⟨x, hx⟩ :=
    (ggLAut_eq_ggInducedAut K θ ⟨x, hx⟩).symm
  have hxBs : x ∈ Bs := hC.2.1.1 hxB
  have hσA : K.normalizerMonoidHom ⟨x, hx⟩ ∈ ggAutsOf K Bs hN := (mem_ggAutsOf hN).2 ⟨x, hxBs, rfl⟩
  subst hBsB
  by_cases hInnF : GGInnField I F (ggLAut K θ ⟨x, hx⟩)
  · by_cases hxI : ggLAut K θ ⟨x, hx⟩ ∈ I
    ·
      exact ggD4OddCent_false_of_inner hNA1 hP1s hLT hLTs hI hDJ hm hD hyB hJK hN
        (hQI ⟨hloc, hcard⟩ hdat (by rwa [hσ]))
    ·
      have hm5 : LargeEvenTwoLocalRank 3 G = 5 := by
        rcases (by omega : LargeEvenTwoLocalRank 3 G = 4 ∨ LargeEvenTwoLocalRank 3 G = 5) with h4' | h5'
        · exfalso
          have h27 : Nat.card ↥(ggAutsOf K Bs hN) = 3 ^ 3 := by
            rw [hcardA, h4']
          exact hxI (by
            have := hdat.2.2.2.2.1 h27 _ hσA (by rwa [hσ])
            rwa [hσ] at this)
        · exact h5'
      exact ggD4OddCent_false_of_field hP2 hLT hKG7 hTR hI hDJ hm hm5 hD hyB hJK hN
        (hQF ⟨hloc, hcard⟩ hdat (by rwa [hσ]) (by rwa [hσ]))
  ·
    have hiff : LargeEvenTwoLocalRank 3 G = 5 → Nat.card ↥(ggAutsOf K Bs hN) = 3 ^ 4 := by
      intro h5'
      rw [hcardA, h5']
    refine ggD4OddCent_false_of_graph hNG2 hNT hP1c hKG7 hTR hE6 hI hDJ hm hD hyB hJK hN
      (largeEvenMarking_mono ?_ (hQG ⟨hloc, hcard⟩ hdat (by rwa [hσ])))
    rintro lab' R' _ I' F' θ' (h | h | ⟨h1, h2, h3, h4'⟩)
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr ⟨h1, h2, h3, fun h5' => h4' (hiff h5')⟩)

theorem ggNbrGraphD4OddCentInput_of_kg (hsub : GGNbrSubcomponentInput)
    (hNG2 : GGStdSubNotG2Input) (hE6 : GGTwE6LocalRankInput) (hKG : GGD4OddCentKGInputs) :
    GGNbrGraphD4OddCentInput :=
  let ⟨hG, hF, hInner, hNT, hNA1, hP1s, hP1c, hP2, hLT, hLTs, hKG7, hTR⟩ := hKG
  ggNbrGraphD4OddCentInput_of_known hsub hG hF hInner hNG2 hNT hNA1 hP1s hP1c hP2 hLT hLTs hKG7
    hTR hE6

end Main

end CFSG.StandardType

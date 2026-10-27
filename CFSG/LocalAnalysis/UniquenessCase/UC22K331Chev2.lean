module

public import CFSG.LocalAnalysis.UniquenessCase.UC22K331Fams
import CFSG.LocalAnalysis.UniquenessCase.UC22K331Chev2BT
import CFSG.LocalAnalysis.RankThreeUC.AGL81S15K21dTitsModels
import CFSG.Adapters.TauCetiLieModels
import CFSG.Milestones.ASVolI.A3Aut.SBG2
import CFSG.Milestones.ASVolI.A3Aut.SBD4
import CFSG.Milestones.ASVolI.A3Aut.SBF4
import CFSG.HardMathSupport.Cooperstein.Coordinator.FFExclusionsTwo

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.InS3

open TauCeti
open CFSG.Open (StatedLieTag StatedClassicalModel)
open CFSG.Blueprint (LieModel ChevalleyExceptionalModel)
open CFSG.LocalAnalysis.RankThreeUC.S15.K21dTitsProof (solvOver_of_lieModel)
open CFSG.QuasithinUnique.Setup.X6 (isSylowTwoOf_iff_isSylowOf)
open CFSG.HardMathSupport.Cooperstein.Coordinator
  (chevalleyExceptionalModel_trialityD4_of_lie reeTitsModel_reeF4_of_lie)

private theorem card_eq_two_iff_exponent {q : PrimePower} (hp : q.p = 2) :
    q.card = 2 ↔ q.exponent = 1 := by
  rw [PrimePower.card_def, hp]
  exact ⟨fun h => Nat.pow_right_injective le_rfl (h.trans (pow_one 2).symm),
    fun h => by rw [h, pow_one]⟩

private theorem two_le_exponent_of_card_ne {q : PrimePower} (hp : q.p = 2) (hq : q.card ≠ 2) :
    2 ≤ q.exponent := by
  have h1 := q.exponent_pos
  have h2 := mt (card_eq_two_iff_exponent hp).2 hq
  omega

theorem k331At_of_statedClassicalModel {L : Type} [Group L] [Finite L] {t : StatedLieTag}
    {m f : ℕ} (hf : 2 ≤ f) (ht : t = .PSL ∨ t = .PSp ∨ t = .PSU ∨ t = .POmegaMinus)
    (h : StatedClassicalModel L t m 2 f) : K331At L := by
  have hl : LieModel L t m 2 f := .inl ⟨by rcases ht with rfl | rfl | rfl | rfl <;> decide, h⟩
  exact k331At_of_solvBorel fun _ hT =>
    solvOver_of_lieModel hf ht hl (isSylowTwoOf_iff_isSylowOf.2 hT)

theorem k331Idx_A_even {r : ℕ} {q : PrimePower} (hv : (LieTypeIndex.A r q).Valid)
    (hp : q.p = 2) (hf : 2 ≤ q.exponent) : K331Idx (.lie ⟨.A r q, hv⟩) := by
  intro L _ _ _ _ ⟨e⟩
  have h := (CFSG.Models.lieModel_A r q hv e).2.resolve_right fun h0 => absurd h0.1 (by omega)
  rw [hp] at h
  exact k331At_of_statedClassicalModel hf (Or.inl rfl) h

theorem k331Idx_twistedA_even {r : ℕ} {q : PrimePower} (hv : (LieTypeIndex.twistedA r q).Valid)
    (hp : q.p = 2) (hf : 2 ≤ q.exponent) : K331Idx (.lie ⟨.twistedA r q, hv⟩) := by
  intro L _ _ _ _ ⟨e⟩
  have h := (CFSG.Models.lieModel_twistedA r q hv e).2.resolve_right fun h0 =>
    absurd h0.1 (by omega)
  have hc : ValidLieTypeIndex.characteristic ⟨.twistedA r q, hv⟩ = 2 :=
    (LieTypeIndex.characteristic_twistedA r q).trans hp
  have he : ValidLieTypeIndex.fieldExponent ⟨.twistedA r q, hv⟩ = q.exponent :=
    LieTypeIndex.fieldExponent_twistedA r q
  rw [hc, he] at h
  exact k331At_of_statedClassicalModel hf (Or.inr (Or.inr (Or.inl rfl))) h

theorem k331Idx_B_even {r : ℕ} {q : PrimePower} (hv : (LieTypeIndex.B r q).Valid)
    (hp : q.p = 2) (hf : 2 ≤ q.exponent) : K331Idx (.lie ⟨.B r q, hv⟩) := by
  intro L _ _ _ _ ⟨e⟩
  have hr : 2 ≤ r := ((LieTypeIndex.inStandardRange_iff _).1 ((LieTypeIndex.valid_iff _).1 hv).1).1
  rcases CFSG.Models.lieModel_B r q hv e with h | h
  · have hs := h.2.resolve_right fun h0 => absurd h0.1 (by omega)
    rw [hp] at hs
    exact k331At_of_statedClassicalModel hf (Or.inr (Or.inl rfl)) hs
  · exact absurd hp h.1.2.2.2

section Certified


set_option linter.unusedSectionVars false

theorem k331Idx_G2_even {q : PrimePower} (hv : (LieTypeIndex.G2 q).Valid) (hp : q.p = 2) :
    K331Idx (.lie ⟨.G2 q, hv⟩) := by
  intro L _ _ _ _ ⟨e⟩
  have : Fact q.p.Prime := ⟨q.prime_p⟩
  have hq3 : 3 ≤ q.card :=
    (LieTypeIndex.inStandardRange_iff _).1 ((LieTypeIndex.valid_iff _).1 hv).1
  have hK : Nat.card (GaloisField q.p q.exponent) = q.card := by
    rw [GaloisField.card _ _ q.exponent_pos.ne', PrimePower.card_def]
  obtain ⟨e0⟩ := CFSG.TauCetiBridge.Even.untwistedBridgeEven_G2 q hv hp
    (GaloisField q.p q.exponent) hK
  have h : ChevalleyExceptionalModel L .G2 q.p q.exponent := by
    refine ⟨⟨q.prime_p, q.exponent_pos, rfl, ?_⟩, GaloisField q.p q.exponent, inferInstance,
      inferInstance, ?_, ⟨e.trans e0.symm⟩⟩
    · rw [← PrimePower.card_def]
      exact hq3
    · rw [hK, PrimePower.card_def]
  rw [hp] at h
  exact k331At_of_solvBorel fun T hT => CFSG.ASVolI.burnsideAut_solvBorel_G2 L q.exponent
    (two_le_exponent_of_card_ne hp (by omega)) h T (isSylowTwoOf_iff_isSylowOf.2 hT)

section Ree


theorem k331Idx_reeF4 {m : ℕ} (hv : (LieTypeIndex.reeF4 m).Valid) :
    K331Idx (.lie ⟨.reeF4 m, hv⟩) := by
  intro L _ _ _ _ ⟨e⟩
  have hm : 1 ≤ m := (LieTypeIndex.inStandardRange_iff _).1 ((LieTypeIndex.valid_iff _).1 hv).1
  exact k331At_of_solvBorel fun T hT => CFSG.ASVolI.burnsideAut_solvBorel_2F4 L (2 * m + 1)
    ⟨m, rfl⟩ (by omega) (reeTitsModel_reeF4_of_lie hv e) T (isSylowTwoOf_iff_isSylowOf.2 hT)

end Ree


theorem k331Idx_trialityD4_even {q : PrimePower} (hv : (LieTypeIndex.trialityD4 q).Valid)
    (hp : q.p = 2) : K331Idx (.lie ⟨.trialityD4 q, hv⟩) := by
  intro L _ _ _ _ ⟨e⟩
  have h := chevalleyExceptionalModel_trialityD4_of_lie hv hp e
  by_cases hq : q.card = 2
  · rw [(card_eq_two_iff_exponent hp).1 hq] at h
    have hL : Nat.card L = CFSG.Open.ordTrialityD4 (2 ^ 1) :=
      CFSG.Timmesfeld.card_chevalleyExceptionalModel_two h
    exact k331At_of_card (Or.inl (by rw [hL]; decide))
  · exact k331At_of_solvBorel fun T hT => CFSG.ASVolI.burnsideAut_solvBorel_3D4 L q.exponent
      (two_le_exponent_of_card_ne hp hq) h T (isSylowTwoOf_iff_isSylowOf.2 hT)


theorem k331_chev2 : K331Fam K331Chev2 := by
  intro i hi
  rcases i with ⟨p, hp⟩ | ⟨n, hn⟩ | ⟨⟨d, hv⟩⟩ | s
  · exact False.elim hi
  · exact False.elim hi
  · cases d with
    | A r q =>
      obtain ⟨hp, hr, -, hc⟩ := hi
      refine k331Idx_A_even hv hp (two_le_exponent_of_card_ne hp fun h2 => ?_)
      rcases hr with rfl | rfl
      · exact ((LieTypeIndex.valid_iff _).1 hv).2
          ((LieTypeIndex.isDuplicateRepresentative_iff _).2 (Or.inr (Or.inr ⟨rfl, h2⟩)))
      · exact hc ⟨rfl, h2⟩
    | twistedA r q =>
      obtain ⟨hp, -, hc⟩ := hi
      exact k331Idx_twistedA_even hv hp (two_le_exponent_of_card_ne hp fun h2 => by omega)
    | B r q =>
      obtain ⟨rfl, hp⟩ := hi
      exact k331Idx_B_even hv hp (two_le_exponent_of_card_ne hp fun h2 =>
        ((LieTypeIndex.inStandardRange_iff _).1 ((LieTypeIndex.valid_iff _).1 hv).1).2 ⟨rfl, h2⟩)
    | G2 q => exact k331Idx_G2_even hv hi
    | trialityD4 q => exact k331Idx_trialityD4_even hv hi
    | reeF4 m => exact k331Idx_reeF4 hv
    | _ => exact False.elim hi
  · exact False.elim hi

end Certified

end CFSG.LocalAnalysis.UniquenessCase.UC22.InS3

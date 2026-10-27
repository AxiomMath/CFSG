module

public import CFSG.LocalAnalysis.UniquenessCase.UC22K331Basic
public import CFSG.LieType.SeitzGeneration.Defs
import CFSG.LocalAnalysis.UniquenessCase.UC22K331NonLie
import CFSG.LocalAnalysis.UniquenessCase.UC22K331RankCl
import CFSG.LocalAnalysis.UniquenessCase.UC22K331RankExc

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.InS3

open TauCeti
open CFSG.Blueprint.NativeSporadic (Carrier)
open CFSG.Blueprint.Chevalley (Tag)
open CFSG.Blueprint (AdjointQuotient)
open CFSG.TauCetiBridge.Even (ChevalleyBridgesAll)
open CFSG.LieType.SeitzGeneration (Cat)
open CFSG.SectionRank (SporadicThreeRankWitnesses)
open CFSG.Open (IsElemAbelian)

@[expose] def K331RankGap : CFSGIndex → Prop
  | .lie ⟨.twistedE6 _, _⟩ => True
  | .lie ⟨.twistedA r q, _⟩ => 5 ≤ r ∧ q.card % 3 = 1
  | _ => False

@[expose] def K331ClassicalLow : CFSGIndex → Prop
  | .lie ⟨.A r q, _⟩ => r = 1 ∨ (q.p ≠ 2 ∧ (r = 2 ∨ ((r = 3 ∨ r = 4) ∧ q.card % 3 = 2)))
  | .lie ⟨.twistedA r q, _⟩ => q.p ≠ 2 ∧ (r = 2 ∨ ((r = 3 ∨ r = 4) ∧ q.card % 3 = 1))
  | .lie ⟨.B r q, _⟩ => r = 2 ∧ q.p ≠ 2
  | _ => False

@[expose] def K331L3Even : CFSGIndex → Prop
  | .lie ⟨.A r q, _⟩ => r = 2 ∧ q.p = 2
  | .lie ⟨.twistedA r q, _⟩ => r = 2 ∧ q.p = 2
  | _ => False

@[expose] def K331G2Odd : CFSGIndex → Prop
  | .lie ⟨.G2 q, _⟩ => q.p ≠ 2
  | _ => False

@[expose] def K331D4Odd : CFSGIndex → Prop
  | .lie ⟨.trialityD4 q, _⟩ => q.p ≠ 2
  | _ => False

@[expose] def K331Chev2 : CFSGIndex → Prop
  | .lie ⟨.A r q, _⟩ => q.p = 2 ∧ (r = 3 ∨ r = 4) ∧ q.card % 3 = 2 ∧ ¬ (r = 4 ∧ q.card = 2)
  | .lie ⟨.twistedA r q, _⟩ => q.p = 2 ∧ (r = 3 ∨ r = 4) ∧ q.card % 3 = 1
  | .lie ⟨.B r q, _⟩ => r = 2 ∧ q.p = 2
  | .lie ⟨.G2 q, _⟩ => q.p = 2
  | .lie ⟨.trialityD4 q, _⟩ => q.p = 2
  | .lie ⟨.reeF4 _, _⟩ => True
  | _ => False

@[expose] def K331SporSmall : CFSGIndex → Prop
  | .sporadic s => s = .J2 ∨ s = .M22 ∨ s = .M23 ∨ s = .HS
  | _ => False

@[expose] def K331HeRu : CFSGIndex → Prop
  | .sporadic s => s = .He ∨ s = .Ru
  | _ => False

structure K331Inputs : Prop where
  bridge : ∀ s : SporadicName, Nonempty (Carrier s ≃* s.Group)
  card_M11 : Nat.card (Carrier .M11) = 7920
  card_M12 : Nat.card (Carrier .M12) = 2 ^ 6 * 3 ^ 3 * 5 * 11
  card_J1 : Nat.card (Carrier .J1) = 2 ^ 3 * 3 * 5 * 7 * 11 * 19
  witness : SporadicThreeRankWitnesses
  monster : Nontrivial (Carrier .M) →
    ∃ E : Subgroup (Carrier .M), IsElemAbelian 3 E ∧ Nat.card E = 3 ^ 4
  chevalley : ChevalleyBridgesAll
  adjoint : ∀ τ : Tag, (τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) →
    ∀ (K : Type) [Field K] [Finite K] (S : Type) [Group S] [Finite S],
      Nonempty (S ≃* AdjointQuotient τ K) → 3 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup S)
  ree : ∀ (m : ℕ) (hv : (LieTypeIndex.reeG2 m).Valid) (S : Type) [Group S] [Finite S],
    Nonempty (S ≃* Cat ⟨.reeG2 m, hv⟩) → 3 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup S)
  suzuki : ∀ (m : ℕ) (hv : (LieTypeIndex.suzuki m).Valid),
    Nat.Coprime 3 (Nat.card (Cat ⟨.suzuki m, hv⟩))
  tits : ∀ hv : LieTypeIndex.tits.Valid, Nat.card (Cat ⟨.tits, hv⟩) = 17971200
  rankGap : K331Fam K331RankGap
  classicalLow : K331Fam K331ClassicalLow
  l3Even : K331Fam K331L3Even
  g2Odd : K331Fam K331G2Odd
  d4Odd : K331Fam K331D4Odd
  heRu : K331Fam K331HeRu

theorem k331Idx_dispatch (hI : K331Inputs) (i : CFSGIndex)
    (hRG : K331RankGap i → K331Idx i) (hCL : K331ClassicalLow i → K331Idx i)
    (hL3 : K331L3Even i → K331Idx i) (hG2 : K331G2Odd i → K331Idx i)
    (hD4 : K331D4Odd i → K331Idx i) (hC2 : K331Chev2 i → K331Idx i)
    (hSS : K331SporSmall i → K331Idx i) (hHR : K331HeRu i → K331Idx i) : K331Idx i := by
  rcases i with ⟨p, hp⟩ | ⟨n, hn⟩ | ⟨⟨d, hv⟩⟩ | s
  · exact k331Idx_cyclic p hp
  · exact k331Idx_alternating n hn
  · have hr := (LieTypeIndex.inStandardRange_iff _).mp ((LieTypeIndex.valid_iff _).mp hv).1
    cases d with
    | A r q =>
      have hr1 : 1 ≤ r := hr.1
      by_cases h5 : 5 ≤ r
      · exact k331Idx_A hv (by omega) (Or.inl h5)
      by_cases h34 : (r = 3 ∨ r = 4) ∧ q.card % 3 = 2
      · by_cases hL : r = 4 ∧ q.card = 2
        · obtain ⟨rfl, hq⟩ := hL
          exact k331Idx_A_four_two hv hq
        · by_cases hq2 : q.p = 2
          · exact hC2 (by simp only [K331Chev2]; omega)
          · exact hCL (by simp only [K331ClassicalLow]; omega)
      · by_cases h3 : 3 ≤ r
        · exact k331Idx_A hv h3 (Or.inr (by omega))
        · by_cases hq2 : q.p = 2 ∧ r = 2
          · exact hL3 (by simp only [K331L3Even]; omega)
          · exact hCL (by simp only [K331ClassicalLow]; omega)
    | twistedA r q =>
      have hr2 : 2 ≤ r := hr.1
      by_cases h3 : 3 ≤ r
      · by_cases hc : q.card % 3 = 1
        · by_cases h5 : 5 ≤ r
          · exact hRG (by simp only [K331RankGap]; omega)
          · by_cases hq2 : q.p = 2
            · exact hC2 (by simp only [K331Chev2]; omega)
            · exact hCL (by simp only [K331ClassicalLow]; omega)
        · exact k331Idx_twistedA hv h3 hc
      · by_cases hq2 : q.p = 2
        · exact hL3 (by simp only [K331L3Even]; omega)
        · exact hCL (by simp only [K331ClassicalLow]; omega)
    | B r q =>
      have hr2 : 2 ≤ r := hr.1
      by_cases h3 : 3 ≤ r
      · exact k331Idx_B hv h3
      · by_cases hq2 : q.p = 2
        · exact hC2 (by simp only [K331Chev2]; omega)
        · exact hCL (by simp only [K331ClassicalLow]; omega)
    | C r q => exact k331Idx_C hv
    | D r q => exact k331Idx_D hv
    | twistedD r q => exact k331Idx_twistedD hv
    | E6 q =>
      exact k331Idx_untwisted (c := LieTypeIndex.E6) hI.chevalley.e6
        (hI.adjoint .E6 (by simp)) q hv
    | E7 q =>
      exact k331Idx_untwisted (c := LieTypeIndex.E7) hI.chevalley.e7
        (hI.adjoint .E7 (by simp)) q hv
    | E8 q =>
      exact k331Idx_untwisted (c := LieTypeIndex.E8) hI.chevalley.e8
        (hI.adjoint .E8 (by simp)) q hv
    | F4 q =>
      exact k331Idx_untwisted (c := LieTypeIndex.F4) hI.chevalley.f4
        (hI.adjoint .F4 (by simp)) q hv
    | G2 q =>
      by_cases hq2 : q.p = 2
      · exact hC2 (by simpa only [K331Chev2] using hq2)
      · exact hG2 (by simpa only [K331G2Odd] using hq2)
    | twistedE6 q => exact hRG (by simp only [K331RankGap])
    | trialityD4 q =>
      by_cases hq2 : q.p = 2
      · exact hC2 (by simpa only [K331Chev2] using hq2)
      · exact hD4 (by simpa only [K331D4Odd] using hq2)
    | suzuki m => exact k331Idx_suzuki hv (hI.suzuki m hv)
    | reeG2 m => exact K331Idx.of_three_le (hI.ree m hv)
    | reeF4 m => exact hC2 (by simp only [K331Chev2])
    | tits => exact k331Idx_tits hv (hI.tits hv)
  · by_cases h1 : s = .J2 ∨ s = .M22 ∨ s = .M23 ∨ s = .HS
    · exact hSS h1
    · by_cases h2 : s = .He ∨ s = .Ru
      · exact hHR h2
      · refine k331Idx_sporadic hI.bridge hI.card_M11 hI.card_M12 hI.card_J1 hI.witness
          hI.monster ?_
        simp only [not_or] at h1 h2 ⊢
        exact ⟨h1.1, h1.2.1, h1.2.2.1, h1.2.2.2, h2.1, h2.2⟩

@[expose] def K331ResidueIdx (i : CFSGIndex) : Prop :=
  K331Chev2 i ∨
  K331SporSmall i

@[expose] def K331Residue : Prop := K331Fam K331ResidueIdx

theorem k331_of_inputs (hI : K331Inputs) (h : K331Residue) : K331 :=
  k331_of_fam fun i _ => k331Idx_dispatch hI i
    (hI.rankGap i)
    (hI.classicalLow i)
    (hI.l3Even i)
    (hI.g2Odd i)
    (hI.d4Odd i)
    (fun hF => h i (by simp only [K331ResidueIdx, hF, true_or, or_true]))
    (fun hF => h i (by simp only [K331ResidueIdx, hF, true_or, or_true]))
    (hI.heRu i)

end CFSG.LocalAnalysis.UniquenessCase.UC22.InS3

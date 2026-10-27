module

public import CFSG.RankThree.PartTwo.Sec4.Item423Res2ProofPairing

public section

namespace CFSG.RankThree.PartTwo.Sec4

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo CFSG.Blueprint

namespace Res4Seven


theorem exists_tauCeti_g2 {X : Type} [Group X] {p f : ℕ}
    (h : ChevalleyExceptionalModel X .G2 p f) :
    ∃ (q : TauCeti.PrimePower) (hq : (TauCeti.LieTypeIndex.G2 q).Valid),
      Nonempty (X ≃* (TauCeti.CFSGIndex.lie ⟨.G2 q, hq⟩).Group) := by
  have hB := CFSG.TauCetiBridge.Even.chevalleyBridgesAll
  obtain ⟨hadm, hm⟩ := h
  have hp : p.Prime := hadm.1
  have hf : 1 ≤ f := hadm.2.1
  let q : TauCeti.PrimePower := ⟨p, f, hp, hf⟩
  have hq : q.card = p ^ f := TauCeti.PrimePower.card_def q
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ := hm
  have hv : (TauCeti.LieTypeIndex.G2 q).Valid := by
    refine (TauCeti.LieTypeIndex.valid_iff _).2 ⟨?_, ?_⟩
    · simpa [TauCeti.LieTypeIndex.inStandardRange_iff, hq] using hadm.2.2.2
    · simp [TauCeti.LieTypeIndex.isDuplicateRepresentative_iff]
  obtain ⟨b⟩ := hB.g2 q hv K (by rw [hK, hq])
  exact ⟨q, hv, ⟨e.trans b⟩⟩

theorem exists_tauCeti_d4 {X : Type} [Group X] {p f : ℕ}
    (h : ChevalleyExceptionalModel X .trialityD4 p f) :
    ∃ (q : TauCeti.PrimePower) (hq : (TauCeti.LieTypeIndex.trialityD4 q).Valid),
      Nonempty (X ≃* (TauCeti.CFSGIndex.lie ⟨.trialityD4 q, hq⟩).Group) := by
  have hB := CFSG.TauCetiBridge.Even.chevalleyBridgesAll
  obtain ⟨hadm, hm⟩ := h
  have hp : p.Prime := hadm.1
  have hf : 1 ≤ f := hadm.2.1
  let q : TauCeti.PrimePower := ⟨p, f, hp, hf⟩
  have hq : q.card = p ^ f := TauCeti.PrimePower.card_def q
  obtain ⟨K, _, _, hK, σ, hσ, ⟨e⟩⟩ := hm
  have hv : (TauCeti.LieTypeIndex.trialityD4 q).Valid := by simp
  obtain ⟨b⟩ := hB.trialityD4 q hv K (by rw [hK, hq]) σ (fun x => by rw [hq]; exact hσ x)
  exact ⟨q, hv, ⟨e.trans b⟩⟩

theorem census424_of_g2_pairing (hL : K424PairingLie) {X : Type} [Group X] [Finite X]
    (hX : IsList46 X) (hq : IsQuasisimple X) (hZ : Subgroup.center X = ⊥)
    (hSL : ¬ IsSLThreePiAny X) {p f : ℕ} (hG : ChevalleyExceptionalModel X .G2 p f) :
    Census424 X := by
  intro D c d K h
  have hT := exists_tauCeti_g2 hG
  exact ⟨Or.inl hT, Or.inr (hL X hX hq hZ hSL (Or.inl hT) D c d K h)⟩

theorem census424_of_d4_pairing (hL : K424PairingLie) {X : Type} [Group X] [Finite X]
    (hX : IsList46 X) (hq : IsQuasisimple X) (hZ : Subgroup.center X = ⊥)
    (hSL : ¬ IsSLThreePiAny X) {p f : ℕ} (hG : ChevalleyExceptionalModel X .trialityD4 p f) :
    Census424 X := by
  intro D c d K h
  have hT := exists_tauCeti_d4 hG
  exact ⟨Or.inr (Or.inl hT), Or.inr (hL X hX hq hZ hSL (Or.inr hT) D c d K h)⟩

end Res4Seven

end CFSG.RankThree.PartTwo.Sec4

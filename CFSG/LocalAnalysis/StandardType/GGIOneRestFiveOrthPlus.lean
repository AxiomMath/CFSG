module

public import CFSG.LocalAnalysis.StandardType.GGIOneRestFiveRoot
public import CFSG.LocalAnalysis.StandardType.GGIOneOrthEndMain

public section

namespace CFSG.StandardType

open CFSG.Assembly

@[expose] def GGIOneOrthPlusFourInput : Prop :=
  ∀ (K : Type) [Field K] [Finite K], Nat.card K = 2 →
    GGEndNodeIOne 3 3 (OrthRest.RPlus K 4) (LargeEvenInnSet _)

section Certs

theorem largeEvenLabelAll_endNodeIOne_orthPlusFour (hE : GGIOneOrthPlusFourInput) {p : ℕ}
    {lab : LargeEvenLabel} (h : GGIOneMoreOrthPlusFourLabel p lab) :
    LargeEvenLabelAll lab fun R _ I _ => GGOutdiagOdd p R I ∧
      ∃ r, GGTorusLift p r R ∧ GGEndNodeIOne p r R I := by
  obtain ⟨t, l, n⟩ := lab
  obtain ⟨ht, hl, hn, rfl⟩ := h
  dsimp only at ht hl hn
  subst ht hl hn
  intro Q hQ
  dsimp only [LargeEvenRawDatum] at hQ ⊢
  split_ifs at hQ ⊢ with h3
  · omega
  · obtain ⟨K, _, _, hK, hq⟩ := hQ
    have hK2 : Nat.card K = 2 := by rw [hK, pow_one]
    exact ⟨K, inferInstance, inferInstance, hK, hq, ggOutdiagOdd_innSet _ _, 4 - 1,
      ggOrthRestTorusLiftInput_holds.2 K 4 hK2 le_rfl, hE K hK2⟩

theorem ggStdSubIOneProperInputOn_orthPlusFour (ha₀ : GGLNoncyclicInput)
    (hE : GGIOneOrthPlusFourInput) : GGStdSubIOneProperInputOn GGIOneMoreOrthPlusFourLabel :=
  ggStdSubIOneProperInputOn_of_labels ha₀ fun _ _ _ _ h _ =>
    largeEvenLabelAll_endNodeIOne_orthPlusFour hE h

end Certs

end CFSG.StandardType

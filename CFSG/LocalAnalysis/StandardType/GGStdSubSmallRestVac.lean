module

public import CFSG.LocalAnalysis.StandardType.GGStdSubSmall
public import CFSG.LocalAnalysis.StandardType.GGTableBExcSmall
public import CFSG.LocalAnalysis.StandardType.GGTableBTwoThreeB2der

public section

namespace CFSG.StandardType

open CFSG.Assembly

theorem ggStdSubSmallInputOn_of_labelAll_card_lt {S : ℕ → LargeEvenLabel → Prop}
    (h : ∀ (p : ℕ) (lab : LargeEvenLabel), p.Prime → LargeEvenInLambda2 lab → S p lab →
      LargeEvenSplit p lab → LargeEvenLabelAll lab fun R _ I _ => ∀ X : Subgroup (MulAut R),
        (X : Set (MulAut R)) ⊆ I → IsElemAbelian p X → Nat.card X < p ^ 3) :
    GGStdSubSmallInputOn S :=
  fun _ _ _ _ _ _ _ _ _ _ hcfg hM _ => (ggThmIHyp_false_of_labelAll h hcfg.1 hM).elim

theorem largeEvenLabelAll_card_lt_b2derThree {p : ℕ} {lab : LargeEvenLabel}
    (h : GGB2derThreeLabel p lab) :
    LargeEvenLabelAll lab fun R _ I _ => ∀ X : Subgroup (MulAut R),
      (X : Set (MulAut R)) ⊆ I → IsElemAbelian p X → Nat.card X < p ^ 3 := by
  obtain ⟨t, l, n⟩ := lab
  obtain ⟨rfl, ht⟩ := h
  dsimp only at ht
  subst ht
  intro Q hQ
  obtain ⟨K, i1, i2, hK, hQ⟩ := hQ
  exact ⟨K, i1, i2, hK, hQ, fun X hXI hX => TwoThree.card_lt_of_not_dvd Nat.prime_three
    (TwoThree.gsp_subset_normalizer hK) (TwoThree.not_dvd_card_GL_four hK) hX hXI⟩

@[expose] def GGStdSubSmallVacLabel (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  lab.tag = .G2 ∨ lab.tag = .twB2 ∨ GGTableBTwDThreeLabel p lab ∨ GGB2derThreeLabel p lab

theorem ggStdSubSmallInputOn_vac :
    GGStdSubSmallInputOn GGStdSubSmallVacLabel :=
  ggStdSubSmallInputOn_of_labelAll_card_lt fun _ _ hp hlab h hs => by
    rcases h with h | h | h | h
    · exact TableBExc.largeEvenLabelAll_card_lt_G2TwB2 hp hlab (Or.inl h) hs
    · exact TableBExc.largeEvenLabelAll_card_lt_G2TwB2 hp hlab (Or.inr h) hs
    · exact largeEvenLabelAll_card_lt_twDThree hp hlab h
    · exact largeEvenLabelAll_card_lt_b2derThree h

end CFSG.StandardType

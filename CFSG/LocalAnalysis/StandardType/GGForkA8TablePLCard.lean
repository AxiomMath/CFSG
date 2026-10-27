module

public import CFSG.LocalAnalysis.StandardType.GGForkA8TablePClauses
public import CFSG.LocalAnalysis.StandardType.GGSecFiveSplitNbrSmallRank
public import CFSG.LocalAnalysis.StandardType.GGFieldCaseL48TBVac
public import CFSG.LocalAnalysis.StandardType.GGTableBNbrInnerNinePGL
public import CFSG.LocalAnalysis.StandardType.GGTableBNbrInnerNineSmall
public import CFSG.LocalAnalysis.StandardType.GGTableBTwDThree

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Open

@[expose] def GGTAPSmall (lab : LargeEvenLabel) : Prop :=
  (lab.tag = .A ∧ lab.rank ≤ 2) ∨ ((lab.tag = .B ∨ lab.tag = .C) ∧ lab.rank = 2) ∨
    lab.tag = .G2 ∨ lab.tag = .triD4 ∨ (lab.tag = .twD ∧ lab.rank ≤ 3)

theorem largeEvenLabelAll_card_lt_seven_small
    {lab : LargeEvenLabel} (hlab : LargeEvenInLambda2 lab) (hn : lab.n = 3) (h : GGTAPSmall lab) :
    LargeEvenLabelAll lab fun R _ I _ => ∀ X : Subgroup (MulAut R),
      (X : Set (MulAut R)) ⊆ I → IsElemAbelian 7 X → Nat.card X < 7 ^ 3 := by
  obtain ⟨t, l, n⟩ := lab
  dsimp only at hn
  subst hn
  simp only [GGTAPSmall] at h
  rcases h with ⟨ht, hr⟩ | ⟨ht, hr⟩ | ht | ht | ⟨ht, hr⟩
  ·
    subst ht
    have hl1 : 1 ≤ l := hlab.2.1
    have hl12 : l = 1 ∨ l = 2 := by omega
    rcases hl12 with rfl | rfl
    · exact largeEvenLabelAll_card_lt_linearTwo (p := 7) (by norm_num) (by norm_num) hlab
        (.inl ⟨rfl, rfl⟩)
    · exact largeEvenLabelAll_card_lt_A2_all (p := 7) (by norm_num) (by norm_num) rfl rfl
  ·
    rcases ht with rfl | rfl
    · exact largeEvenLabelAll_card_lt_symplecticTwo (p := 7) (by norm_num) (by norm_num) hlab
        (Or.inl rfl) hr
    · exact largeEvenLabelAll_card_lt_symplecticTwo (p := 7) (by norm_num) (by norm_num) hlab
        (Or.inr rfl) hr
  ·
    subst ht
    exact NbrInnerNine.largeEvenLabelAll_card_lt_G2_all (p := 7) (by norm_num) (by norm_num) rfl
  ·
    subst ht
    exact NbrInnerNine.largeEvenLabelAll_card_lt_triD4_of (p := 7) (by norm_num) hlab rfl
      (.inr (by norm_num))
  ·
    subst ht
    have hl2 : 2 ≤ l := hlab.2
    have hl23 : l = 2 ∨ l = 3 := by omega
    rcases hl23 with rfl | rfl
    · exact largeEvenLabelAll_card_lt_linearTwo (p := 7) (by norm_num) (by norm_num) hlab
        (.inr ⟨rfl, rfl⟩)
    · exact largeEvenLabelAll_card_lt_twDThree (p := 7) (by norm_num) hlab ⟨rfl, rfl, by norm_num⟩

end CFSG.StandardType

end

module

public import CFSG.LocalAnalysis.StandardType.GGTableBThreeTBE6
public import CFSG.LocalAnalysis.StandardType.GGTableBExcTwoTBMain
public import CFSG.LocalAnalysis.StandardType.GGBstarLIDUnit63Holds
public import CFSG.LocalAnalysis.StandardType.GGRemTableBLExc3
public import CFSG.LocalAnalysis.StandardType.GGRemTableBLExcReduction
public import CFSG.LocalAnalysis.StandardType.GGTableBUnitTvSixQ2

public section

namespace CFSG.Yardstones.M3f9567aba59d

open CFSG CFSG.Assembly CFSG.StandardType CFSG.StandardType.TableBExcTwoTB

@[expose] def GGRemTableBLExc4Label (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  (lab.tag = .twE6 ∧ p ∣ 2 ^ lab.n + 1 ∧ p < 5) ∨ (lab.tag = .F4 ∧ lab.n = 1 ∧ p = 3)

@[expose] def GGRemTableBLExc4TvLabel (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  (lab.tag = .twE6 ∧ p ∣ 2 ^ lab.n + 1 ∧ p < 5) ∨
    ((lab.tag = .E7 ∨ lab.tag = .E8 ∨ lab.tag = .F4) ∧ lab.n = 1 ∧ p = 3)

theorem ggRemTableBLExc4Label_of (p : ℕ) (lab : LargeEvenLabel)
    (h : ((GGRemTableBLExc3Label p lab ∧ ¬ GGTableBE6DivLabel p lab) ∧
      ¬ GGE7TwoThreeLabel p lab) ∧ ¬ GGE8TwoThreeLabel p lab) :
    GGRemTableBLExc4Label p lab := by
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  rcases h1 with h1 | h1 | ⟨ht, hn, hp⟩
  · exact Or.inl h1
  · exact (h2 h1).elim
  · rcases ht with ht | ht | ht
    · exact (h3 ⟨ht, hn, hp⟩).elim
    · exact (h4 ⟨ht, hn, hp⟩).elim
    · exact Or.inr ⟨ht, hn, hp⟩

theorem ggRemTableBLExc4TvLabel_of (p : ℕ) (lab : LargeEvenLabel)
    (h : GGRemTableBLExc3Label p lab ∧ ¬ GGTableBE6DivLabel p lab) :
    GGRemTableBLExc4TvLabel p lab := by
  obtain ⟨h1, h2⟩ := h
  rcases h1 with h1 | h1 | h1
  · exact Or.inl h1
  · exact (h2 h1).elim
  · exact Or.inr h1

end CFSG.Yardstones.M3f9567aba59d

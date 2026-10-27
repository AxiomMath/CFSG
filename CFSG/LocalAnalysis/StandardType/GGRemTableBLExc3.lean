module

public import CFSG.LocalAnalysis.StandardType.GGRemTableBLExcLabel
public import CFSG.LocalAnalysis.StandardType.GGTableBE6TwoTBTv
public import CFSG.LocalAnalysis.StandardType.GGTableBTwE6TBModel

public section

namespace CFSG.Yardstones.M3f9567aba59d

open CFSG CFSG.Assembly CFSG.StandardType

@[expose] def GGRemTableBLExc3Label (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  (lab.tag = .twE6 ∧ p ∣ 2 ^ lab.n + 1 ∧ p < 5) ∨
    (lab.tag = .E6 ∧ p = 3 ∧ p ∣ 2 ^ lab.n - 1) ∨
    ((lab.tag = .E7 ∨ lab.tag = .E8 ∨ lab.tag = .F4) ∧ lab.n = 1 ∧ p = 3)

theorem ggRemTableBLExc3Label_of_exc2 (p : ℕ) (lab : LargeEvenLabel)
    (h : GGRemTableBLExc2Label p lab ∧ ¬ GGTwE6TBLabel p lab) : GGRemTableBLExc3Label p lab := by
  obtain ⟨h1, h2⟩ := h
  rcases h1 with ⟨ht, hd⟩ | h1 | h1
  · refine Or.inl ⟨ht, hd, ?_⟩
    by_contra h5
    exact h2 ⟨ht, hd, by omega⟩
  · exact Or.inr (Or.inl h1)
  · exact Or.inr (Or.inr h1)

end CFSG.Yardstones.M3f9567aba59d

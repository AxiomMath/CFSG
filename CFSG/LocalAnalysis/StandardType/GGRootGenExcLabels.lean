module

public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyQFourDom

public section

namespace CFSG.StandardType

open CFSG.Assembly

@[expose] def GGRootGenExcTag (lab : LargeEvenLabel) : Prop :=
  lab.tag = .E6 ∨ lab.tag = .E7 ∨ lab.tag = .E8 ∨ lab.tag = .F4 ∨ lab.tag = .twE6

@[expose] def GGRootGenExcNonSplitLabel (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  GGRootGenExcTag lab ∧ 2 ≤ lab.n ∧ ¬ LargeEvenSplit p lab

@[expose] def GGRootGenExcNonHalfSplitLabel (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  GGRootGenExcTag lab ∧ 2 ≤ lab.n ∧ ¬ LargeEvenHalfSplit p lab False

theorem eq_of_ggLabelIso_of_excTag {lab lab' : LargeEvenLabel} (h : GGRootGenExcTag lab)
    (hiso : GGLabelIso lab lab') : lab' = lab := by
  obtain ⟨t, l, n⟩ := lab
  unfold GGRootGenExcTag at h
  unfold GGLabelIso at hiso
  rcases hiso with h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8
  · exact h1.symm
  all_goals exfalso
  all_goals rcases h with h | h | h | h | h <;> simp_all

theorem largeEvenHalfSplit_false_of_excTag {p : ℕ} {lab : LargeEvenLabel} {c : Prop}
    (h : GGRootGenExcTag lab) (hs : LargeEvenHalfSplit p lab c) :
    LargeEvenHalfSplit p lab False := by
  rcases hs with hs | hs | hs | ⟨h4, -⟩ | hs | hs
  · exact Or.inl hs
  · exact Or.inr (Or.inl hs)
  · exact Or.inr (Or.inr (Or.inl hs))
  · exfalso
    rcases h with h | h | h | h | h <;> rw [h] at h4 <;> cases h4
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hs))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hs))))

end CFSG.StandardType

end

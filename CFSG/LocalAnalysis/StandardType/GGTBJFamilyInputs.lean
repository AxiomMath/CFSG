module

public import CFSG.LocalAnalysis.StandardType.GGTBJLabelSides

public section

namespace CFSG.StandardType

open CFSG.Assembly

@[expose] def ggTBJSplitALabel (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  (lab.tag = .A ∨ (lab.tag = .D ∧ lab.rank = 3)) ∧ 3 ≤ lab.rank ∧ p ∣ 2 ^ lab.n - 1

@[expose] def ggTBJSpRankThreeLabel (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  (lab.tag = .B ∨ lab.tag = .C) ∧ lab.rank = 3 ∧ p ∣ 2 ^ lab.n - 1

@[expose] def ggTBJUnitaryDvdLabel (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  lab.tag = .twA ∧ 4 ≤ lab.rank ∧ ¬ (lab.rank = 5 ∧ lab.n = 1) ∧ p ∣ 2 ^ lab.n + 1 ∧
    p ∣ lab.rank + 1

@[expose] def GGTBJOrdinaryOutside (E : ℕ → LargeEvenLabel → Prop) : Prop :=
  (GGTBJLeftOn fun p lab => ¬ ggTBJExoticTag p lab ∧ ¬ E p lab) ∧
    (GGTBJNbrOn fun p lab => ¬ ggTBJExoticTag p lab ∧ ¬ E p lab)

@[expose] def GGTBJOrderRestSplitAInput : Prop :=
  GGTBJOrdinaryOutside fun p lab =>
    GGRootGenSmallRankLabel p lab ∨ ggTBJFieldTwoLabel p lab ∨
      GGTableBNbrInnerNineClassicalLabel p lab ∨ ggTBJSplitALabel p lab

theorem GGTBJOrdinaryOutside.of_proved {E T : ℕ → LargeEvenLabel → Prop}
    (hL : GGTBJLeftOn T) (hK : GGTBJNbrOn T)
    (h : GGTBJOrdinaryOutside fun p lab => E p lab ∨ T p lab) : GGTBJOrdinaryOutside E := by
  classical
  have hL' := h.1.or hL
  have hK' := h.2.or hK
  refine ⟨hL'.mono ?_, hK'.mono ?_⟩ <;>
  · intro p lab hP
    by_cases hT : T p lab
    · exact Or.inr hT
    · exact Or.inl ⟨hP.1, fun hE => hE.elim hP.2 hT⟩

@[expose] def GGTBJOrderRestSplitAUnitDvdInput : Prop :=
  GGTBJOrdinaryOutside fun p lab =>
    (GGRootGenSmallRankLabel p lab ∨ ggTBJFieldTwoLabel p lab ∨
      GGTableBNbrInnerNineClassicalLabel p lab ∨ ggTBJSplitALabel p lab) ∨
        ggTBJUnitaryDvdLabel p lab

@[expose] def ggTBJUnitarySixLabel (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  lab.tag = .twA ∧ lab.rank = 5 ∧ p = 3 ∧ lab.n = 1

@[expose] def ggTBJUnitaryRankThreeLabel (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  (lab.tag = .twA ∨ lab.tag = .twD) ∧ lab.rank = 3 ∧ p ∣ 2 ^ lab.n + 1

@[expose] def GGTBJOrderRestSplitAUnitSixInput : Prop :=
  GGTBJOrdinaryOutside fun p lab =>
    ((GGRootGenSmallRankLabel p lab ∨ ggTBJFieldTwoLabel p lab ∨
      GGTableBNbrInnerNineClassicalLabel p lab ∨ ggTBJSplitALabel p lab) ∨
        ggTBJUnitaryDvdLabel p lab) ∨ ggTBJUnitarySixLabel p lab

@[expose] def GGTBJOrderRestSplitAUnitRankThreeInput : Prop :=
  GGTBJOrdinaryOutside fun p lab =>
    (((GGRootGenSmallRankLabel p lab ∨ ggTBJFieldTwoLabel p lab ∨
      GGTableBNbrInnerNineClassicalLabel p lab ∨ ggTBJSplitALabel p lab) ∨
        ggTBJUnitaryDvdLabel p lab) ∨ ggTBJUnitarySixLabel p lab) ∨
          ggTBJUnitaryRankThreeLabel p lab

end CFSG.StandardType

end

module

public import CFSG.LocalAnalysis.StandardType.GGResLeviLE3Defs
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyRefl
public import CFSG.LocalAnalysis.StandardType.GGRootGenSmallRankQFour
public import CFSG.LocalAnalysis.StandardType.GGTableBNbrInnerNineClassicalLabel

public section

namespace CFSG.StandardType

open CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

@[expose] def GGTBJLeftOn (S : ℕ → LargeEvenLabel → Prop) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (y : G) (K : Subgroup G), GGResHyp p B Bs x L D J y K → ∀ [Fact p.Prime],
    GGInnerDiagOnLabel S p Bs L → GGResXDatum p Bs L →
      GGResSideDatum p Bs L J ∨ GGResLeviSideDatumLE3 p Bs L J ∨ GGResRowAt ggRowNonLevi p J L

@[expose] def GGTBJNbrOn (S : ℕ → LargeEvenLabel → Prop) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (y : G) (K : Subgroup G), GGResHyp p B Bs x L D J y K → ∀ [Fact p.Prime],
    GGInnerDiagOnLabel S p Bs K → GGResXDatum p Bs K →
      GGResSideDatum p Bs K J ∨ GGResLeviSideDatumLE3 p Bs K J ∨ GGResRowAt ggRowNonLevi p J K

theorem GGTBJLeftOn.mono {S T : ℕ → LargeEvenLabel → Prop} (h : GGTBJLeftOn S)
    (hTS : ∀ p lab, T p lab → S p lab) : GGTBJLeftOn T :=
  by
  intro G _ _ p B Bs x L D J y K hH hp hL hX
  exact h G p B Bs x L D J y K hH
    (largeEvenMarking_mono (fun _ _ _ _ _ _ hP => ⟨hTS p _ hP.1, hP.2⟩) hL) hX

theorem GGTBJNbrOn.mono {S T : ℕ → LargeEvenLabel → Prop} (h : GGTBJNbrOn S)
    (hTS : ∀ p lab, T p lab → S p lab) : GGTBJNbrOn T :=
  by
  intro G _ _ p B Bs x L D J y K hH hp hK hX
  exact h G p B Bs x L D J y K hH
    (largeEvenMarking_mono (fun _ _ _ _ _ _ hP => ⟨hTS p _ hP.1, hP.2⟩) hK) hX

theorem GGTBJLeftOn.or {S T : ℕ → LargeEvenLabel → Prop} (hS : GGTBJLeftOn S)
    (hT : GGTBJLeftOn T) : GGTBJLeftOn fun p lab => S p lab ∨ T p lab :=
  by
  intro G _ _ p B Bs x L D J y K hH hp hL hX
  exact (GGInnerDiagOnLabel.elim_or hL).elim
    (fun h => hS G p B Bs x L D J y K hH h hX) (fun h => hT G p B Bs x L D J y K hH h hX)

theorem GGTBJNbrOn.or {S T : ℕ → LargeEvenLabel → Prop} (hS : GGTBJNbrOn S)
    (hT : GGTBJNbrOn T) : GGTBJNbrOn fun p lab => S p lab ∨ T p lab :=
  by
  intro G _ _ p B Bs x L D J y K hH hp hK hX
  exact (GGInnerDiagOnLabel.elim_or hK).elim
    (fun h => hS G p B Bs x L D J y K hH h hX) (fun h => hT G p B Bs x L D J y K hH h hX)

theorem ggTBJInputR_of_labels (hL : GGTBJLeftOn fun _ _ => True)
    (hK : GGTBJNbrOn fun _ _ => True) : GGTBJInputR := by
  intro G _ _ p B Bs x L D J y K hH hp
  refine ⟨fun hX => hL G p B Bs x L D J y K hH ?_ hX, fun hX => hK G p B Bs x L D J y K hH ?_ hX⟩
  · exact largeEvenMarking_mono (fun _ _ _ _ _ _ hP => ⟨trivial, hP⟩) hH.2.2.1.1
  · exact largeEvenMarking_mono (fun _ _ _ _ _ _ hP => ⟨trivial, hP⟩)
      (hH.2.2.1.2 y K hH.2.2.2.2.1)

@[expose] def ggTBJExoticTag (_p : ℕ) (lab : LargeEvenLabel) : Prop :=
  lab.tag = .triD4 ∨ lab.tag = .G2 ∨ lab.tag = .twB2 ∨ lab.tag = .twF4 ∨ lab.tag = .B2der ∨
    lab.tag = .G2der ∨ lab.tag = .twF4der

@[expose] def GGTBJOrdinaryInput : Prop :=
  (GGTBJLeftOn fun p lab => ¬ ggTBJExoticTag p lab) ∧
    (GGTBJNbrOn fun p lab => ¬ ggTBJExoticTag p lab)

@[expose] def ggTBJLowRankOrdinaryLabel (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  GGRootGenSmallRankLabel p lab ∧ ¬ ggTBJExoticTag p lab

@[expose] def GGTBJOrdinaryRestInput : Prop :=
  (GGTBJLeftOn fun p lab => ¬ ggTBJExoticTag p lab ∧ ¬ GGRootGenSmallRankLabel p lab) ∧
    (GGTBJNbrOn fun p lab => ¬ ggTBJExoticTag p lab ∧ ¬ GGRootGenSmallRankLabel p lab)

@[expose] def ggTBJFieldTwoLabel (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  StdSubRestThree.GGTwoThreeSmallLabel p lab ∧ 3 ≤ lab.rank

@[expose] def GGTBJFieldTwoRestInput : Prop :=
  (GGTBJLeftOn fun p lab =>
    (¬ ggTBJExoticTag p lab ∧ ¬ GGRootGenSmallRankLabel p lab) ∧ ¬ ggTBJFieldTwoLabel p lab) ∧
  (GGTBJNbrOn fun p lab =>
    (¬ ggTBJExoticTag p lab ∧ ¬ GGRootGenSmallRankLabel p lab) ∧ ¬ ggTBJFieldTwoLabel p lab)

@[expose] def GGTBJOrderRestInput : Prop :=
  (GGTBJLeftOn fun p lab =>
    ((¬ ggTBJExoticTag p lab ∧ ¬ GGRootGenSmallRankLabel p lab) ∧ ¬ ggTBJFieldTwoLabel p lab) ∧
      ¬ GGTableBNbrInnerNineClassicalLabel p lab) ∧
  (GGTBJNbrOn fun p lab =>
    ((¬ ggTBJExoticTag p lab ∧ ¬ GGRootGenSmallRankLabel p lab) ∧ ¬ ggTBJFieldTwoLabel p lab) ∧
      ¬ GGTableBNbrInnerNineClassicalLabel p lab)

end CFSG.StandardType

end

module

public import CFSG.LocalAnalysis.StandardType.GGCoxeterLabelProof

public section

namespace CFSG.StandardType

open Module CFSG.Assembly

@[expose] def GGDependentReflectionDatum {G : Type} [Group G] (p : ℕ) [Fact p.Prime]
    (Bs L K : Subgroup G) : Prop :=
  ∃ (Λ : Type) (_ : Fintype Λ) (_ : DecidableEq Λ)
    (V : Type) (_ : AddCommGroup V) (_ : Module (ZMod p) V)
    (ι : Additive ↥Bs ≃+ V) (φ : Option Λ → MulAut ↥Bs)
    (h : Option Λ → V) (α : Option Λ → Module.Dual (ZMod p) V) (b : Λ),
    (∀ node, α node (h node) = 2) ∧
      (∀ node, h node ≠ 0) ∧
      (∀ node vector, ggLin (p := p) ι (φ node) vector =
        vector - α node vector • h node) ∧
      ¬ LinearIndependent (ZMod p) h ∧
      ggAutomizer L Bs = Subgroup.closure (Set.range fun node : Λ => φ (some node)) ∧
      ggAutomizer K Bs = Subgroup.closure
        (Set.range (fun node : {node : Λ // node ≠ b} => φ (some node)) ∪ {φ none})

@[expose] def GGExceptionalTypeAPair {G : Type} [Group G] (p : ℕ)
    (Bs L K : Subgroup G) : Prop :=
  p = 3 ∧ ∃ leftRank rightRank : ℕ,
    1 ≤ leftRank ∧ 1 ≤ rightRank ∧
      Nonempty ((CoxeterMatrix.A leftRank).Group ≃* ↥(ggAutomizer L Bs)) ∧
      Nonempty ((CoxeterMatrix.A rightRank).Group ≃* ↥(ggAutomizer K Bs)) ∧
      (leftRank = 5 ∨ leftRank = 8 ∨ rightRank = 5 ∨ rightRank = 8)

@[expose] def GGResidualOther {G : Type} [Group G] (p : ℕ) [Fact p.Prime]
    (Bs L K : Subgroup G) : Prop :=
  ¬ GGExceptionalTypeAPair p Bs L K ∧ ¬ GGDependentReflectionDatum p Bs L K

@[expose] def GGCoxeterLabelResidualInputOn
    (label : ∀ (G : Type) [Group G] (p : ℕ) [Fact p.Prime],
      Subgroup G → Subgroup G → Subgroup G → Prop) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G)
    (x : G) (L D J : Subgroup G),
    GGConfig p B Bs x L D J → GGOpAutTrivial p Bs →
      GGInnerDiagAll p B Bs x L D J → GGNoTransvection p Bs →
      ∀ (y : G) (K : Subgroup G), GGNbr p B x D J y K →
      GGReflGenerated p (ggAutomizer K Bs) → GGScalarsOrWeyl' p B Bs x D J →
      ∀ [Fact p.Prime], ¬ GGCoxeterForkDatum p Bs L K →
      ¬ GGCoxeterStdDatum p Bs L K → label G p Bs L K →
      GGWeylReflectionGroup p (ggAutomizer L Bs ⊔ ggAutomizer K Bs)

@[expose] def GGCoxeterLabelExceptionalTypeAInput : Prop :=
  GGCoxeterLabelResidualInputOn (fun _ _ p _ Bs L K => GGExceptionalTypeAPair p Bs L K)

@[expose] def GGCoxeterLabelDependentInput : Prop :=
  GGCoxeterLabelResidualInputOn (fun _ _ p _ Bs L K => GGDependentReflectionDatum p Bs L K)

@[expose] def GGCoxeterLabelOtherInput : Prop :=
  GGCoxeterLabelResidualInputOn (fun _ _ p _ Bs L K => GGResidualOther p Bs L K)

theorem ggResidual_cases {G : Type} [Group G] (p : ℕ) [Fact p.Prime]
    (Bs L K : Subgroup G) :
    GGExceptionalTypeAPair p Bs L K ∨ GGDependentReflectionDatum p Bs L K ∨
      GGResidualOther p Bs L K := by
  classical
  by_cases exceptional : GGExceptionalTypeAPair p Bs L K
  · exact Or.inl exceptional
  · by_cases dependent : GGDependentReflectionDatum p Bs L K
    · exact Or.inr (Or.inl dependent)
    · exact Or.inr (Or.inr ⟨exceptional, dependent⟩)

theorem ggCoxeterLabelResidualInput_of_cases
    (exceptionalInput : GGCoxeterLabelExceptionalTypeAInput)
    (dependentInput : GGCoxeterLabelDependentInput)
    (otherInput : GGCoxeterLabelOtherInput) : GGCoxeterLabelResidualInput := by
  intro G _ _ p B Bs x L D J config opAut innerDiag noTransvection y K neighbour
    reflectionGenerated scalars _ noFork noStandard
  rcases ggResidual_cases p Bs L K with exceptional | dependent | other
  · exact exceptionalInput G p B Bs x L D J config opAut innerDiag noTransvection y K
      neighbour reflectionGenerated scalars noFork noStandard exceptional
  · exact dependentInput G p B Bs x L D J config opAut innerDiag noTransvection y K
      neighbour reflectionGenerated scalars noFork noStandard dependent
  · exact otherInput G p B Bs x L D J config opAut innerDiag noTransvection y K
      neighbour reflectionGenerated scalars noFork noStandard other

end CFSG.StandardType

module

public import CFSG.LocalAnalysis.StandardType.GGR4PumpDefs
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GField
public import CFSG.CharacterTheory.Wreathed.BrauerWongTypes
public import CFSG.CharacterTheory.Wreathed.WreathCentralSquare
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10FBase2
public import CFSG.LocalAnalysis.GLTheoremA.CatA.YS1011U64Types
public import CFSG.LocalAnalysis.GLTheoremA.S11.Inputs119

public section

namespace CFSG.StandardType.KG

open CFSG.Open CFSG.Assembly CFSG.LocalAnalysis.GLTheoremA
  CFSG.LocalAnalysis.GLTheoremA.Y10GField CFSG.LocalAnalysis.GLTheoremA.Y10F

@[expose] def KGLabConcl (lab : LargeEvenLabel) (k f : ℕ) : Prop :=
  ((lab.tag = .B ∨ lab.tag = .C) ∧ k < lab.rank ∧ lab.n = f) ∨ (k = 3 ∧ lab.tag = .F4 ∧ lab.n = f)

@[expose] def KGSimpleOn (Fam : GLALabel → Prop) : Prop :=
  ∀ (p : ℕ), p.Prime → p ≠ 2 → ∀ (S : Type) [Group S] [Finite S] (lab : LargeEvenLabel)
    (α : MulAut S) (K : Subgroup S), Fam lab → LargeEvenInLambda2 lab → Subgroup.center S = ⊥ →
      InnDiagKind S lab α → α ^ p = 1 → α ≠ 1 → CFSG.Assembly.IsComponentOf K (ggFixSub α) →
        ∀ k f : ℕ, 3 ≤ k → GGHasLabel ⟨.C, k, f⟩ (K ⧸ Subgroup.center K) → KGLabConcl lab k f

@[expose] def KGSimple : Prop := KGSimpleOn fun _ => True

@[expose] def FamExcE (lab : GLALabel) : Prop := lab.tag = .E6 ∨ lab.tag = .E7 ∨ lab.tag = .E8

@[expose] def FamExcTw (lab : GLALabel) : Prop := lab.tag = .twE6

@[expose] def FamExcF4 (lab : GLALabel) : Prop := lab.tag = .F4

@[expose] def FamExcSmall (lab : GLALabel) : Prop :=
  lab.tag = .triD4 ∨ lab.tag = .G2 ∨ lab.tag = .G2der ∨ lab.tag = .twB2 ∨ lab.tag = .twF4 ∨
    lab.tag = .twF4der

end CFSG.StandardType.KG

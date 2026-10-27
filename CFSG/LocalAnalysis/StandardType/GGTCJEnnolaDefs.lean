module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveSplitNbrEnnola
public import CFSG.LocalAnalysis.StandardType.GGTCJDivDefs

public section

namespace CFSG.StandardType.TCJ

open CFSG.Open CFSG.Assembly CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.Y10F
  CFSG.LocalAnalysis.GLTheoremA.Y10GField
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup)

@[expose] def TCJEnnolaSimple : Prop :=
  ∀ (p : ℕ), p.Prime → p ≠ 2 → ∀ (S : Type) [Group S] [Finite S] (lab : LargeEvenLabel)
    (α : MulAut S) (K : Subgroup S), LargeEvenInLambda2 lab → ggRowP_Ennola p lab →
      Subgroup.center S = ⊥ → InnDiagKind S lab α → α ^ p = 1 →
      CFSG.Assembly.IsComponentOf K (ggFixSub α) →
        ∀ labJ₀ : LargeEvenLabel, LargeEvenInLambda2 labJ₀ →
          GGHasLabel labJ₀ (K ⧸ Subgroup.center K) →
          ∃ labJ : LargeEvenLabel, LargeEvenInLambda2 labJ ∧
            GGHasLabel labJ (K ⧸ Subgroup.center K) ∧ p ∣ 2 ^ labJ.n + 1 ∧
            ¬ (labJ.tag = .twD ∧ labJ.rank = 2)

@[expose] def InnDiagAllEnnolaOn (Fam : GLALabel → Prop) : Prop :=
  ∀ (S : Type) [Group S] [Finite S] (p : ℕ) (α : MulAut S) (J : Subgroup S)
    (labK labJ : GLALabel), Fam labK → p.Prime → p ≠ 2 → ggRowP_Ennola p labK →
      Subgroup.center S = ⊥ → InnDiagKind S labK α → α ^ p = 1 →
        HasLabel ↥J (fun l : GLALabel => l = labJ) →
        CFSG.Assembly.IsComponentOf J (fixSubgroup α) →
          ∃ k : ℕ, Odd k ∧ (canonLabel labJ).n = k * (canonLabel labK).n

end CFSG.StandardType.TCJ

end

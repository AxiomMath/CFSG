module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GField
public import CFSG.CharacterTheory.Wreathed.BrauerWongTypes
public import CFSG.CharacterTheory.Wreathed.WreathCentralSquare
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10FBase2
public import CFSG.LocalAnalysis.GLTheoremA.CatA.YS1011U64Types
public import CFSG.LocalAnalysis.GLTheoremA.S11.Inputs119

public section

namespace CFSG.StandardType.TCJ

open CFSG.Open CFSG.Assembly CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.Y10F
  CFSG.LocalAnalysis.GLTheoremA.Y10GField
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup)

@[expose] def InnDiagAllOn (Fam : GLALabel → Prop) : Prop :=
  ∀ (S : Type) [Group S] [Finite S] (p : ℕ) (α : MulAut S) (J : Subgroup S)
    (labK labJ : GLALabel), Fam labK → p.Prime → p ≠ 2 → Subgroup.center S = ⊥ →
      InnDiagKind S labK α → α ^ p = 1 → HasLabel ↥J (fun l : GLALabel => l = labJ) →
        CFSG.Assembly.IsComponentOf J (fixSubgroup α) →
          (canonLabel labK).n ∣ (canonLabel labJ).n

end CFSG.StandardType.TCJ

end

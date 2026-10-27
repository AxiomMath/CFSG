module

public import CFSG.LocalAnalysis.StandardType.GGFinModelInput
public import CFSG.LocalAnalysis.StandardType.GGFinModelRootCompatDefs

public section

namespace CFSG.StandardType.LieKnownR2.ExcPos

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.StandardType CFSG.StandardType.GGFinModel
  CFSG.Open CFSG.RankThree.PartOne.KE

@[expose] def TwE6LangPos (f : ℕ)
    (E : Subgroup (ModGL (langTag .twistedE6) GGL)) (w : WeylGroup (langTag .twistedE6))
    (g : ModGL (langTag .twistedE6) GGL) : Prop :=
  g ∈ adjointGroup (langTag .twistedE6) GGL ∧
    ggPhi .twistedE6 f g = g * canonicalRep (coxeterSystem (langTag .twistedE6)) GGL w ∧
    E.map (MulAut.conj g⁻¹).toMonoidHom ≤
      twistedTorusOf (canonicalRep (coxeterSystem (langTag .twistedE6)) GGL w)
        (ggPhi .twistedE6 f)

@[expose] def TwE6LawPos
    (p f : ℕ) (E : Subgroup (ModGL (langTag .twistedE6) GGL)) : Prop :=
  ∃ (ht : GGExcFive .twistedE6) (w : WeylGroup (langTag .twistedE6))
    (g : ModGL (langTag .twistedE6) GGL), TwE6LangPos f E w g ∧ GGWeylLaw .twistedE6 p f ht w

section Units


@[expose] def TwE6TTFive : Prop :=
  ∀ (f : ℕ), 1 ≤ f → 5 ∣ 2 ^ f + 1 →
    ∀ E : Subgroup (ModGL (langTag .twistedE6) GGL), E ≤ ggFixGp .twistedE6 f →
      IsElemAbelian 5 E → Nat.card E = 5 ^ 4 → TwE6LawPos 5 f E

@[expose] def TwE6TTThreeSplit : Prop :=
  ∀ (f : ℕ), 1 ≤ f → 3 ∣ 2 ^ f - 1 →
    ∀ E : Subgroup (ModGL (langTag .twistedE6) GGL), E ≤ ggFixGp .twistedE6 f →
      IsElemAbelian 3 E → Nat.card E = 3 ^ 4 → TwE6LawPos 3 f E

@[expose] def TwE6TTThreeUnitary : Prop :=
  ∀ (f : ℕ), 1 ≤ f → 9 ∣ 2 ^ f + 1 →
    ∀ E : Subgroup (ModGL (langTag .twistedE6) GGL), E ≤ ggFixGp .twistedE6 f →
      IsElemAbelian 3 E → Nat.card E = 3 ^ 5 → TwE6LawPos 3 f E

end Units

end CFSG.StandardType.LieKnownR2.ExcPos

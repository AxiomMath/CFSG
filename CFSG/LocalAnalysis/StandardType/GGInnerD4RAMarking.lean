module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GField
public import CFSG.LocalAnalysis.StandardType.GGTPNThmRABase

public section

namespace CFSG.StandardType.S2MathAs51600RAMarking

@[expose] def RAModelSelfMarking : Prop :=
  ∀ (lab : CFSG.Assembly.LargeEvenLabel),
    CFSG.Assembly.LargeEvenInLambda2 lab →
    (lab.tag = .A ∨ lab.tag = .twA) →
    CFSG.StandardType.LargeEvenLabelAll lab
      (CFSG.StandardType.LargeEvenSimpleGuard
        (fun R _ I _ => ∀ β ∈ I,
          CFSG.LocalAnalysis.GLTheoremA.Y10GField.InnDiagKind R lab β))

@[expose] def RASelectedMarking : Prop :=
  ∀ (X : Type) [Group X] (A : Subgroup (MulAut X)) (σ : MulAut X),
    σ ∈ A →
    CFSG.StandardType.LargeEvenMarking X
      (fun lab _ _ I _ θ => CFSG.StandardType.GGKacRA lab 3 ∧
        CFSG.StandardType.GGInducedInn A θ I) →
    CFSG.StandardType.LargeEvenMarking X
      (fun lab R _ I _ θ =>
        (CFSG.StandardType.GGKacRA lab 3 ∧
          CFSG.StandardType.GGInducedInn A θ I) ∧
        CFSG.LocalAnalysis.GLTheoremA.Y10GField.InnDiagKind R lab
          (CFSG.StandardType.ggInducedAut θ σ))

end CFSG.StandardType.S2MathAs51600RAMarking

end

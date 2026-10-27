module

public import CFSG.LocalAnalysis.StandardType.GGFrameTBInputs

public section

namespace CFSG.StandardType.FrameRoute

open CFSG CFSG.Assembly

@[expose] def frameTBBody (lab : LargeEvenLabel) : LargeEvenRawCont := fun R _ I _ =>
  ∀ r : ℕ, 6 ≤ r → frameTBRange lab r → GGTorusReflGenW 3 r R I ∧
    ∀ (L' : Type) [Group L'] [Finite L'] (ψ : L' →* R) (A : Subgroup (MulAut L')),
      GGTorusTBGroup 3 r R I L' ψ A →
        (FrameNumIs (ggAutomizer (MulAut.conj : L' →* MulAut L').range A) (frameLabNum lab).1
            (frameLabNum lab).2 ∧
          FrameConn (ggAutomizer (MulAut.conj : L' →* MulAut L').range A)) ∧
        ∃ S : Subgroup L', IsPGroup 3 S ∧ ¬ IsCyclic S

theorem ggFrameTBNumerologyInput_iff : GGFrameTBNumerologyInput ↔
    (∀ lab : LargeEvenLabel, LargeEvenInLambda2 lab → lab.n = 1 → frameTagTabled lab.tag →
      LargeEvenLabelAll lab (frameTBBody lab)) ∧
    ∀ lab : LargeEvenLabel, LargeEvenInLambda2 lab → lab.n = 1 → lab.tag = .E8 →
      LargeEvenLabelAll lab fun R _ _ _ => GGTorusLift 3 7 R :=
  Iff.rfl

end CFSG.StandardType.FrameRoute

end

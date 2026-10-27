module

public import CFSG.LocalAnalysis.StandardType.GGTypeANbrKnownDefs

public section

namespace CFSG.StandardType

open CFSG.Assembly TableB

@[expose] def GGNbrFrameInputOne : Prop :=
  ∀ p : ℕ, p.Prime → p ≠ 2 → ∀ lab : LargeEvenLabel, LargeEvenInLambda2 lab →
    GGFrameLabel p lab →
    LargeEvenLabelAll lab fun R _ I _ => ∃ r, GGTorusLift p r R ∧
      ∀ (L' : Type) [Group L'] [Finite L'] (ψ : L' →* R) (A : Subgroup (MulAut L')),
        GGTorusTBGroup p r R I L' ψ A → GGTorusFrame p A

end CFSG.StandardType

end

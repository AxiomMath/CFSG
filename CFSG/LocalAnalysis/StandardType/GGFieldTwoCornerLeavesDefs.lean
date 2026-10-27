module

public import CFSG.LocalAnalysis.StandardType.GGKD2Leaves1615

public section

namespace CFSG.StandardType

open CFSG.Assembly

@[expose] def GGCornerRemainingTypes : Prop :=
  ∀ lab : LargeEvenLabel, LargeEvenInLambda2 lab →
    LargeEvenLabelAll lab (fun R _ I _ =>
      ∀ (L' : Type) [Group L'] [Finite L'] (ψ : L' →* R), Function.Surjective ψ →
        ψ.ker ≤ Subgroup.center L' → commutator L' = ⊤ →
        ∀ (e : MulAut L') (J : Subgroup L') (a : MulAut L'),
          GGRankOneSetup I ψ 3 e J 3 a → S2MathAs3_1615.RemainingLab lab → False)

@[expose] def GGCornerE6 : Prop :=
  ∀ lab : LargeEvenLabel, LargeEvenInLambda2 lab →
    LargeEvenLabelAll lab (fun R _ I _ =>
      ∀ (L' : Type) [Group L'] [Finite L'] (ψ : L' →* R), Function.Surjective ψ →
        ψ.ker ≤ Subgroup.center L' → commutator L' = ⊤ →
        ∀ (e : MulAut L') (J : Subgroup L') (a : MulAut L'),
          GGRankOneSetup I ψ 3 e J 3 a → S2MathAs3_1615.E6Lab lab → False)

end CFSG.StandardType

end

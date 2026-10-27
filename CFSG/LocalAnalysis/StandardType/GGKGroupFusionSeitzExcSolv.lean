module

public import CFSG.LocalAnalysis.StandardType.GGKGroupFusionSeitzExcBasic

public section

namespace CFSG.StandardType

open CFSG.Assembly

@[expose] def GGSeitzExcUFourTwoInput : Prop :=
  ∀ (K : Type) [Group K] [Finite K] (d : TauCeti.ValidLieTypeIndex) (q : TauCeti.PrimePower),
    q.p = 2 → q.exponent = 1 → d.1 = .twistedA 3 q →
      Nonempty (K ≃* (TauCeti.CFSGIndex.lie d).Group) →
        ∀ X : Subgroup K, X ≠ ⊤ → ¬ 3 ∣ X.index → Group.IsSolvable ↥X

theorem ggKGroupFusionAt_uFourTwo
    (hSch : CFSG.LocalAnalysis.ComponentInitial.SchreierFor InCatalog)
    (hU : GGSeitzExcUFourTwoInput) : GGKGroupFusionAt GGKFSeitzUFourTwo :=
  ggKGroupFusionAt_of_solvable hSch fun _ _ ⟨hp, d, q, hi, hq2, hq1, hd⟩ K _ _ _ he _ hX h3 => by
    subst hp hi
    exact hU K d q hq2 hq1 hd he _ hX h3

end CFSG.StandardType

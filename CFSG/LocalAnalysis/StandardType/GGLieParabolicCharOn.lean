module

public import CFSG.LocalAnalysis.StandardType.GGKGroupFusionAltDefining

public section

namespace CFSG.StandardType

@[expose] def GGLieParabolicOpenIndex (d : TauCeti.ValidLieTypeIndex) : Prop :=
  match d.1 with
  | .A _ _ | .twistedA _ _ | .B _ _ | .C _ _ | .D _ _ | .twistedD _ _ | .reeG2 _ => True
  | _ => False

@[expose] def GGLieParabolicCharInputOn (P : TauCeti.ValidLieTypeIndex → Prop) : Prop :=
  ∀ (K : Type) [Group K] [Finite K] (d : TauCeti.ValidLieTypeIndex), P d →
    Nonempty (K ≃* (TauCeti.CFSGIndex.lie d).Group) → d.1.characteristic ≠ 2 →
      ∀ S X : Subgroup K, IsPGroup d.1.characteristic S → ¬ d.1.characteristic ∣ S.index →
        Subgroup.normalizer (S : Set K) ≤ X → X ≠ ⊤ → IsCharacteristicP d.1.characteristic ↥X

theorem ggLieParabolicCharInput_of_on {P : TauCeti.ValidLieTypeIndex → Prop}
    (h₁ : GGLieParabolicCharInputOn P) (h₂ : GGLieParabolicCharInputOn fun d => ¬ P d) :
    GGLieParabolicCharInput := by
  intro K _ _ d
  by_cases hd : P d
  · exact h₁ K d hd
  · exact h₂ K d hd

end CFSG.StandardType

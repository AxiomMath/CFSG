module

public import CFSG.Quasithin.Background.B5Statement
public import CFSG.Quasithin.Background.A4Defs

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin

@[expose] def FactKv12618 : Prop :=
  ∀ (Γ : Type) [Group Γ] [Finite Γ] (Y K T T₀ B : Subgroup Γ), K ≤ Y →
    Y ≤ Subgroup.normalizer (K : Set Γ) → IsSimpleGroup ↥K → B56QuasisimpleList ↥K →
    IsSylowTwoOf T Y → Y = K ⊔ T → pCoreOf 2 Y = ⊥ → B < K → T₀ ≤ T →
    T₀.relIndex T ≤ 4 → T₀ ≤ Subgroup.normalizer (B : Set Γ) → ⁅B, B⁆ = B →
    quasithinO2QuotientIso B ↥(alternatingGroup (Fin 6)) → ⁅pCoreOf 2 B, B⁆ = ⊥ →
      (IsAlt 7 ↥K ∧ ¬ 2 ∣ (Y ⊓ Subgroup.normalizer (B : Set Γ)).relIndex Y ∧
        centralizerSection T B (pCoreOf 2 B) = ⊥) ∨
      (IsAlt 8 ↥K ∧ T₀.relIndex T = 4)

end CFSG.Quasithin.H13

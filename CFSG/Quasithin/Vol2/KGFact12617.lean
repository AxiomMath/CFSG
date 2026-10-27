module

public import CFSG.Quasithin.Background.B5Statement
public import CFSG.Quasithin.Background.A4Defs

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin

@[expose] def FactKv12617 : Prop :=
  ∀ (Γ : Type) [Group Γ] [Finite Γ] (Y K T T₀ B R : Subgroup Γ), K ≤ Y →
    Y ≤ Subgroup.normalizer (K : Set Γ) → IsSimpleGroup ↥K → B56QuasisimpleList ↥K →
    IsSylowTwoOf T Y → Y = K ⊔ T → pCoreOf 2 Y = ⊥ → B < K → T₀ ≤ T →
    T₀.relIndex T ≤ 4 → T₀ ≤ Subgroup.normalizer (B : Set Γ) → ⁅B, B⁆ = B →
    quasithinO2QuotientIso B ↥(alternatingGroup (Fin 6)) → R ≠ ⊥ →
    R ≤ centralizerSection T B (pCoreOf 2 B) → T₀ ≤ Subgroup.normalizer (R : Set Γ) →
    K ⊓ Subgroup.normalizer (R : Set Γ) ≤ Subgroup.normalizer (B : Set Γ) →
      T₀.relIndex T = 4 ∧ ∃ e : ↥Y ≃* Equiv.Perm (Fin 8),
        (K.subgroupOf Y).map e.toMonoidHom = alternatingGroup (Fin 8) ∧
        (R.subgroupOf Y).map e.toMonoidHom = Subgroup.zpowers (Equiv.swap 0 1)

end CFSG.Quasithin.H13

module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.QuasithinUnique.Defs
public import CFSG.Open.QuasithinDefs
public import CFSG.Quasithin.Background.A1cModuleDefs
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.Assembly.LowTwoRank

@[expose] def FactKv12618LieFam : Prop :=
  ∀ (Γ : Type) [Group Γ] [Finite Γ] (Y K T T₀ B : Subgroup Γ), K ≤ Y →
    Y ≤ Subgroup.normalizer (K : Set Γ) → IsSimpleGroup ↥K →
    ((∃ (n : ℕ) (F : Type) (_ : Field F) (_ : Finite F), 2 ≤ n ∧ Nat.card F = 2 ^ n ∧
        Nonempty (↥K ≃* ↥(Assembly.LowTwoRank.StatedSp 2 F))) ∨
      (∃ (n : ℕ) (F : Type) (_ : Field F) (_ : Finite F), 2 ≤ n ∧ Even n ∧ Nat.card F = 2 ^ n ∧
        Nonempty (↥K ≃* ↥(CFSG.Open.quasithinG2 F)))) →
    IsSylowTwoOf T Y → Y = K ⊔ T → pCoreOf 2 Y = ⊥ → B < K → T₀ ≤ T →
    T₀.relIndex T ≤ 4 → T₀ ≤ Subgroup.normalizer (B : Set Γ) → ⁅B, B⁆ = B →
    quasithinO2QuotientIso B ↥(alternatingGroup (Fin 6)) → ⁅pCoreOf 2 B, B⁆ = ⊥ → False

@[expose] def FactKv12618L52 : Prop :=
  ∀ (B T₀ : Subgroup ↥(Assembly.LowTwoRank.StatedSL 5 (ZMod 2))), ⁅B, B⁆ = B →
    quasithinO2QuotientIso B ↥(alternatingGroup (Fin 6)) → ⁅pCoreOf 2 B, B⁆ = ⊥ →
    IsPGroup 2 ↥T₀ → 2 ^ 8 ≤ Nat.card ↥T₀ → T₀ ≤ Subgroup.normalizer (B : Set _) → False

end CFSG.Quasithin.H13

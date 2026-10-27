module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Quasithin.Background.A4Defs
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin

@[expose] def Conf12617 {Γ : Type} [Group Γ] (Y K T T₀ B R : Subgroup Γ) : Prop :=
  K ≤ Y ∧ Y ≤ Subgroup.normalizer (K : Set Γ) ∧ IsSimpleGroup ↥K ∧ IsSylowTwoOf T Y ∧
    Y = K ⊔ T ∧ pCoreOf 2 Y = ⊥ ∧ B < K ∧ T₀ ≤ T ∧ T₀.relIndex T ≤ 4 ∧
    T₀ ≤ Subgroup.normalizer (B : Set Γ) ∧ ⁅B, B⁆ = B ∧
    quasithinO2QuotientIso B ↥(alternatingGroup (Fin 6)) ∧ R ≠ ⊥ ∧
    R ≤ centralizerSection T B (pCoreOf 2 B) ∧ T₀ ≤ Subgroup.normalizer (R : Set Γ) ∧
    K ⊓ Subgroup.normalizer (R : Set Γ) ≤ Subgroup.normalizer (B : Set Γ)

@[expose] def FactKv12617LieFam : Prop :=
  ∀ (Γ : Type) [Group Γ] [Finite Γ] (Y K T T₀ B R : Subgroup Γ), Conf12617 Y K T T₀ B R →
    ((∃ (n : ℕ) (F : Type) (_ : Field F) (_ : Finite F), 2 ≤ n ∧ Nat.card F = 2 ^ n ∧
        Nonempty (↥K ≃* ↥(Assembly.LowTwoRank.StatedSp 2 F))) ∨
      (∃ (n : ℕ) (F : Type) (_ : Field F) (_ : Finite F), 2 ≤ n ∧ Even n ∧ Nat.card F = 2 ^ n ∧
        Nonempty (↥K ≃* ↥(CFSG.Open.quasithinG2 F)))) → False

@[expose] def FactKv12617L52 : Prop :=
  ∀ (Γ : Type) [Group Γ] [Finite Γ] (Y K T T₀ B R : Subgroup Γ), Conf12617 Y K T T₀ B R →
    Nonempty (↥K ≃* ↥(Assembly.LowTwoRank.StatedSL 5 (ZMod 2))) → False

@[expose] def FactKv12617A8 : Prop :=
  ∀ (Γ : Type) [Group Γ] [Finite Γ] (Y K T T₀ B R : Subgroup Γ), Conf12617 Y K T T₀ B R →
    Nonempty (↥K ≃* ↥(Assembly.LowTwoRank.StatedSL 4 (ZMod 2))) →
      T₀.relIndex T = 4 ∧ ∃ e : ↥Y ≃* Equiv.Perm (Fin 8),
        (K.subgroupOf Y).map e.toMonoidHom = alternatingGroup (Fin 8) ∧
        (R.subgroupOf Y).map e.toMonoidHom = Subgroup.zpowers (Equiv.swap 0 1)

end CFSG.Quasithin.H13

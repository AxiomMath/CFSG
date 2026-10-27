module

public import CFSG.Quasithin.Vol2.Ch5Sec2LocalLem522

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin

@[expose] def Stmt5_2_2_bot_D4 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M L V H B D L₂ Dp : Subgroup G) (n : ℕ),
    Hyp5_2_2p G T M L V H B D L₂ Dp n 3 → pCoreOf 2 (Dp ⊔ (L₂ ⊔ sec52S M H)) = ⊥ →
    Nonempty (oTwoQuot ↥(Dp ⊔ sec52S M H) ≃* Equiv.Perm (Fin 3)) →
    Hyp111 L₂ (Dp ⊔ sec52S M H) (sec52S M H) →
    (centerOf (sec52S M H) ≤ Subgroup.centralizer (L₂ : Set G) ∨
        centerOf (sec52S M H) ≤ Subgroup.centralizer ((Dp ⊔ sec52S M H : Subgroup G) : Set G) →
      centerOf (sec52S M H) ≤ Subgroup.centralizer (L₂ : Set G)) →
    IsAmalgamOfGroup (RankTwoAmalgam.ofSubgroups
        (L₂ ⊔ bigB L₂ (Dp ⊔ sec52S M H) (sec52S M H))
        ((Dp ⊔ sec52S M H) ⊔ bigB L₂ (Dp ⊔ sec52S M H) (sec52S M H)))
      (IsLieOverTwo .trialityD4 0 1) →
    IsL2Quot 3 (oTwoQuot ↥L₂) → IsSpecialPow 2 2 4 ↥(pCoreOf 2 L₂) →
    Nat.card ↥(pCoreOf 2 (Dp ⊔ sec52S M H)) = 2 ^ 11 → False

@[expose] def Stmt5_2_2_bot_J2 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M L V H B D L₂ Dp : Subgroup G) (n : ℕ),
    Hyp5_2_2p G T M L V H B D L₂ Dp n 3 → pCoreOf 2 (Dp ⊔ (L₂ ⊔ sec52S M H)) = ⊥ →
    Nonempty (oTwoQuot ↥(Dp ⊔ sec52S M H) ≃* Equiv.Perm (Fin 3)) →
    Hyp111 L₂ (Dp ⊔ sec52S M H) (sec52S M H) →
    (centerOf (sec52S M H) ≤ Subgroup.centralizer (L₂ : Set G) ∨
        centerOf (sec52S M H) ≤ Subgroup.centralizer ((Dp ⊔ sec52S M H : Subgroup G) : Set G) →
      centerOf (sec52S M H) ≤ Subgroup.centralizer (L₂ : Set G)) →
    IsParabolicAmalgamOfGroup (RankTwoAmalgam.ofSubgroups
        (L₂ ⊔ bigB L₂ (Dp ⊔ sec52S M H) (sec52S M H))
        ((Dp ⊔ sec52S M H) ⊔ bigB L₂ (Dp ⊔ sec52S M H) (sec52S M H)))
      (fun Y _ => Nonempty (Y ≃* quasithinJ2)) →
    IsL2Quot 2 (oTwoQuot ↥L₂) → IsQ8D8 ↥(pCoreOf 2 L₂) →
    Nat.card ↥(pCoreOf 2 (Dp ⊔ sec52S M H)) = 2 ^ 6 → False

@[expose] def Stmt5_2_2_bot_U4 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M L V H B D L₂ Dp : Subgroup G) (n : ℕ),
    Hyp5_2_2p G T M L V H B D L₂ Dp n 3 → pCoreOf 2 (Dp ⊔ (L₂ ⊔ sec52S M H)) = ⊥ →
    Nonempty (oTwoQuot ↥(Dp ⊔ sec52S M H) ≃* Equiv.Perm (Fin 3)) →
    Hyp111 (Dp ⊔ sec52S M H) L₂ (sec52S M H) →
    (centerOf (sec52S M H) ≤ Subgroup.centralizer (L₂ : Set G) ∨
        centerOf (sec52S M H) ≤ Subgroup.centralizer ((Dp ⊔ sec52S M H : Subgroup G) : Set G) →
      centerOf (sec52S M H) ≤
        Subgroup.centralizer ((Dp ⊔ sec52S M H : Subgroup G) : Set G)) →
    (IsAmalgamOfGroup (RankTwoAmalgam.ofSubgroups
          ((Dp ⊔ sec52S M H) ⊔ bigB (Dp ⊔ sec52S M H) L₂ (sec52S M H))
          (L₂ ⊔ bigB (Dp ⊔ sec52S M H) L₂ (sec52S M H)))
        (IsLieOverTwo .PSU 4 1) ∨
      IsU4ExtTwo 1 (RankTwoAmalgam.ofSubgroups
        ((Dp ⊔ sec52S M H) ⊔ bigB (Dp ⊔ sec52S M H) L₂ (sec52S M H))
        (L₂ ⊔ bigB (Dp ⊔ sec52S M H) L₂ (sec52S M H)))) →
    IsSpecialPow 2 2 2 ↥(pCoreOf 2 (Dp ⊔ sec52S M H)) → IsBlock2 L₂ L₂ →
    IsL2Quot 2 (oTwoQuot ↥L₂) → IsOmega4MinusType L₂ 1 → IsAltType L₂ 5 → False

end CFSG.Quasithin.H13

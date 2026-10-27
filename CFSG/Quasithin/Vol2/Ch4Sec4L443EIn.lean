module

public import CFSG.Quasithin.Vol2.Ch4Sec4W443

public section

namespace CFSG.Quasithin.H13.Ch4.E443

open CFSG.Open CFSG.Quasithin CFSG.Blueprint CFSG.QuasithinUnique
open scoped IsMulCommutative

@[expose] def Shape443 (X : Type) [Group X] : Prop :=
  (∃ n : ℕ, 2 ≤ n ∧ LieModel X .PSL 2 2 n) ∨ LieModel X .PSL 3 2 1 ∨ LieModel X .PSL 4 2 1 ∨
    Nonempty (X ≃* alternatingGroup (Fin 6)) ∨ Nonempty (X ≃* alternatingGroup (Fin 7)) ∨
    (Group.IsPerfect X ∧ Nat.card (Subgroup.center X) = 3 ∧
      Nonempty (X ⧸ Subgroup.center X ≃* alternatingGroup (Fin 6))) ∨
    LieModel X .PSU 3 3 1

@[expose] def Concl443B (G : Type) [Group G] (T M L K LB VB : Subgroup G) : Prop :=
  (CFSG.IsQuasisimple (↥LB ⧸ CFSG.pCore 2 ↥LB) ∧ Shape443 (↥LB ⧸ CFSG.pCore 2 ↥LB) ∧
    (((∃ _ : IsMulCommutative ↥VB,
          IsFFModule (V := ↥VB) (autOn (M ⊓ Subgroup.normalizer (VB : Set G)) VB)) ∧
        (LieModel (↥LB ⧸ CFSG.pCore 2 ↥LB) .PSL 3 2 1 → IsNaturalSumUnder 3 LB VB) ∧
        (LieModel (↥LB ⧸ CFSG.pCore 2 ↥LB) .PSL 4 2 1 →
          IsNaturalSumUnder 4 LB VB ∨
            ∃ _ : IsMulCommutative ↥VB, SLExteriorTwo (V := ↥VB) (autOn LB VB) ⊤ ⊥ 4) ∧
        ((Group.IsPerfect (↥LB ⧸ CFSG.pCore 2 ↥LB) ∧
            Nat.card (Subgroup.center (↥LB ⧸ CFSG.pCore 2 ↥LB)) = 3 ∧
            Nonempty ((↥LB ⧸ CFSG.pCore 2 ↥LB) ⧸ Subgroup.center (↥LB ⧸ CFSG.pCore 2 ↥LB) ≃*
              alternatingGroup (Fin 6))) →
          ∀ z ∈ VB ⊓ Subgroup.centralizer ((T ⊓ conjClosure L T : Subgroup G) : Set G),
            orderOf z = 2 →
            ¬ VB ≤ pCoreOf 2 (K ⊓ Subgroup.centralizer ({z} : Set G))) ∧
        (LieModel (↥LB ⧸ CFSG.pCore 2 ↥LB) .PSU 3 3 1 → Nat.card VB = 2 ^ 6 →
          ∃ V₃ : Subgroup G, V₃ ≤ VB ∧ Nat.card V₃ = 2 ^ 3 ∧
            T ⊓ conjClosure L T ≤ Subgroup.normalizer (V₃ : Set G) ∧
              ¬ K ⊓ Subgroup.centralizer (V₃ : Set G) ≤ M)) ∨
      (∃ m : ℕ, 1 ≤ m ∧ LieModel (↥LB ⧸ CFSG.pCore 2 ↥LB) .PSL 2 2 (2 * m) ∧
        ∃ _ : IsMulCommutative ↥VB, BinaryOrthogonalFour (V := ↥VB) (autOn LB VB) ⊤ ⊥ m) ∨
      (LieModel (↥LB ⧸ CFSG.pCore 2 ↥LB) .PSL 3 2 1 ∧
        ∃ _ : IsMulCommutative ↥VB, FanoCoreModule (V := ↥VB) (autOn LB VB) ⊤ ⊥))) ∨
  (IsSporadic .J4 ↥K ∧
    (IsSporadic .M24 (↥LB ⧸ CFSG.pCore 2 ↥LB) ∨ LieModel (↥LB ⧸ CFSG.pCore 2 ↥LB) .PSL 5 2 1))

@[expose] def Insp443 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M L B Tp VB K : Subgroup G),
    H13.Ch4.Setting443 G T M L B Tp VB →
    IsUniqueM (perfectCore (conjClosure L T ⊓ Subgroup.centralizer (B : Set G)) ⊔
      (Tp ⊓ Subgroup.normalizer (B : Set G))) M →
    oddCoreIn (Subgroup.normalizer (B : Set G)) ≤ M ⊓ Subgroup.normalizer (B : Set G) →
    K ≤ Subgroup.normalizer (B : Set G) →
    Subgroup.normalizer (B : Set G) ≤ Subgroup.normalizer (K : Set G) →
    CFSG.IsQuasisimple ↥K → ¬ K ≤ M → VB ≤ K →
    perfectCore (conjClosure L T ⊓ Subgroup.centralizer (B : Set G)) ≤ K →
    Subgroup.normalizer (B : Set G) ⊓ Subgroup.centralizer (K : Set G) =
      oddCoreIn (Subgroup.normalizer (B : Set G)) →
    Concl443B G T M L K (perfectCore (conjClosure L T ⊓ Subgroup.centralizer (B : Set G))) VB

@[expose] def Gap443J4 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M L B Tp VB K : Subgroup G),
    H13.Ch4.Setting443 G T M L B Tp VB →
    IsUniqueM (perfectCore (conjClosure L T ⊓ Subgroup.centralizer (B : Set G)) ⊔
      (Tp ⊓ Subgroup.normalizer (B : Set G))) M →
    oddCoreIn (Subgroup.normalizer (B : Set G)) ≤ M ⊓ Subgroup.normalizer (B : Set G) →
    K ≤ Subgroup.normalizer (B : Set G) →
    Subgroup.normalizer (B : Set G) ≤ Subgroup.normalizer (K : Set G) →
    CFSG.IsQuasisimple ↥K → ¬ K ≤ M → VB ≤ K →
    perfectCore (conjClosure L T ⊓ Subgroup.centralizer (B : Set G)) ≤ K →
    Subgroup.normalizer (B : Set G) ⊓ Subgroup.centralizer (K : Set G) =
      oddCoreIn (Subgroup.normalizer (B : Set G)) →
    IsSporadic .J4 ↥K →
    (IsSporadic .M24 (↥(perfectCore (conjClosure L T ⊓ Subgroup.centralizer (B : Set G))) ⧸
        CFSG.pCore 2 ↥(perfectCore (conjClosure L T ⊓ Subgroup.centralizer (B : Set G)))) ∨
      LieModel (↥(perfectCore (conjClosure L T ⊓ Subgroup.centralizer (B : Set G))) ⧸
        CFSG.pCore 2 ↥(perfectCore (conjClosure L T ⊓ Subgroup.centralizer (B : Set G))))
        .PSL 5 2 1) → False

end CFSG.Quasithin.H13.Ch4.E443

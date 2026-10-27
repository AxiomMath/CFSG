module

public import CFSG.Quasithin.Vol2.Ch4Sec4HypPrime
public import CFSG.Quasithin.Background.B2FactorizationResidual

public section

namespace CFSG.Quasithin.Vol2.Ch11

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13
open scoped IsMulCommutative Pointwise

@[expose] def Concl4_4_3 {G : Type} [Group G] (T M L B VB : Subgroup G) : Prop :=
  Subgroup.normalizer (B : Set G) ≤ M ∨
  (M ≤ Subgroup.normalizer (L : Set G) ∧
    ((∃ n : ℕ, 2 ≤ n ∧ LieModel (↥L ⧸ CFSG.pCore 2 ↥L) .PSL 2 2 n) ∨
      LieModel (↥L ⧸ CFSG.pCore 2 ↥L) .PSL 3 2 1 ∨
      LieModel (↥L ⧸ CFSG.pCore 2 ↥L) .PSL 4 2 1 ∨
      Nonempty (↥L ⧸ CFSG.pCore 2 ↥L ≃* alternatingGroup (Fin 6)) ∨
      Nonempty (↥L ⧸ CFSG.pCore 2 ↥L ≃* alternatingGroup (Fin 7)) ∨
      (Group.IsPerfect (↥L ⧸ CFSG.pCore 2 ↥L) ∧
        Nat.card (Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L)) = 3 ∧
        Nonempty ((↥L ⧸ CFSG.pCore 2 ↥L) ⧸ Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L) ≃*
          alternatingGroup (Fin 6))) ∨
      LieModel (↥L ⧸ CFSG.pCore 2 ↥L) .PSU 3 3 1) ∧
    (((∃ _ : IsMulCommutative ↥VB, IsFFModule (V := ↥VB) (autOn (L ⊔ T) VB)) ∧
        (LieModel (↥L ⧸ CFSG.pCore 2 ↥L) .PSL 3 2 1 → IsNaturalSumUnder 3 L VB) ∧
        (LieModel (↥L ⧸ CFSG.pCore 2 ↥L) .PSL 4 2 1 →
          IsNaturalSumUnder 4 L VB ∨
            ∃ _ : IsMulCommutative ↥VB, SLExteriorTwo (V := ↥VB) (autOn L VB) ⊤ ⊥ 4) ∧
        ((Group.IsPerfect (↥L ⧸ CFSG.pCore 2 ↥L) ∧
            Nat.card (Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L)) = 3 ∧
            Nonempty ((↥L ⧸ CFSG.pCore 2 ↥L) ⧸ Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L) ≃*
              alternatingGroup (Fin 6))) → Nat.card VB = 2 ^ 6 →
          ∀ z ∈ VB ⊓ Subgroup.centralizer ((T ⊓ L : Subgroup G) : Set G), orderOf z = 2 →
            ¬ VB ≤ pCoreOf 2 (Subgroup.centralizer ({z} : Set G))) ∧
        (LieModel (↥L ⧸ CFSG.pCore 2 ↥L) .PSU 3 3 1 → Nat.card VB = 2 ^ 6 →
          ∃ V₃ : Subgroup G, V₃ ≤ VB ∧ Nat.card V₃ = 2 ^ 3 ∧
            T ⊓ L ≤ Subgroup.normalizer (V₃ : Set G) ∧
              ¬ Subgroup.centralizer (V₃ : Set G) ≤ M)) ∨
      (∃ m : ℕ, 1 ≤ m ∧ LieModel (↥L ⧸ CFSG.pCore 2 ↥L) .PSL 2 2 (2 * m) ∧
        ∃ _ : IsMulCommutative ↥VB, BinaryOrthogonalFour (V := ↥VB) (autOn L VB) ⊤ ⊥ m) ∨
      (LieModel (↥L ⧸ CFSG.pCore 2 ↥L) .PSL 3 2 1 ∧
        ∃ _ : IsMulCommutative ↥VB, FanoCoreModule (V := ↥VB) (autOn L VB) ⊤ ⊥)))

theorem stmt4_4_3_iff : Stmt4_4_3' ↔
  (∀ (G : Type) [Group G] [Finite G] (T M L B Tp VB : Subgroup G), IsSimpleGroup G →
      (∃ a b : G, a * b ≠ b * a) → QuasithinUnique.quasithinIsQTKECat G →
      quasithinIsSylowTwo T → quasithinIsMaxTwoLocal M → T ≤ M →
      quasithinIsMaximalLocal T L → quasithinIsFaithfulLocal T L → L ≤ M →
      CFSG.IsQuasisimple (↥L ⧸ CFSG.pCore 2 ↥L) →
      B ≤ M → B ≠ ⊥ → IsMulCommutative ↥B → Odd (Nat.card B) →
      ⁅conjClosure L T, B⁆ ≤ pCoreOf 2 (conjClosure L T) →
      Tp ≤ T → (B : Set G) * (Tp : Set G) = (Tp : Set G) * (B : Set G) →
      (L : Set G) * (T : Set G) = (L : Set G) * (Tp : Set G) →
      VB ≤ quasithinOmegaOneCenter (pCoreOf 2 (conjClosure L T ⊔ T)) →
      conjClosure L T ⊔ T ≤ Subgroup.normalizer (VB : Set G) →
      VB = ⁅VB, conjClosure L T⁆ → VB ≠ ⊥ → ⁅VB, B⁆ = ⊥ →
        Concl4_4_3 T M L B VB) :=
  Iff.rfl

@[expose] def TmpL4_4_2 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M L B V : Subgroup G), IsSimpleGroup G →
    (∃ a b : G, a * b ≠ b * a) → QuasithinUnique.quasithinIsQTKECat G →
    quasithinIsSylowTwo T → quasithinIsMaxTwoLocal M → T ≤ M →
    quasithinIsMaximalLocal T L → quasithinIsFaithfulLocal T L → L ≤ M →
    CFSG.IsQuasisimple (↥L ⧸ CFSG.pCore 2 ↥L) → M ≤ Subgroup.normalizer (L : Set G) →
    V ≤ L ⊔ T → IsPrimeReduced 2 (V.subgroupOf (L ⊔ T)) → V = ⁅V, L⁆ → V ≠ ⊥ →
    B ≤ M ⊓ Subgroup.centralizer (V : Set G) → B ≠ ⊥ → IsMulCommutative ↥B →
    Odd (Nat.card B) → Concl4_4_3 T M L B V

end CFSG.Quasithin.Vol2.Ch11

module

public import CFSG.RankThree.PartTwo.KFacts.AutKindsStd

public section

namespace CFSG.RankThree.PartTwo.Sec4

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.KFacts
open CFSG.Assembly.RankThreeEven (projSU projSp)
open CFSG.Blueprint

section Item419

@[expose] def Item4_19NJ3 : Prop :=
  ∀ (G : Type) [Group G] [Finite G], SectionFourHyp G →
    ∀ L : Subgroup G, IsComponent L →
    ∀ (A : Subgroup G) (c : G), Maximal (fun B : Subgroup G => CFSG.Assembly.IsElemAbelian 3 B) A →
      Nat.card A = 3 ^ 4 → A ⊓ Subgroup.centralizer (L : Set G) = Subgroup.zpowers c →
      orderOf c = 3 →
    ∀ a ∈ A, a ∉ Subgroup.zpowers c →
    ∀ K : Subgroup G, K ≤ L ⊓ Subgroup.centralizer ({a} : Set G) →
      IsComponent (K.subgroupOf (L ⊓ Subgroup.centralizer ({a} : Set G))) →
      ((∃ n : ℕ, ChevalleyExceptionalModel ↥K .G2 2 n) ∨ Nonempty (K ≃* projSU 3 3 1) ∨
        (∃ n : ℕ, ReeTitsModel ↥K .twistedF4 2 n) ∨ ReeTitsModel ↥K .Tits 2 1 ∨
        (∃ n : ℕ, 2 ≤ n ∧ Nonempty (K ≃* projSp 2 (GaloisField 2 n))) ∨
        Nonempty (K ≃* alternatingGroup (Fin 6)) ∨
        (∃ m : ℕ, Odd m ∧ Nonempty (K ≃* projSU 3 2 m))) →
      (∀ A₀ ∈ partTwoF G, Nat.card A₀ ≤ 3 ^ 4) →
        (InducesStdKind L a .field ∨ InducesStdKind L a .graphField) ∨
        (Nonempty (K ≃* alternatingGroup (Fin 6)) ∧
          (Nonempty (L ≃* alternatingGroup (Fin 9)) ∨
            Nonempty (L ≃* projSp 3 (GaloisField 2 1)))) ∨
        (Nonempty (K ≃* alternatingGroup (Fin 6)) ∧
          Nonempty (L ⧸ Subgroup.center L ≃* NativeSporadic.J3))

@[expose] def Item4_19NUnitary : Prop :=
  ∀ (G : Type) [Group G] [Finite G], SectionFourHyp G →
    ∀ L : Subgroup G, IsComponent L →
    ∀ (A : Subgroup G) (c : G), Maximal (fun B : Subgroup G => CFSG.Assembly.IsElemAbelian 3 B) A →
      Nat.card A = 3 ^ 4 → A ⊓ Subgroup.centralizer (L : Set G) = Subgroup.zpowers c →
      orderOf c = 3 →
    ∀ a ∈ A, a ∉ Subgroup.zpowers c →
    ∀ K : Subgroup G, K ≤ L ⊓ Subgroup.centralizer ({a} : Set G) →
      IsComponent (K.subgroupOf (L ⊓ Subgroup.centralizer ({a} : Set G))) →
      (∃ m : ℕ, Odd m ∧ Nonempty (K ≃* projSU 3 2 m)) →
      (∀ A₀ ∈ partTwoF G, Nat.card A₀ ≤ 3 ^ 4) →
        InducesStdKind L a .field ∨ InducesStdKind L a .graphField

end Item419

namespace Res4Three419

theorem card_alternatingGroup_six : Nat.card (alternatingGroup (Fin 6)) = 360 := by
  rw [Nat.card_eq_fintype_card, card_alternatingGroup, Fintype.card_fin]
  decide

end Res4Three419

open Res4Three419

end CFSG.RankThree.PartTwo.Sec4

module

public import CFSG.Quasithin.EmptyFaithful.S1421F112

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique

@[expose] def F112L24G2NoNatural : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L1 L2 S : Subgroup G), Hyp111 L1 L2 S →
    IsQuasithinSub (L1 ⊔ L2 ⊔ S) →
    ((S.subgroupOf (S ⊔ borelOf L1 S)).Normal ∨ (S.subgroupOf (S ⊔ borelOf L2 S)).Normal) →
    Nat.card (oTwoQuot ↥L1) = 60 → Nat.card (oTwoQuot ↥L2) = 60 →
    (¬ IsShort2 L1 ∨ ¬ IsShort2 L2) →
    ∀ K V A B : Subgroup G, K ≤ L1 ⊔ bigB L1 L2 S →
      L1 ⊔ bigB L1 L2 S ≤ Subgroup.normalizer (K : Set G) → ⁅K, K⁆ = K →
      (∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = 4 ∧
        Nonempty (↥K ⧸ CFSG.pCore 2 ↥K ≃* Matrix.SpecialLinearGroup (Fin 2) F)) →
      V ≤ L1 ⊔ bigB L1 L2 S → L1 ⊔ bigB L1 L2 S ≤ Subgroup.normalizer (V : Set G) →
      Nat.card ↥V = 4 → K ≤ Subgroup.centralizer (V : Set G) →
      A ≤ B → B ≤ pCoreOf 2 (L1 ⊔ bigB L1 L2 S) → B ≤ Subgroup.normalizer (A : Set G) →
      K ≤ Subgroup.normalizer (A : Set G) → K ≤ Subgroup.normalizer (B : Set G) → A ≠ B →
      ∀ y ∈ K, orderOf y = 3 → ∃ b ∈ B, b ∉ A ∧ y * b * y⁻¹ * b⁻¹ ∈ A

end CFSG.Quasithin

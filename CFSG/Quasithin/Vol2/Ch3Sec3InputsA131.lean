module

public import CFSG.Foundations.Basic

public section

namespace CFSG.Quasithin.ASInputs

@[expose] def AS_A_1_31 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ), p.Prime → p ≠ 2 → CFSG.pRank p G ≤ 2 →
    ∀ (H : Subgroup G) [H.Normal],
      CFSG.generalizedFitting (G ⧸ H) = CFSG.pCore p (G ⧸ H) →
      (∀ S : Subgroup (G ⧸ H), IsPGroup 2 S → S ≠ ⊥ →
        IsCyclic ↥(CFSG.pCore p (G ⧸ H) ⊓ Subgroup.centralizer (S : Set (G ⧸ H)))) ∧
      CFSG.pRank 2 (G ⧸ H) ≤ 2 ∧
      (CFSG.IsElementaryAbelian p ↥(CFSG.pCore p (G ⧸ H)) →
        Nat.card ↥(CFSG.pCore p (G ⧸ H)) = p ^ 3 → 1 < CFSG.pRank 2 (G ⧸ H) →
          ∃ K : Subgroup (G ⧸ H), K.Normal ∧ ⊥ < K ∧ K < CFSG.pCore p (G ⧸ H))

end CFSG.Quasithin.ASInputs

module

public import CFSG.LocalAnalysis.UniquenessCase.UC22Defs

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

@[expose] def Asc80ThmB : Prop :=
  ∀ {G : Type} [Group G] [Finite G] (H A M : Subgroup G),
    IsSimpleGroup ↥(Fstar H) → (∃ a b : ↥(Fstar H), a * b ≠ b * a) →
    IsCatalogGroup ↥(Fstar H) → A ≤ H → IsElemAbelian 2 A → maxOver H A = {M} →
    (∃ n, IsL2 ↥H n ∨ IsSz ↥H n) ∧
      ∃ T : Subgroup G, IsSylowIn 2 T H ∧ M = H ⊓ normalizer (T : Set G)

@[expose] def R3_1 : Prop :=
  ∀ (n : ℕ), 4 < n → ∀ (H T K : Subgroup (Equiv.Perm (Fin n))),
    alternatingGroup (Fin n) ≤ H → IsSylowIn 2 T ⊤ →
    H ⊓ Subgroup.setNormalizer {t : Equiv.Perm (Fin n) | t ∈ T ∧ t.IsSwap} ≤ K → K ≤ H →
      K = H ∨
      K = H ⊓ Subgroup.setNormalizer {t : Equiv.Perm (Fin n) | t ∈ T ∧ t.IsSwap} ∨
      (Odd n ∧ ∃ α : Fin n, (∀ t ∈ T, t.IsSwap → t α = α) ∧
        K = H ⊓ MulAction.stabilizer (Equiv.Perm (Fin n)) α) ∨
      (Nonempty (↥H ≃* alternatingGroup (Fin 7)) ∧ IsL3 ↥K 1) ∨
      ((Nonempty (↥H ≃* alternatingGroup (Fin 8)) ∨ Nonempty (↥H ≃* alternatingGroup (Fin 9))) ∧
        ∃ (E : Subgroup (Equiv.Perm (Fin n))) (_ : (E.subgroupOf K).Normal),
          E ≤ K ∧ IsElemAbelian 2 E ∧ Nat.card E = 8 ∧ IsL3 (↥K ⧸ E.subgroupOf K) 1)

end CFSG.LocalAnalysis.WeakClosure81

module

public import CFSG.Quasithin.Recognition.GoldschmidtBasic

public section

namespace CFSG.Quasithin.Fan86

@[expose] def Sigma3PushingUp : Prop :=
  ∀ (H : Type) [Group H] [Finite H] (S : Subgroup H),
    Nonempty (H ⧸ CFSG.Open.pCore 2 H ≃* Equiv.Perm (Fin 3)) → IsPGroup 2 S →
    Nat.card H = 3 * Nat.card S →
    (∀ K : Subgroup H, K ≤ S → (K.subgroupOf S).Characteristic → K.Normal → K = ⊥) →
    (∃ T E : Subgroup H, Nonempty (↥T ≃* Equiv.Perm (Fin 3)) ∧ CFSG.Open.IsElemAbelian 2 E ∧
        (∀ t ∈ T, ∀ e ∈ E, t * e = e * t) ∧ T ⊓ E = ⊥ ∧ T ⊔ E = ⊤) ∨
    (∃ T C : Subgroup H, Nonempty (↥T ≃* Equiv.Perm (Fin 4)) ∧ IsPGroup 2 C ∧
        (∀ t ∈ T, ∀ c ∈ C, t * c = c * t) ∧ T ⊓ C = ⊥ ∧ T ⊔ C = ⊤)

@[expose] def Sigma3Aut : Prop :=
  ∀ (H : Type) [Group H] [Finite H] (S : Subgroup H) (x : H) (f : ↥S ≃* ↥S) (q : ℕ),
    Nonempty (H ⧸ CFSG.Open.pCore 2 H ≃* Equiv.Perm (Fin 3)) → IsPGroup 2 S →
    Nat.card H = 3 * Nat.card S → orderOf x = 3 → q.Prime → q ≠ 2 → orderOf f = q →
    (∀ K : Subgroup H, K ≤ S → (∀ s : ↥S, (s : H) ∈ K → ((f s : ↥S) : H) ∈ K) → K.Normal →
      K = ⊥) →
    (Subgroup.zpowers x).Normal

end CFSG.Quasithin.Fan86

module

public import CFSG.LocalAnalysis.WeakClosure81.W183Abs4
public import CFSG.LocalAnalysis.WeakClosure81.EightEightDefs

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.QuasithinUnique Subgroup
open CFSG.LocalAnalysis.UniquenessCase.UC22 (IsL2 IsL3 IsU3 IsAlt)

@[expose] def FinL32 : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (L : Subgroup Y), L.Normal → IsL3 ↥L 1 →
    Subgroup.centralizer (L : Set Y) = ⊥ → (∃ τ : Y, ActsOnDynkinMod ⊥ L τ) →
      ∀ A : Subgroup Y, Nat.card A = 4 → IsElemAbelian 2 A → ¬ IsTISub Y A

@[expose] def FinA6 : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (L : Subgroup Y), L.Normal → IsAlt ↥L 6 →
    Subgroup.centralizer (L : Set Y) = ⊥ → (∃ τ : Y, ActsOnDynkinMod ⊥ L τ) →
      ∀ A : Subgroup Y, Nat.card A = 4 → IsElemAbelian 2 A → ¬ IsTISub Y A

@[expose] def FinA5 : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (L : Subgroup Y), L.Normal → IsL2 ↥L 2 →
    Subgroup.centralizer (L : Set Y) = ⊥ →
      ∀ A : Subgroup Y, Nat.card A = 4 → IsElemAbelian 2 A → IsTISub Y A → IsSylowIn 2 A L

@[expose] def FinU34 : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (L : Subgroup Y), L.Normal → IsU3 ↥L 2 →
    Subgroup.centralizer (L : Set Y) = ⊥ →
      ∀ A : Subgroup Y, Nat.card A = 4 → IsElemAbelian 2 A → IsTISub Y A →
        ∃ S : Subgroup Y, IsSylowIn 2 S L ∧ A = (Subgroup.center ↥S).map S.subtype

end CFSG.LocalAnalysis.WeakClosure81

end

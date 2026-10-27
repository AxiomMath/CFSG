module

public import CFSG.Quasithin.EmptyFaithful.S1421F112

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique

@[expose] def F112L24G2Statement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L1 L2 S : Subgroup G), Hyp111 L1 L2 S →
    IsQuasithinSub (L1 ⊔ L2 ⊔ S) →
    ((S.subgroupOf (S ⊔ borelOf L1 S)).Normal ∨ (S.subgroupOf (S ⊔ borelOf L2 S)).Normal) →
    Nat.card (oTwoQuot ↥L1) = 60 → Nat.card (oTwoQuot ↥L2) = 60 →
    (¬ IsShort2 L1 ∨ ¬ IsShort2 L2) →
    ∃ L1' L2' : Subgroup G, ((L1' = L1 ∧ L2' = L2) ∨ (L1' = L2 ∧ L2' = L1)) ∧
      IsAmalgamOfGroup (RankTwoAmalgam.ofSubgroups (L1' ⊔ bigB L1' L2' S)
        (L2' ⊔ bigB L1' L2' S)) (IsG2Over 2)

end CFSG.Quasithin

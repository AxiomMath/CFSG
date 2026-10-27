module

public import CFSG.Quasithin.Vol2.Ch3nE2

public section

namespace CFSG.Quasithin.Res2

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits B2F

@[expose] def E215MemberW : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (H T M V : Subgroup G), E2.Hyp28 H T M V → CharTwo H →
    ¬ Group.IsSolvable H →
    (∀ A : Subgroup G, A ≤ T → IsElemAbelian 2 A →
      (A ⊓ Subgroup.centralizer (V : Set G)).relIndex A ≤ 4) →
    ∃ g ∈ H, E2.Pair (Ch3n.pairI V g) (T ⊓ Ch3n.pairI V g) (M ⊓ Ch3n.pairI V g) V g ∧
      CharTwo (Ch3n.pairI V g) ∧ Ch3n.pairI V g ≠ V ∧
      (V ⊓ Subgroup.centralizer ((B6.conjSub g
          (kerIn (M ⊓ Ch3n.pairI V g) (Ch3n.pairI V g) ⊓ V) : Subgroup G) : Set G)).relIndex V <
        ((B6.conjSub g (kerIn (M ⊓ Ch3n.pairI V g) (Ch3n.pairI V g) ⊓ V) ⊓
            Subgroup.centralizer (V : Set G)).relIndex
          (B6.conjSub g (kerIn (M ⊓ Ch3n.pairI V g) (Ch3n.pairI V g) ⊓ V))) ^ 2

end CFSG.Quasithin.Res2

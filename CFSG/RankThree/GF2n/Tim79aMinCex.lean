module

public import CFSG.CGT.Timmesfeld75.Defs
public import CFSG.Foundations.Basic

public section

namespace CFSG.RankThree.GF2n

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open

namespace Tim79a

variable {G : Type} [Group G]

structure MinCex (M V Q P H : Subgroup G) : Prop where
  o2 : pCore 2 G = ⊥
  maxLocal : IsMaximalTwoLocal M
  fitting : generalizedFitting M = pCore 2 M
  maxAb : Maximal (fun U : Subgroup G => U ≤ M ∧ M ≤ Subgroup.normalizer (U : Set G) ∧
    IsMulCommutative U) V
  elemAb : Assembly.IsElemAbelian 2 V
  ti : IsTI V
  four : 4 ≤ Nat.card V
  hQ : Q = inSubgroup (pCore 2) M
  hP : P = Q ⊓ Subgroup.centralizer (V : Set G)
  notWC : ¬ WeaklyClosedIn V M
  PleH : P ≤ H
  o2H : inSubgroup (pCore 2) H ≠ ⊥
  notLe : ¬ V ≤ inSubgroup (pCore 2) H
  min : ∀ K : Subgroup G, P ≤ K → inSubgroup (pCore 2) K ≠ ⊥ → K < H →
    V ≤ inSubgroup (pCore 2) K

end Tim79a

end CFSG.RankThree.GF2n

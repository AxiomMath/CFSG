module

public import CFSG.CGT.Timmesfeld75.Defs
public import CFSG.Foundations.Basic

public section

namespace CFSG.RankThree.GF2n

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open

namespace Tim78

variable {G : Type} [Group G]

@[expose] def classD (B : Subgroup G) : Set G :=
  {t | ∃ g : G, ∃ b ∈ B, b ≠ 1 ∧ t = g * b * g⁻¹}

structure Hyp4 (M B Q P T : Subgroup G) : Prop where
  o2 : pCore 2 G = ⊥
  maxLocal : IsMaximalTwoLocal M
  fitting : generalizedFitting M = pCore 2 M
  maxAb : Maximal (fun U : Subgroup G => U ≤ M ∧ M ≤ Subgroup.normalizer (U : Set G) ∧
    IsMulCommutative U) B
  sq_eq_one : ∀ x ∈ B, x ^ 2 = 1
  ti : IsTI B
  q4 : 4 ≤ Nat.card B
  hQ : Q = inSubgroup (pCore 2) M
  hP : P = ⨆ (g : G) (_ : conjSubgroup g B ≤ Q), conjSubgroup g B
  hT : T = Q ⊓ Subgroup.centralizer (P : Set G)
  notWC : ∃ g : G, conjSubgroup g B ≤ Q ∧ conjSubgroup g B ≠ B
  PneQ : P ≠ Q

end Tim78

@[expose] def Tim78Sec4Statement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (M B Q P T : Subgroup G),
    Tim78.Hyp4 M B Q P T → False

end CFSG.RankThree.GF2n

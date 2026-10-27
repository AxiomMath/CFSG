module

public import CFSG.RankThree.PartTwo.Sec21.FF79Sec3L4In

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF79.H4

open CFSG CFSG.RankThree.PartTwo.Sec21
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

structure FF79Sec34In4 (b : G) (J B A P D : Subgroup G) : Prop where
  hyp : FF79Hyp 4 b J
  sylB : IsSylowOf 3 B (Cen b)
  elemB : IsElemAb 3 3 B
  elemB0 : IsElemAb 3 2 (B ⊓ J)
  supB : Subgroup.zpowers b ⊔ (B ⊓ J) = B
  elemA : IsElemAb 3 4 A
  B0A : B ⊓ J ≤ A
  bA : b ∈ Nor A
  commbA : ⁅Subgroup.zpowers b, A⁆ = B ⊓ J
  hJ : J = OUpp 2 (Cen b)
  cbSplit : setMul3 (Subgroup.zpowers b) J (Opp 3 (Cen b)) = Cen b ∧
    Nat.card (Cen b) = 3 * Nat.card J * Nat.card (Opp 3 (Cen b))
  oddX : Odd (Nat.card (Opp 3 (Cen b)))
  oddCB : Odd (Nat.card (CenS B))
  star : ∃ As : Subgroup G, FF79AStar b D A As
  DJ : D ≤ J
  DA : D ≤ Nor A
  D8 : Nat.card D = 8 ∧ ¬ IsMulCommutative D
  sylD : IsSylowOf 2 D (Cen b ⊓ Nor A)

end CFSG.RankThree.PartTwo.Sec21.FF79.H4

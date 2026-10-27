module

public import CFSG.RankThree.PartTwo.Sec21.FF79Vocab

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF79

open CFSG CFSG.RankThree.PartTwo.Sec21
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

@[expose] def FF79AStar (b : G) (D A As : Subgroup G) : Prop :=
  A ≤ As ∧ IsSylowOf 3 As (CenS A) ∧ IsMulCommutative As ∧ b ∈ Nor As ∧ D ≤ Nor As ∧
  (∀ z ∈ Subgroup.center D, z ≠ 1 → ∀ s ∈ As, z * s * z⁻¹ = s⁻¹) ∧
  IsSylowOf 3 (As ⊔ Subgroup.zpowers b) ⊤ ∧
  (∀ s : G, s ∈ As → (⁅⁅s, b⁆, b⁆ = 1 ↔ s ∈ A))

structure FF79Sec34In (b : G) (J B A P D : Subgroup G) : Prop where
  hyp : FF79Hyp 5 b J
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

abbrev U34 (b a : G) (J A : Subgroup G) : Subgroup G :=
  A ⊓ CenS (Lay (J ⊓ Cen a)) ⊓ Nor (Subgroup.closure {a, b})

end CFSG.RankThree.PartTwo.Sec21.FF79

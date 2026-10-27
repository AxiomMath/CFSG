module

public import CFSG.RankThree.PartTwo.Sec21.FF79Sec3L4In

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF79

open CFSG CFSG.RankThree.PartTwo.Sec21

variable {G : Type} [Group G] [Finite G]

structure FF79Sec34Pre (b : G) (J B A P D : Subgroup G) : Prop where
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
  DJ : D ≤ J
  DA : D ≤ Nor A
  D8 : Nat.card D = 8 ∧ ¬ IsMulCommutative D
  sylD : IsSylowOf 2 D (Cen b ⊓ Nor A)
  hP : P = Subgroup.zpowers b ⊔ A
  sylP : IsSylowOf 3 P (Nor B)
  expP : Monoid.exponent P = 3
  zA : ∀ z ∈ Subgroup.center D, z ≠ 1 → ∀ a ∈ A, z * a * z⁻¹ = a⁻¹

theorem FF79Sec34Pre.toIn {b : G} {J B A P D : Subgroup G} (h : FF79Sec34Pre b J B A P D)
    (hs : ∃ As : Subgroup G, FF79AStar b D A As) : FF79Sec34In b J B A P D :=
  ⟨h.hyp, h.sylB, h.elemB, h.elemB0, h.supB, h.elemA, h.B0A, h.bA, h.commbA, h.hJ, h.cbSplit,
    h.oddX, h.oddCB, hs, h.DJ, h.DA, h.D8, h.sylD⟩

@[expose] def FF79AStarExists : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (b : G) (J B A P D : Subgroup G),
    IsSimpleGroup G → (∃ x y : G, x * y ≠ y * x) →
    CFSG.Assembly.KProper CFSG.Assembly.InCatalog G → FF79Sec3 b J →
    FF79Sec34Pre b J B A P D → ∃ As : Subgroup G, FF79AStar b D A As

end CFSG.RankThree.PartTwo.Sec21.FF79

module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Foundations.Basic
public import CFSG.RankThree.PartTwo.Sec8.Hering611SGenB

public section

namespace CFSG.RankThree.PartTwo.Sec8.Hering611

open CFSG CFSG.RankThree.PartTwo

structure J3VPair (J : Type) [Group J] (kb ab : J) (V : Fin 2 → Subgroup J) : Prop where
  elem : ∀ i, CFSG.Assembly.IsElemAbelian 2 (V i) ∧ Nat.card (V i) = 16
  inv : ∀ i, kb ∈ Subgroup.normalizer (V i : Set J) ∧ ab ∈ Subgroup.normalizer (V i : Set J)
  card : Nat.card (V 0 ⊔ V 1 : Subgroup J) = 64
  norm : ∀ i j, V j ≤ Subgroup.normalizer (V i : Set J)
  le_res : ∀ i j, V j ≤ inSubgroup perfectResidual (Subgroup.normalizer (V i : Set J))
  ab_mem : ∀ i, ab ∈ inSubgroup perfectResidual (Subgroup.normalizer (V i : Set J))
  closure : ∀ i, Subgroup.closure {z : J | ∃ x ∈ inSubgroup perfectResidual
      (Subgroup.normalizer (V i : Set J)), z = x * ab * x⁻¹} =
    inSubgroup perfectResidual (Subgroup.normalizer (V i : Set J))
  gen : inSubgroup perfectResidual (Subgroup.normalizer (V 0 : Set J)) ⊔
    inSubgroup perfectResidual (Subgroup.normalizer (V 1 : Set J)) = ⊤
  aut : ∀ i, ∀ σ : MulAut J, (∀ v ∈ V i, σ v = v) → ∃ v ∈ V i, σ = MulAut.conj v
  four : ∀ m : ℕ, m < 3 →
    Nat.card (Subgroup.centralizer ({kb * ab ^ m} : Set J) ⊓ (V 0 ⊔ V 1) : Subgroup J) = 4 ∧
      ∃ w ∈ Subgroup.centralizer ({kb * ab ^ m} : Set J) ⊓ (V 0 ⊔ V 1), ab * w * ab⁻¹ ≠ w

structure J3TwoLocalFacts (J : Type) [Group J] (kb ab : J) : Prop where
  B0 : CFSG.Assembly.IsElemAbelian 3
      (Subgroup.centralizer ((Subgroup.closure ({kb, ab} : Set J) : Subgroup J) : Set J)) ∧
    Nat.card (Subgroup.centralizer ((Subgroup.closure ({kb, ab} : Set J) : Subgroup J) : Set J)) =
      27
  fuse : ∀ m : ℕ, (m = 1 ∨ m = 2) → ∃ g ∈ Subgroup.normalizer
    ((Subgroup.centralizer ((Subgroup.closure ({kb, ab} : Set J) : Subgroup J) : Set J) :
      Subgroup J) : Set J), g * kb * g⁻¹ = kb * ab ^ m
  pair : ∃ V : Fin 2 → Subgroup J, J3VPair J kb ab V

@[expose] def J3TwoLocalInput : Prop :=
  ∀ (J : Type) [Group J] [Finite J], Nonempty (J ≃* Blueprint.NativeSporadic.J3) →
    ∀ kb ab : J, orderOf kb = 3 → orderOf ab = 3 → kb * ab = ab * kb →
      (∃ Pb : Subgroup J, Group.IsPerfect Pb ∧ Pb ≤ Subgroup.centralizer ({kb} : Set J) ∧ ab ∈ Pb ∧
        360 ∣ Nat.card Pb) → J3TwoLocalFacts J kb ab

end CFSG.RankThree.PartTwo.Sec8.Hering611

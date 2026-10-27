module

public import CFSG.LocalAnalysis.UniquenessCase.UC22K108H207

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.F10

open Subgroup

@[expose] def K108RowH (F : (S : Type) → [Group S] → Prop) : Prop :=
  ∀ (Gh : Type) [Group Gh] [Finite Gh] (S : Subgroup Gh), S.Normal → IsSimpleGroup ↥S →
    (∃ a b : ↥S, a * b ≠ b * a) → centralizer (S : Set Gh) = ⊥ → F ↥S →
    ∀ (T B : Subgroup Gh), Hyp10 T B → S ⊔ B = ⊤ →
    ∀ (X M : Subgroup Gh), X ≤ B → (Nat.card X).Prime → Odd (Nat.card X) →
      T ≤ M → X ≤ M → (∀ g : Gh, (∀ x ∈ X, g⁻¹ * x * g ∈ M) → g ∈ M) → S ≤ M

@[expose] def K108RowX (F : (S : Type) → [Group S] → Prop) : Prop :=
  ∀ (Gh : Type) [Group Gh] [Finite Gh] (S : Subgroup Gh), S.Normal → IsSimpleGroup ↥S →
    (∃ a b : ↥S, a * b ≠ b * a) → centralizer (S : Set Gh) = ⊥ → F ↥S →
    ∀ (T X : Subgroup Gh), CFSG.ABGLocalTools.IsSylowOf 2 T ⊤ → (Nat.card X).Prime → Odd (Nat.card X) →
      S ⊔ X = ⊤ → X ≤ normalizer (T : Set Gh) →
    ∀ M : Subgroup Gh, T ≤ M → X ≤ M → (∀ g : Gh, (∀ x ∈ X, g⁻¹ * x * g ∈ M) → g ∈ M) → S ≤ M

@[expose] def K108BT (F : (S : Type) → [Group S] → Prop) : Prop :=
  ∀ (S : Type) [Group S] [Finite S], IsSimpleGroup S → (∃ a b : S, a * b ≠ b * a) → F S →
    ∀ T : Subgroup S, CFSG.ABGLocalTools.IsSylowOf 2 T ⊤ →
    ∀ H : Subgroup S, T ≤ H → Group.IsSolvable ↥H → H ≤ normalizer (T : Set S)

@[expose] def K108RowL2 : Prop := K108RowX K108FamL2
@[expose] def K108RowSz : Prop := K108RowX K108FamSz
@[expose] def K108RowU3 : Prop := K108RowX K108FamU3
@[expose] def K108RowL3 : Prop := K108RowX K108FamL3
@[expose] def K108RowSp4 : Prop := K108RowX K108FamSp4
@[expose] def K108RowG2 : Prop := K108RowX K108FamG2
@[expose] def K108Row3D4 : Prop := K108RowX K108Fam3D4
@[expose] def K108Row2F4 : Prop := K108RowX K108Fam2F4
@[expose] def K108RowU4 : Prop := K108RowX K108FamU4
@[expose] def K108RowU5 : Prop := K108RowX K108FamU5
@[expose] def K108RowL4 : Prop := K108RowX K108FamL4
@[expose] def K108RowSp6 : Prop := K108RowX K108FamSp6
@[expose] def K108RowO8m : Prop := K108RowX K108FamO8m
@[expose] def K108Row3D4two : Prop := K108RowH K108Fam3D4two

@[expose] def K108BTL2 : Prop := K108BT K108FamL2
@[expose] def K108BTSz : Prop := K108BT K108FamSz
@[expose] def K108BTU3 : Prop := K108BT K108FamU3
@[expose] def K108BTL3 : Prop := K108BT K108FamL3
@[expose] def K108BTSp4 : Prop := K108BT K108FamSp4
@[expose] def K108BTG2 : Prop := K108BT K108FamG2
@[expose] def K108BT3D4 : Prop := K108BT K108Fam3D4
@[expose] def K108BT2F4 : Prop := K108BT K108Fam2F4
@[expose] def K108BTU4 : Prop := K108BT K108FamU4
@[expose] def K108BTU5 : Prop := K108BT K108FamU5
@[expose] def K108BTL4 : Prop := K108BT K108FamL4
@[expose] def K108BTSp6 : Prop := K108BT K108FamSp6
@[expose] def K108BTO8m : Prop := K108BT K108FamO8m

structure K108Rows : Prop where
  l2 : K108RowL2
  sz : K108RowSz
  u3 : K108RowU3
  l3 : K108RowL3
  sp4 : K108RowSp4
  g2 : K108RowG2
  d4 : K108Row3D4
  f4 : K108Row2F4
  u4 : K108RowU4
  u5 : K108RowU5
  l4 : K108RowL4
  sp6 : K108RowSp6
  o8m : K108RowO8m
  bt_l2 : K108BTL2
  bt_sz : K108BTSz
  bt_u3 : K108BTU3
  bt_l3 : K108BTL3
  bt_sp4 : K108BTSp4
  bt_g2 : K108BTG2
  bt_d4 : K108BT3D4
  bt_f4 : K108BT2F4
  bt_u4 : K108BTU4
  bt_u5 : K108BTU5
  bt_l4 : K108BTL4
  bt_sp6 : K108BTSp6
  bt_o8m : K108BTO8m
  d4two : K108Row3D4two

end CFSG.LocalAnalysis.UniquenessCase.UC22.F10

module

public import CFSG.RankThree.PartTwo.Sec19.SimsC198Defs
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.GroupTheory.ABGLocalTools.Basic

public section

namespace CFSG.RankThree.PartTwo.Sec18.Item185Proof

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Late
open CFSG.ABGLocalTools (IsSylowOf)
open CFSG.Assembly (IsElemAbelian)
open CFSG.RankThree.PartTwo.Sec19.SimsC198 (RankHyp)

variable {G : Type} [Group G] [Finite G]

@[expose] def innerAut (X : Type) [Group X] : Subgroup (MulAut X) :=
  (MulAut.conj : X →* MulAut X).range

@[expose] def fixedSubgroup {X : Type} [Group X] (σ : MulAut X) : Subgroup X :=
  MonoidHom.eqLocus σ.toMonoidHom (MonoidHom.id X)

@[expose] noncomputable def oTwoThreeFixed {X : Type} [Group X] (σ : MulAut X) : Subgroup X :=
  (Sec4.oTwoP 3 (fixedSubgroup σ)).map (fixedSubgroup σ).subtype

@[expose] def LeafF1 : Prop :=
  ∀ (X : Type) [Group X] [Finite X], RankHyp X → CFSG.Open.pRank 3 (⊤ : Subgroup X) ≤ 1 →
    ∀ D : Subgroup (MulAut X), IsElemAbelian 3 D → Nat.card D = 9 → D ⊓ innerAut X ≠ ⊥

structure OuterData (X : Type) [Group X] [Finite X] (P A B : Subgroup (MulAut X))
    (c : MulAut X) : Prop where
  isPGroup : IsPGroup 3 P
  sylow : IsSylowOf 3 P (P ⊔ innerAut X)
  card_le : ∀ E ≤ P, IsElemAbelian 3 E → Nat.card E ≤ 27
  isElemAbelian : IsElemAbelian 3 A
  card_A : Nat.card A = 27
  le_P : A ≤ P
  le_B : B ≤ A
  card_B : Nat.card B = 9
  eq_sup : A = Subgroup.zpowers c ⊔ B
  not_mem : c ∉ B
  le_inner : B ≤ innerAut X
  dichotomy : (∀ x ∈ P, x * c = c * x) ∨
    ((∀ x ∈ P, (∀ a ∈ A, x * a = a * x) → x ∈ A) ∧
      ∀ b ∈ B, ∃ x ∈ P ⊓ Subgroup.centralizer (B : Set (MulAut X)), x * c * x⁻¹ = b * c)
  omega : B ≤ (oTwoThreeFixed c).map (MulAut.conj : X →* MulAut X)
  outer : c ∉ innerAut X

@[expose] def LeafOuter : Prop :=
  ∀ (X : Type) [Group X] [Finite X], RankHyp X →
    ∀ (P A B : Subgroup (MulAut X)) (c : MulAut X), OuterData X P A B c → False

@[expose] def LeafInner : Prop :=
  ∀ (X : Type) [Group X] [Finite X], RankHyp X → ∀ (A B : Subgroup X) (c : X),
    IsElemAbelian 3 A → Nat.card A = 27 → B ≤ A → Nat.card B = 9 →
    A = Subgroup.zpowers c ⊔ B → c ∉ B → A ⊓ Subgroup.center X = ⊥ →
    Subgroup.normalizer (A : Set X) ≤ Subgroup.normalizer (B : Set X) →
    B ≤ (Sec4.oTwoP 3 (Subgroup.centralizer ({c} : Set X))).map
      (Subgroup.centralizer ({c} : Set X)).subtype → False

end CFSG.RankThree.PartTwo.Sec18.Item185Proof

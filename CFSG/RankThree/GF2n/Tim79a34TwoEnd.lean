module

public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.RankThree.GF2n.Tim79aRootStatements
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.RankThree.GF2n.Tim79a

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open
open scoped commutatorElement

variable {G : Type} [Group G]

structure TwoEndHyp (M V Q P H : Subgroup G) : Prop where
  setup : Sec23Setup M V Q P H
  q_two : qBar V H = 2
  three : Sec23Three V H
  centre : CentreClause V H
  tilde : Sec24bTilde V H P
  concl : Sec25Concl V H P
  module : Nat.card ↥(V ⊓ wOf V H) = qBar V H

@[expose] def Sec34QIndexStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M V Q P H : Subgroup G), TwoEndHyp M V Q P H →
    Subgroup.center (Xbar V H) = ⊥ → P.relIndex Q ≤ 2

@[expose] def Sec34IWStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M V Q P H : Subgroup G), TwoEndHyp M V Q P H →
    Subgroup.center (Xbar V H) = ⊥ → cPbar V H P ≤ wOf V H

@[expose] def Sec34GammaStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M V Q P H : Subgroup G), TwoEndHyp M V Q P H →
    Subgroup.center (Xbar V H) = ⊥ →
    ∃ C : Subgroup G, C ≤ Q ∧ P ⊔ C = Q ∧ (∀ p ∈ P, ∀ c ∈ C, ⁅p, c⁆ ∈ V ⊓ wOf V H) ∧
      (∀ c ∈ C, ∀ w ∈ wOf V H, c * w = w * c) ∧ (∀ c ∈ C, ∀ x ∈ xOf V H, ⁅x, c⁆ ∈ wOf V H) ∧
      P.relIndex Q ≤ 2

theorem xOf_eq_H_of_iw (hI : Sec34IWStatement) {G : Type} [Group G] [Finite G]
    {M V Q P H : Subgroup G} (hH : TwoEndHyp M V Q P H) (hZ : Subgroup.center (Xbar V H) = ⊥) :
    xOf V H = H := by
  have hX : xOf V H ⊔ cPbar V H P = H := hH.concl.2.1
  have hle : cPbar V H P ≤ xOf V H := (hI G M V Q P H hH hZ).trans (wOf_le_xOf V H)
  rw [sup_eq_left.mpr hle] at hX
  exact hX

@[expose] def NTTwoStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M V Q P H : Subgroup G), TwoEndHyp M V Q P H →
    Subgroup.center (Xbar V H) = ⊥ →
    Nonempty (↥(StatedSp 2 (GaloisField 2 1)) ≃* XbarZ V H) → False

end CFSG.RankThree.GF2n.Tim79a

module

public import CFSG.RankThree.GF2n.Stroth80.Sec9Stmt

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement Matrix

@[expose] def ListWCBoundStatement : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (T L : Subgroup Y), T ≠ ⊥ → T ≤ L → IsElemAbelian 2 L →
    CorBHyp T → ListGroup ↥(Subgroup.normalClosure (T : Set Y)) →
    (∀ h : Y, L ⊓ conjSubgroup h L ≠ ⊥ → T ⊓ conjSubgroup h L ≠ ⊥) →
    Nat.card L < Nat.card T ^ 4

@[expose] def Close93FinalWithClaimThreeStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) (hc : Ctx M Q Z B) (n : ℕ) (t : G),
    Sec9Hyp hc n t → ∀ Z0 : Subgroup G, IsCentrePre Z0 (Rt M (LB M Q B) t) Q →
      (∀ h ∈ M, LB M Q B ⊓ conjSubgroup h (LB M Q B) ≠ Q →
        Z0 ⊓ (LB M Q B ⊓ conjSubgroup h (LB M Q B)) ≠ Q) →
      WeaklyClosedInCent M Q Z0 → False

theorem stroth93_of_steps_withClaimThree (hA : Sec9AExistsStatement) (h1 : Step93OneStatement)
    (h2 : Step93VanishStatement) (h3 : Step93TIStatement) (h4 : Step93FourStatement)
    (hE : Step93EndStatement) (hF : Close93FinalWithClaimThreeStatement) :
    Stroth93Statement := by
  intro G _ _ M Q Z B hc n t hs Z0 hZ0 hsc
  obtain ⟨r, hr⟩ := hA G M Q Z B hc n t hs
  have e3 := h3 G M Q Z B hc n t hs r hr Z0 hZ0 hsc
  refine hF G M Q Z B hc n t hs Z0 hZ0 e3 ?_
  intro g hg hcomm x hx
  by_contra hnot
  have hT : Sec9T1 M Q Z0 x g := ⟨hx, hg, fun y hy => hcomm x hx y hy, hnot⟩
  have e1 := h1 G M Q Z B hc n t hs r hr Z0 hZ0 hsc
  have e2 := h2 G M Q Z B hc n t hs r hr Z0 hZ0 hsc x g hT
  have e4 := h4 G M Q Z B hc n t hs r hr Z0 hZ0 hsc x g hT e1 e2 e3
  exact hE G M Q Z B hc n t hs r hr Z0 hZ0 hsc x g hT e4

end CFSG.RankThree.GF2n.Stroth80

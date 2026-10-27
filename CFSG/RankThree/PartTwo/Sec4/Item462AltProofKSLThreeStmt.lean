module

public import CFSG.RankThree.PartTwo.Sec4.Item462AltProofKFacts

public section

namespace CFSG.RankThree.PartTwo.Sec4.Item462AltProof

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo

@[expose] def KSLThreeCentralizerQ : Prop :=
  ∀ (X : Type) [Group X] [Finite X], IsQuasisimple X → ∀ (p e : ℕ) [Fact p.Prime], 1 ≤ e →
    (IsSLThreePiAt X (p ^ e) ∨ IsoLThreePi X p e) → ∀ β : MulAut X, orderOf β = 3 →
      InnThetaNoncyclic β → p ≠ 2 ∧ ∃ v : X, v ^ 3 = 1 ∧ β = MulAut.conj v

theorem _root_.CFSG.RankThree.PartTwo.Sec4.Item462AltProof.KSLThreeCentralizerQ.inst
    (hKL3 : KSLThreeCentralizerQ) {G : Type} [Group G] [Finite G] {L : Subgroup G}
    (hL : L ∈ thetaComponents 3 G) {p e : ℕ} [Fact p.Prime] (he : 1 ≤ e)
    (h : IsSLThreePiAt (L ⧸ aschbacherSolvableCore 3 L) (p ^ e) ∨
      IsoLThreePi (L ⧸ aschbacherSolvableCore 3 L) p e)
    {β : MulAut (L ⧸ aschbacherSolvableCore 3 L)} (hβ3 : orderOf β = 3)
    (hβ : InnThetaNoncyclic β) :
    p ≠ 2 ∧ ∃ v : L ⧸ aschbacherSolvableCore 3 L, v ^ 3 = 1 ∧ β = MulAut.conj v :=
  hKL3 _ hL.2.2 p e he h β hβ3 hβ

end CFSG.RankThree.PartTwo.Sec4.Item462AltProof

end

module

public import CFSG.RankThree.PartTwo.Sec4.Item462AltProofModels
public import CFSG.RankThree.PartTwo.Sec4.Item47WStatement
public import CFSG.RankThree.PartTwo.Sec4.Item462AltProofKSLThreeStmt
import CFSG.RankThree.PartTwo.Sec10.Sec10XProofCover
public import CFSG.RankThree.PartTwo.Sec4.Item462ProofUL

public section

namespace CFSG.RankThree.PartTwo.Sec4.Item462AltProof

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Assembly.RankThreeEven (projSL projSU projSp)

@[expose] def List463 {G : Type} [Group G] (L : Subgroup G) : Prop :=
  haveI : (solvableRadical L).Normal := Subgroup.normal_sSup _ fun _ hN => hN.1
  Nonempty (L ⧸ solvableRadical L ≃* alternatingGroup (Fin 7)) ∨
    Nonempty (L ⧸ solvableRadical L ≃* Blueprint.NativeSporadic.M12) ∨
    Nonempty (L ⧸ solvableRadical L ≃* Blueprint.NativeSporadic.J2) ∨
    Nonempty (L ⧸ solvableRadical L ≃* Blueprint.NativeSporadic.M22) ∨
    (∃ (p e : ℕ) (_ : Fact p.Prime), 3 < p ∧ 1 ≤ e ∧ e ≤ 2 ∧
      IsoLThreePi (L ⧸ solvableRadical L) p e) ∨
    Nonempty (L ⧸ solvableRadical L ≃* projSL 2 (GaloisField 3 3))

section Main


theorem alt47_cases (hKL2 : KLTwoCentralizer) (hKC2 : KChevTwoCentralizer)
    (hKL3 : KSLThreeCentralizerQ) {G : Type} [Group G] [Finite G] {L : Subgroup G}
    (hL : L ∈ thetaComponents 3 G) {β : MulAut (L ⧸ aschbacherSolvableCore 3 L)}
    (hβ3 : orderOf β = 3) (hβ : InnThetaNoncyclic β) {x : G} (h47 : Alt47W L x) :
    (Nonempty (L ⧸ aschbacherSolvableCore 3 L ≃* projSL 2 (GaloisField 3 3)) ∧
        β ∉ (MulAut.conj : L ⧸ aschbacherSolvableCore 3 L →* MulAut _).range) ∨
      ∃ (p e : ℕ) (_ : Fact p.Prime), 3 < p ∧ 1 ≤ e ∧ e ≤ 2 ∧
        (IsSLThreePiAt (L ⧸ aschbacherSolvableCore 3 L) (p ^ e) ∨
          IsoLThreePi (L ⧸ aschbacherSolvableCore 3 L) p e) ∧
        KFacts.InducesStdKind L x .diagonal := by
  have hq := hL.2.2
  rcases h47 with ⟨p, e, hpF, hp2, he, ⟨eX⟩, -⟩ | ⟨p, e, hpF, hp3, he1, he2, hiso, hdiag⟩ |
      ⟨hmod, -⟩ | ⟨n, hn, hiso, -⟩ | ⟨n, hn, hD4⟩
  · left
    obtain ⟨rfl, h3e, hβo⟩ := hKL2 p (3 * e) hp2 (by omega) _ ⟨eX⟩ β hβ3 hβ
    obtain rfl : e = 1 := by omega
    exact ⟨⟨eX⟩, hβo⟩
  · exact Or.inr ⟨p, e, hpF, hp3, he1, he2, hiso, hdiag⟩
  · exact (hKC2 _ hq (Or.inl hmod) β hβ3 hβ).elim
  · have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact absurd rfl (KSLThreeCentralizerQ.inst hKL3 hL hn hiso hβ3 hβ).1
  · exact (hKC2 _ hq (Or.inr ⟨n, hn, hD4⟩) β hβ3 hβ).elim

theorem case8_462 (hKL2 : KLTwoCentralizer) (hKC2 : KChevTwoCentralizer)
    (hKL3 : KSLThreeCentralizerQ) (hKL3K : KSLThreeNoFieldKind) {G : Type} [Group G] [Finite G]
    {L A : Subgroup G} (hL : L ∈ thetaComponents 3 G) (hAe : CFSG.Assembly.IsElemAbelian 3 A)
    {β : MulAut (L ⧸ aschbacherSolvableCore 3 L)} (hβ3 : orderOf β = 3)
    (hβ : InnThetaNoncyclic β)
    (h47 : ∀ e ∈ A, orderOf e = 3 → InducesOuterTheta e L → Alt47W L e)
    (h8 : ∃ x ∈ A, x ≠ 1 ∧
      (KFacts.InducesStdKind L x .field ∨ KFacts.InducesStdKind L x .graphField)) :
    Nonempty (L ⧸ aschbacherSolvableCore 3 L ≃* projSL 2 (GaloisField 3 3)) ∧
      β ∉ (MulAut.conj : L ⧸ aschbacherSolvableCore 3 L →* MulAut _).range := by
  obtain ⟨x, hxA, hx1, hk⟩ := h8
  have hx3 : x ^ 3 = 1 := hAe.2 x hxA
  have hxo : orderOf x = 3 := orderOf_eq_prime hx3 hx1
  have hout : InducesOuterTheta x L := by
    rcases hk with hk | hk
    · exact KFacts.InducesStdKind.inducesOuterTheta L hk (by decide)
    · exact KFacts.InducesStdKind.inducesOuterTheta L hk (by decide)
  rcases alt47_cases hKL2 hKC2 hKL3 hL hβ3 hβ (h47 x hxA hxo hout) with h |
      ⟨p, e, hpF, hp3, he1, he2, hiso, -⟩
  · exact h
  · obtain ⟨hnf, hngf⟩ := hKL3K G L x p e hp3 he1 he2 hiso hx3
    rcases hk with hk | hk
    · exact (hnf hk).elim
    · exact (hngf hk).elim

theorem case8_463 (hKL2 : KLTwoCentralizer) (hKC2 : KChevTwoCentralizer)
    (hKL3 : KSLThreeCentralizerQ) {G : Type} [Group G] [Finite G]
    {L A : Subgroup G} (hL : L ∈ thetaComponents 3 G) (hAe : CFSG.Assembly.IsElemAbelian 3 A)
    {β : MulAut (L ⧸ aschbacherSolvableCore 3 L)} (hβ3 : orderOf β = 3)
    (hβ : InnThetaNoncyclic β)
    (h47 : ∀ e ∈ A, orderOf e = 3 → InducesOuterTheta e L → Alt47W L e)
    (h8 : ∃ x ∈ A, x ≠ 1 ∧
      (KFacts.InducesStdKind L x .field ∨ KFacts.InducesStdKind L x .graphField)) :
    List463 L := by
  have : (solvableRadical L).Normal := Subgroup.normal_sSup _ fun _ hN => hN.1
  obtain ⟨x, hxA, hx1, hk⟩ := h8
  have hx3 : x ^ 3 = 1 := hAe.2 x hxA
  have hxo : orderOf x = 3 := orderOf_eq_prime hx3 hx1
  have hout : InducesOuterTheta x L := by
    rcases hk with hk | hk
    · exact KFacts.InducesStdKind.inducesOuterTheta L hk (by decide)
    · exact KFacts.InducesStdKind.inducesOuterTheta L hk (by decide)
  rcases alt47_cases hKL2 hKC2 hKL3 hL hβ3 hβ (h47 x hxA hxo hout) with ⟨⟨eX⟩, -⟩ |
      ⟨p, e, hpF, hp3, he1, he2, hiso, -⟩
  · obtain ⟨eR⟩ := Sec10.Sec10XProof.nonempty_quotient_center_mulEquiv (Y := L) hL.2.2
    have hZ := (Item462Proof.center_eq_bot_and_isCyclic_of_l27 eX).1
    have e0 : (L ⧸ aschbacherSolvableCore 3 L) ⧸ Subgroup.center (L ⧸ aschbacherSolvableCore 3 L)
        ≃* L ⧸ aschbacherSolvableCore 3 L :=
      (QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨(eR.symm.trans e0).trans eX⟩))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
      ⟨p, e, hpF, hp3, he1, he2, isoLThreePi_solvableRadical hL he1 hiso⟩))))

end Main

end CFSG.RankThree.PartTwo.Sec4.Item462AltProof

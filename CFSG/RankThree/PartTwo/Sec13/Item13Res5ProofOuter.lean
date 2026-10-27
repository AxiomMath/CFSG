module

public import CFSG.RankThree.PartTwo.Sec13.Item13Res5ProofCenter

public section

namespace CFSG.RankThree.PartTwo.Sec13

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo

@[expose] def KS131SLThreeOuterE9 : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (p e : ℕ), p.Prime → 1 ≤ e → (p = 2 ∨ (3 < p ∧ e ≤ 2)) →
    Sec4.IsSLThreeEpsAt X (p ^ e) → IsQuasisimple X → Nat.card (Subgroup.center X) = 3 →
    ∀ B : Subgroup (MulAut X), CFSG.Assembly.IsElemAbelian 3 B → Nat.card B = 9 →
      (∀ x : X, orderOf x = 3 → (∀ β ∈ B, β x = x) → x ∈ Subgroup.center X) →
      (∀ y : X, MulAut.conj y ∈ B → ∀ β ∈ B, β y = y) →
      ¬ B ≤ (MulAut.conj : X →* MulAut X).range → False

theorem ks131CenterOuterE9_of
    (hSL : KS131SLThreeOuterE9) : KS131CenterOuterE9 := by
  intro X _ _ hl hq hZ3 B hB hB9 hF hNP hout
  rcases Res5Proof.center_cases hl hq with hZ | ⟨p, e, hp, he, hpe, hSL'⟩ | ⟨-, hinn⟩
  · rw [hZ, Subgroup.card_bot] at hZ3
    norm_num at hZ3
  · exact hSL X p e hp he hpe hSL' hq hZ3 B hB hB9 hF hNP hout
  · exact hout fun β hβ => hinn β (hB.2 β hβ)

end CFSG.RankThree.PartTwo.Sec13

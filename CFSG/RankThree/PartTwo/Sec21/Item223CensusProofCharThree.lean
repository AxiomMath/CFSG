module

import CFSG.RankThree.PartTwo.Sec19.Step1919EndProof
import CFSG.RankThree.PartTwo.Sec19.Step1911EndProof
import CFSG.RankThree.PartTwo.Sec19.Step1911Proof
public import CFSG.RankThree.PartTwo.Sec21.Item223CensusProofSporadic

public section

namespace CFSG.RankThree.PartTwo.Sec21

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo
open CFSG.Assembly.RankThreeEven (projSL projSU projSp)

namespace Item223CensusProof

theorem card_le_nine_of_open_pRank {S : Type} [Group S] [Finite S]
    (h : CFSG.Open.pRank 3 (⊤ : Subgroup S) ≤ 2) (F : Subgroup S)
    (hF : CFSG.Assembly.IsElemAbelian 3 F) : Nat.card F ≤ 9 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp (Sec4.isPGroup_of_isElemAbelian hF)
  have hkle : k ≤ CFSG.Open.pRank 3 (⊤ : Subgroup S) := by
    refine le_csSup ⟨Nat.card S, ?_⟩ ⟨F, le_top, hF, hk⟩
    rintro r ⟨B, -, -, hB⟩
    calc r ≤ 3 ^ r := (Nat.lt_pow_self (by norm_num)).le
      _ = Nat.card B := hB.symm
      _ ≤ Nat.card S := Subgroup.card_le_card_group B
  rw [hk]
  calc 3 ^ k ≤ 3 ^ 2 := Nat.pow_le_pow_right (by norm_num) (hkle.trans h)
    _ = 9 := by norm_num

theorem census223Fact_projSU_three_three : Census223Fact (projSU 3 3 1) := by
  have hs := Sec19.Step1911EndProof.isSimpleGroup_projSU_three_three
  have hcard : Nat.card (projSU 3 3 1) = 6048 := Sec19.Step1911Proof.card_projSU_three_three
  have : Finite (projSU 3 3 1) := Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
  refine census223Fact_of_simple_pRank (by rw [hcard]; norm_num)
    (pRank_le_two_of_card_le_nine fun F hF => card_le_nine_of_open_pRank ?_ F hF)
  exact Sec19.Step1919EndProof.pRank_three_le_of_mulEquiv_projSU (MulEquiv.refl _)

end Item223CensusProof

open Item223CensusProof

@[expose] def Census223CharThreeRest : Prop :=
  Census223Fact (projSL 3 (GaloisField 3 2)) ∧
  ∀ (Y : Type) [Group Y] [Finite Y], Nat.card (Subgroup.center Y) ≤ 3 →
    (Blueprint.ChevalleyExceptionalModel (Y ⧸ Subgroup.center Y) .G2 3 1 ∨
      Nonempty (Y ⧸ Subgroup.center Y ≃* projSU 4 3 1)) → Census223Fact Y

theorem census223CharThree_of (h : Census223CharThreeRest) : Census223CharThree :=
  ⟨h.1, census223Fact_projSU_three_three, h.2⟩

end CFSG.RankThree.PartTwo.Sec21

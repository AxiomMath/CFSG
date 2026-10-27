module

public import CFSG.RankThree.PartTwo.Sec4.Item424Res2ProofD4
import CFSG.RankThree.PartTwo.Sec4.Item4Res7ProofTrialityPGL
import CFSG.RankThree.PartTwo.Sec21.LangTwisted3ProofD4Even

public section

namespace CFSG.RankThree.PartTwo.Sec4

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley


theorem k424TrialitySecond_holds :
    K424TrialitySecond := by
  intro n K _ _ σ hK hσ γ y hγ hγy hy
  have hn1 : 1 ≤ n := by
    rcases Nat.eq_zero_or_pos n with rfl | h
    · exfalso
      rw [pow_zero, one_pow] at hK
      exact (Finite.one_lt_card (α := K)).ne' hK
    · exact h
  have hK2 : ringChar K = 2 := Sec8.Item8KFactsProof.ringChar_eq_two_of_card hK
  have : Finite (ModGL TwistTag.D4.tag K) := finite_modGL
  set α := γ * MulAut.conj y with hα
  have hcomm : Commute γ (MulAut.conj y) := by
    refine MulEquiv.ext fun x => ?_
    simp only [MulAut.mul_apply, MulAut.conj_apply, map_mul, map_inv, hγy]
  have hσ₀3 := Sec8.LangTwistedProof.fieldActor_pow_three hK hσ
  have hγ3 : γ ^ 3 = 1 := by
    obtain ⟨β, rfl | rfl⟩ := hγ
    · rw [conj_pow, hσ₀3, mul_one, mul_inv_cancel]
    · rw [conj_pow, inv_pow, hσ₀3, inv_one, mul_one, mul_inv_cancel]
  have hy3 : y ^ 3 = 1 := by rw [← hy]; exact pow_orderOf_eq_one y
  have hα3 : α ^ 3 = 1 := by
    rw [hα, hcomm.mul_pow, hγ3, one_mul, ← map_pow, hy3, map_one]
  have hγin := not_isInnerAut_of_isStdGraphFieldConj hn1 hK hσ hγ
  have hαin : ¬ KFacts.IsInnerAut α := by
    intro h
    apply hγin
    have e : γ = α * (MulAut.conj y)⁻¹ := by rw [hα, mul_inv_cancel_right]
    rw [e]
    exact Subgroup.mul_mem _ h (Subgroup.inv_mem _ ⟨y, rfl⟩)
  by_cases hstd : IsStdGraphFieldConj σ α
  · exact Item424Res2.not_hasType424_autFix_of_isStdGraphFieldConj hK2 σ hstd
  · rcases Nat.even_or_odd n with hev | hodd
    · obtain ⟨K', _, _, hK', ⟨e⟩⟩ :=
        Sec8.kF89D4SecondCentEven_holds n hev hn1 K σ hK hσ α hα3 hαin hstd
      exact Res4Seven.not_hasType424_of_mulEquiv_pgl hev hn1 hK' e
    · rcases Sec8.inputs47ClassesD4_of_lang Sec8.kF82D4LangCoset_holds Sec8.kF82D4SecondCent_holds
        n hodd K σ hK hσ α hα3 hαin with hs | ⟨-, -, -, -, -, -, ⟨K', _, _, hK', ⟨e⟩⟩⟩
      · exact absurd hs hstd
      · exact Res4Seven.not_hasType424_of_mulEquiv_pgu hodd hK' e

theorem k424TrialityOuter_holds :
    K424TrialityOuter :=
  k424TrialityOuter_of k424TrialitySecond_holds

end CFSG.RankThree.PartTwo.Sec4

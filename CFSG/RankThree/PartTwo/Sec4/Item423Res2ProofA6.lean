module

public import CFSG.RankThree.PartTwo.Sec4.Item423Res2ProofTools
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434AltSixAut

public section

namespace CFSG.RankThree.PartTwo.Sec4

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo

namespace Res423Two

open Item434AltPerm

theorem factorization_card_alt6 : (Nat.card (alternatingGroup (Fin 6))).factorization 3 = 2 := by
  rw [CFSG.ComponentClassification.CatalogueSchreierAlternating.DegreeSix.card_alternating_six,
    show (360 : ℕ) = 3 ^ 2 * 40 by norm_num, factorization_three_pow_mul 2 (by norm_num)]

theorem alphaVanishes_F06 : AlphaVanishes (alternatingGroup (Fin 6)) F06 := by
  refine alphaVanishes_of_noSignalizer (alternatingGroup.center_eq_bot (by simp)) ?_ ?_ ?_
  · intro a ha b hb
    exact congrArg Subtype.val (isElemAbelian_F06.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  · intro h
    have h9 := card_F06
    rw [h, Subgroup.card_bot] at h9
    norm_num at h9
  · intro Q hQ hN
    exact eq_bot_of_F06_le_normalizer hQ hN

theorem alphaVanishes_alt6 {X : Type} [Group X] [Finite X] (e : X ≃* alternatingGroup (Fin 6))
    {D : Subgroup X} (hD9 : Nat.card D = 9) : AlphaVanishes X D := by
  have hD9' : Nat.card (D.map e.toMonoidHom) = 9 := by
    rw [Subgroup.card_map_of_injective e.injective, hD9]
  obtain ⟨g, hg⟩ := exists_map_conj_eq_of_card_nine factorization_card_alt6 hD9' card_F06
  refine alphaVanishes_of_mulEquiv e (alphaVanishes_of_mulEquiv (MulAut.conj g) ?_)
  rw [show (D.map e.toMonoidHom).map (MulAut.conj g : alternatingGroup (Fin 6) ≃*
    alternatingGroup (Fin 6)).toMonoidHom = F06 from hg]
  exact alphaVanishes_F06

theorem census423_of_alt6 {X : Type} [Group X] [Finite X] (e : X ≃* alternatingGroup (Fin 6)) :
    Census423 X :=
  census423_of_alphaVanishes fun _ _ hD9 => alphaVanishes_alt6 e hD9

end Res423Two

end CFSG.RankThree.PartTwo.Sec4

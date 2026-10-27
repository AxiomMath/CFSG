module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenDefs2
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven2TwentyOddIndex
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven2TwentyOddTransport
public import CFSG.RankThree.PartTwo.Sec19.SimsTheoremCOmegaBridge

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LieType.ChevTwo CFSG.ComponentClassification.UnbalancedCatalog.EvenCatalog

theorem s16c167_oddCore_isometryCore_quadMinus_zmod_two {m : ℕ} (hm : 2 ≤ m) :
    CFSG.oddCore ↥(CFSG.MatrixModel.isometryCore (StatedQuadMinus (m + 1) (ZMod 2) 1 1)) = ⊥ := by
  refine s16c167_oddCore_isometryCore_of_goodQ (goodQ_minus (n := m) (by omega)) ?_
  obtain ⟨s, -, hs⟩ := CFSG.RankThree.PartTwo.Sec19.SimsTheoremC.exists_card_omegaMinusTwo hm
  have hs' : Nat.card ↥(StatedOmega (StatedQuadMinus (m + 1) (ZMod 2) 1 1)) =
      2 ^ ((m + 1) * m) * s := hs
  rw [hs']
  exact Nat.even_mul.mpr (Or.inl (Nat.even_pow.mpr ⟨even_two, by positivity⟩))

theorem s16c167_oddCore_isOMinus {X : Type} [Group X] {n : ℕ} (hn : n = 6 ∨ n = 8)
    (h : IsOMinus X n 1) : CFSG.oddCore X = ⊥ := by
  obtain ⟨-, K, _, _, b, c, hK, hpoly, ⟨e⟩⟩ := h
  rw [pow_one] at hK
  obtain ⟨t⟩ := s16c167_isometryCore_quadMinus_equiv (n / 2) hK hpoly
  rcases hn with rfl | rfl
  · exact oddCore_eq_bot_of_mulEquiv (e.trans t).symm
      (s16c167_oddCore_isometryCore_quadMinus_zmod_two (m := 2) le_rfl)
  · exact oddCore_eq_bot_of_mulEquiv (e.trans t).symm
      (s16c167_oddCore_isometryCore_quadMinus_zmod_two (m := 3) (by norm_num))

end CFSG.LocalAnalysis.UniquenessCase.PartTwo

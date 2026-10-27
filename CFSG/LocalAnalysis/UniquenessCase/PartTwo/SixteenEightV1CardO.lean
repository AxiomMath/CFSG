module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenDefs2
public import CFSG.HardMathSupport.Foote.E27.Q2OrthMinus
public import CFSG.HardMathSupport.Foote.E27.Q2OrthModel
public import CFSG.LieType.ChevTwo.OrthogonalBasic
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven2TwentyOddTransport

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Open CFSG.LieType.ChevTwo CFSG.HardMathSupport.Foote.E27

private theorem s16e_card_isoGrp_eq_two_mul_of_goodQ {ι : Type} [Fintype ι] [DecidableEq ι]
    {Q : (ι → ZMod 2) → ZMod 2} (hG : GoodQ Q) :
    Nat.card ↥(CFSG.MatrixModel.isometryCore Q) = 2 * Nat.card ↥(StatedOmega Q) := by
  have h := Subgroup.relIndex_mul_card (H := StatedOmega Q) (K := isoGrp Q)
  rw [inf_of_le_left (statedOmega_le_isoGrp Q), hG.relIndex_eq] at h
  rw [isoGrp_eq_isometryCore Q] at h
  exact h.symm

theorem s16e_card_eq_two_mul_of_isOMinus {X Y : Type} [Group X] [Group Y] {n : ℕ}
    (hn : n = 6 ∨ n = 8) (hX : IsOMinus X n 1) (hY : IsOmegaMinus Y n 1) :
    Nat.card X = 2 * Nat.card Y := by
  obtain ⟨-, K, hKfield, hKfinite, b, c, hKcard, hpoly, ⟨eX⟩⟩ := hX
  obtain ⟨-, K', hK'field, hK'finite, b', c', hK'card, hpoly', ⟨eY⟩⟩ := hY
  letI : Field K := hKfield
  letI : Finite K := hKfinite
  letI : Field K' := hK'field
  letI : Finite K' := hK'finite
  rw [pow_one] at hKcard hK'card
  have hXcard : Nat.card X =
      Nat.card ↥(CFSG.MatrixModel.isometryCore (StatedQuadMinus (n / 2) (ZMod 2) 1 1)) := by
    obtain ⟨tX⟩ := s16c167_isometryCore_quadMinus_equiv (n / 2) hKcard hpoly
    exact Nat.card_congr (eX.trans tX).toEquiv
  have hYcard : Nat.card Y =
      Nat.card ↥(StatedOmega (StatedQuadMinus (n / 2) (ZMod 2) 1 1)) := by
    refine Nat.card_congr (eY.trans
      (Q2.statedProjOmegaEquiv (StatedQuadMinus (n / 2) K' b' c') hK'card
        (StatedQuadMinus (n / 2) (ZMod 2) 1 1) ?_)).toEquiv
    intro v σ
    exact Q2.quadMinus_comp (n / 2) σ hpoly' v
  rcases hn with rfl | rfl
  · rw [hXcard, hYcard]
    exact s16e_card_isoGrp_eq_two_mul_of_goodQ (goodQ_minus (n := 2) (by norm_num))
  · rw [hXcard, hYcard]
    exact s16e_card_isoGrp_eq_two_mul_of_goodQ (goodQ_minus (n := 3) (by norm_num))

end CFSG.LocalAnalysis.UniquenessCase.PartTwo

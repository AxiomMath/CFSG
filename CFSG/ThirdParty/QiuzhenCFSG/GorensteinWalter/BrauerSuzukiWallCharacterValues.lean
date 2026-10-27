module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.BrauerSuzukiWallCharacterDecomposition

import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

/-!
# Character values at the distinguished involution

This is the short square-comparison argument in Bender's
Brauer--Suzuki--Wall proof.  Once the two transferred characters have been
decomposed and their pair-count scalar products compared, the three signed
irreducible constituents have values `2`, `-2`, and `-1` at `t`.
-/

namespace CFSG.GorensteinWalter

universe u

/-- Bender's decomposition and equal-square relation force the values of the
three signed irreducible constituents at the distinguished involution. -/
public theorem brauerSuzukiWall_character_values_of_square_ratio
    {G : Type u} [Group G] [Finite G]
    {t : G}
    {alpha beta gamma lambda phi : Section1.ClassFunction G}
    (halphaT : alpha t = 0)
    (hbetaOne : beta 1 = 0)
    (hbetaT : beta t = 4)
    (halphaDecomp :
      alpha = Section1.principalCharacter G + gamma - lambda)
    (hbetaDecomp : beta = phi - gamma)
    (hgammaDegreeNe : gamma 1 ≠ 0)
    (hratio : phi t ^ 2 / phi 1 = gamma t ^ 2 / gamma 1) :
    phi t = 2 ∧ gamma t = -2 ∧ lambda t = -1 := by
  have hdegree : phi 1 = gamma 1 := by
    have heval := congrFun hbetaDecomp (1 : G)
    rw [hbetaOne] at heval
    exact sub_eq_zero.mp heval.symm
  have hsquares : phi t ^ 2 = gamma t ^ 2 := by
    rw [hdegree] at hratio
    exact (div_left_inj' hgammaDegreeNe).mp hratio
  have hdiff : phi t - gamma t = 4 := by
    have heval := congrFun hbetaDecomp t
    rw [hbetaT] at heval
    exact heval.symm
  rcases eq_or_eq_neg_of_sq_eq_sq (phi t) (gamma t) hsquares with
    heq | hneg
  · rw [heq] at hdiff
    norm_num at hdiff
  · have hgammaT : gamma t = -2 := by
      rw [hneg] at hdiff
      linear_combination (-1 / 2 : ℂ) * hdiff
    have hphiT : phi t = 2 := by
      rw [hneg, hgammaT]
      norm_num
    have hlambdaT : lambda t = -1 := by
      have heval := congrFun halphaDecomp t
      rw [halphaT] at heval
      simp only [Pi.add_apply, Pi.sub_apply,
        Section1.principalCharacter_apply] at heval
      rw [hgammaT] at heval
      ring_nf at heval
      exact (sub_eq_zero.mp heval.symm).symm
    exact ⟨hphiT, hgammaT, hlambdaT⟩

end CFSG.GorensteinWalter

module

public import CFSG.LocalAnalysis.StandardType.GGLevTwoS2dAuxForm
public import CFSG.LocalAnalysis.StandardType.GGLevTwoTrans

public section

namespace CFSG.StandardType.LevTwo

open CFSG.LieType.RootSystem
open CFSG.LieType.Universal.Spin
open CFSG.ClassicalInvolution.ModelFacts

theorem levTwoS2d_isRt_transitive (n : ℕ) (hn : 4 ≤ n) {α β : Fin n → ℤ}
    (hα : IsRt (isFiniteType_cartanD n) α) (hβ : IsRt (isFiniteType_cartanD n) β) :
    ∃ w : Wg (isFiniteType_cartanD n), weylAction (isFiniteType_cartanD n) w α = β := by
  refine exists_weylAction_eq_of_isRt (isFiniteType_cartanD n)
    (isIrreducible_cartanD (by omega)) hα hβ ?_
  obtain ⟨wα, i, hαw⟩ := hα
  obtain ⟨wβ, j, hβw⟩ := hβ
  rw [← hαw, ← hβw, form_weylAction, form_weylAction, toRat_single, toRat_single,
    form_single_single, form_single_single]
  rw [levTwoS2d_symmetrizer_const n hn i, levTwoS2d_symmetrizer_const n hn j]

end CFSG.StandardType.LevTwo

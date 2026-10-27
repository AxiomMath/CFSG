module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenConjugateSpan

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {W : Type} [CommGroup W] [Finite W]

theorem s16h_e3_l3_commSub_top_eq_fixV_of_central
    {A L : Subgroup (MulAut W)} {t : MulAut W}
    (hconc : Conc4_136W A t L)
    {τ : MulAut W} (hτC : τ ∈ centSub (commSub (⊤ : Subgroup W) L)) :
    commSub (⊤ : Subgroup W) (Subgroup.zpowers τ) =
      commSub (fixV L) (Subgroup.zpowers τ) := by
  have hsplit : commSub (⊤ : Subgroup W) L ⊔ fixV L = ⊤ :=
    commSub_sup_fixV_eq_top_of_conc4_136W hconc
  have hbot : commSub (commSub (⊤ : Subgroup W) L) (Subgroup.zpowers τ) = ⊥ := by
    rw [commSub_eq_bot_iff]
    intro u hu
    rw [mem_fixV_zpowers]
    exact hτC u hu
  rw [← hsplit, commSub_sup_left, hbot, bot_sup_eq]

end CFSG.LocalAnalysis.UniquenessCase.PartTwo

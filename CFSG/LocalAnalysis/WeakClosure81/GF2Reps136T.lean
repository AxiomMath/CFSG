module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps13FoundA

public section

namespace CFSG.LocalAnalysis.WeakClosure81.GF2Reps136

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.Blueprint (LieModel)
open scoped commutatorElement Pointwise Matrix

variable {W : Type} [CommGroup W] [Finite W]

theorem lemmaT (hw2 : ∀ w : W, w * w = 1) {L R : Subgroup (MulAut W)} (hL : ⁅L, L⁆ = L)
    (hR : ⁅R, R⁆ = R) (hLR : ⁅L, R⁆ = ⊥) (h : commSub (commSub ⊤ L) R ≤ fixV L) :
    commSub (commSub ⊤ L) R = ⊥ := by
  rw [s13_commSub_comm L R hLR] at h ⊢
  refine le_bot_iff.mp (s13_perfect_chain L hL ⊥ (commSub (commSub ⊤ R) L) (commSub ⊤ R) ?_
    le_rfl)
  rw [commSub, Subgroup.closure_le]
  rintro _ ⟨l, hl, y, hy, rfl⟩
  exact Subgroup.mem_bot.mpr (by rw [h hy l hl, mul_inv_cancel])

end CFSG.LocalAnalysis.WeakClosure81.GF2Reps136

module

import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2OmQModelMinus
import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2OmQRank
import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2OmQNatMinus
import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2OmQInstancesMinus
import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2OmQMinusCoreAssembly
import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2OmQWeightDescentGlue
import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2SpCurtisDescent
import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2SpCurtisInterp
import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2SpCurtisWeights
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC8CuUnique
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.GF2RepsC

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
open CFSG.Blueprint (LieModel)

theorem w135c2_omMinus_natural_of_le_six
    {W : Type} [CommGroup W]
    [Finite W] {Y L : Subgroup (MulAut W)} {y : MulAut W} (hW : ∀ w : W, w ^ 2 = 1)
    (hctx : Is135Context Y L) (hyL : y ∈ L) (hy2 : orderOf y = 2)
    (hm : E3.mQuot ⊤ (fixV (Subgroup.zpowers y)) ≤ 6) {n f : ℕ} (hn : 4 ≤ n) (hf : 2 ≤ f)
    (hlie : LieModel (↥L ⧸ Subgroup.center ↥L) .POmegaMinus n 2 f) :
    IsOmegaMinus ↥L (2 * n) f ∧ NatOmegaMinus L ⊤ ⊥ (2 * n) f := by
  classical
  obtain ⟨F, instF, instFin, instChar, b, c, hF, hquad, _, ⟨e⟩⟩ :=
    w135c2_omMinus_model hctx hn hlie
  let instField : Field F := instF
  let instFiniteF : Finite F := instFin
  let instCharP : CharP F 2 := instChar
  obtain ⟨V, _, _, hVfin, ρ, θ, hρ, hθ⟩ := cu_binModel hW (hctx.2.2.2.2.2) e
  let instFiniteV : Finite V := hVfin
  let y' := e.symm ⟨y, hyL⟩
  have hey' : e y' = ⟨y, hyL⟩ := e.apply_symm_apply _
  have hge : ((e y' : ↥L) : MulAut W) = y := by rw [hey']
  have hyy : y * y = 1 := by
    have h := pow_orderOf_eq_one y
    rw [hy2, pow_two] at h
    exact h
  have hy2' : y' * y' = 1 := by
    apply e.injective
    rw [map_mul, map_one, hey']
    exact Subtype.ext hyy
  have hρy : ρ y' ≠ 1 := by
    intro h1
    have hfix : ∀ w : W, (e y' : MulAut W) w = w := by
      intro w
      have h := hθ y' w
      rw [h1] at h
      exact θ.injective (by simpa using h)
    have he1 : (e y' : MulAut W) = 1 := MulEquiv.ext hfix
    have hsub : (⟨y, hyL⟩ : ↥L) = 1 := hey'.symm.trans (Subtype.ext he1)
    have hy1 : y = 1 := by simpa using congrArg Subtype.val hsub
    rw [hy1, orderOf_one] at hy2
    omega
  have hrank : Module.finrank (ZMod 2) (LinearMap.range (ρ y' - 1)) ≤ 6 := by
    rw [← w135c2_omq_mQuot_eq e hθ hge]
    exact hm
  obtain ⟨T, hT⟩ := omq_omMinus_core_of_interfaces
      (omqMinusWeightVectorLong_of_interpolation curtis_root_interpolation)
      (omqMinusWeightVectorShort_of_interpolation curtis_root_interpolation)
      (omqRankFromWeights_of_conj le_finrank_range_sub_one_of_conj)
      (omqMinusDescent_of_extend exists_addEquiv_of_extendScalars_equiv) hn hF hf hquad hρ hy2' hρy
      hrank
  exact w135c2_omMinus_natural_of_equiv hn hF hquad e hθ T hT

end CFSG.LocalAnalysis.WeakClosure81

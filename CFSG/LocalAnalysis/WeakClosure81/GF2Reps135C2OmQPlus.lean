module

import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2OmQModelPlus
import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2OmQRank
import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2OmQNatPlus
import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2OmQInstancePlus
import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2OmQPlusCoreAssembly
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

theorem w135c2_omPlus_natural_of_le_six
    {W : Type} [CommGroup W]
    [Finite W] {Y L : Subgroup (MulAut W)} {y : MulAut W} (hW : ∀ w : W, w ^ 2 = 1)
    (hctx : Is135Context Y L) (hyL : y ∈ L) (hy2 : orderOf y = 2)
    (hm : E3.mQuot ⊤ (fixV (Subgroup.zpowers y)) ≤ 6) {n f : ℕ} (hn : 5 ≤ n) (hf : 2 ≤ f)
    (hlie : LieModel (↥L ⧸ Subgroup.center ↥L) .POmegaPlus n 2 f) :
    IsOmegaPlus ↥L (2 * n) f ∧ NatOmegaPlus L ⊤ ⊥ (2 * n) f := by
  classical
  obtain ⟨F, instF, instFin, instChar, hF, _hZ, ⟨e⟩⟩ :=
    w135c2_omPlus_model hctx (by omega) hlie
  let instField : Field F := instF
  let instFiniteF : Finite F := instFin
  let instCharP : CharP F 2 := instChar
  obtain ⟨V, _, _, hVfin, ρ, θ, hρ, hθ⟩ := cu_binModel hW hctx.2.2.2.2.2 e
  let instFiniteV : Finite V := hVfin
  let y' := e.symm ⟨y, hyL⟩
  have hey : e y' = ⟨y, hyL⟩ := e.apply_symm_apply _
  have hge : ((e y' : ↥L) : MulAut W) = y := by rw [hey]
  have hyy : y * y = 1 := by
    have h := pow_orderOf_eq_one y
    rwa [hy2, pow_two] at h
  have hy2' : y' * y' = 1 := by
    apply e.injective
    rw [map_mul, map_one, hey]
    exact Subtype.ext (by simpa using hyy)
  have hρy : ρ y' ≠ 1 := by
    intro h1
    have hee : (e y' : MulAut W) = 1 := by
      apply MulEquiv.ext
      intro w
      have h := hθ y' w
      rw [h1] at h
      exact θ.injective (by simpa using h)
    have hy'1 : y' = 1 := by
      apply e.injective
      rw [map_one]
      exact Subtype.ext (by simpa using hee)
    have hy1 : y = 1 := by
      rw [← hge, hy'1, map_one]
      simp
    rw [hy1, orderOf_one] at hy2
    omega
  have hrank : Module.finrank (ZMod 2) (LinearMap.range (ρ y' - 1)) ≤ 6 := by
    rw [← w135c2_omq_mQuot_eq e hθ hge]
    exact hm
  obtain ⟨T, hT⟩ := omq_omPlus_core_of_interfaces
      (omqPlusWeightVector_of_interpolation curtis_root_interpolation)
      (omqRankFromWeights_of_conj le_finrank_range_sub_one_of_conj)
      (omqPlusDescent_of_extend exists_addEquiv_of_extendScalars_equiv) hn hF hf hρ hy2' hρy hrank
  exact w135c2_omPlus_natural_of_equiv (by omega) hF e hθ T hT

end CFSG.LocalAnalysis.WeakClosure81

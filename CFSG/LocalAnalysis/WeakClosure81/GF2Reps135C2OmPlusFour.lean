module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2OmPlusFourCore
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC8CuUnique
import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2NatB
import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2OmQModelPlus
import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2OmQNatPlus
import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2OmQRank
import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2PsuOuterInvolution
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135Defs

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
open CFSG.Blueprint (LieModel)

theorem w135c2_omPlus_four_natural_of_le_six
    {W : Type} [CommGroup W]
    [Finite W] {Y L : Subgroup (MulAut W)} {y : MulAut W} (hW : ∀ w : W, w ^ 2 = 1)
    (hctx : Is135Context Y L) (hyL : y ∈ L) (hy2 : orderOf y = 2)
    (hm : E3.mQuot ⊤ (fixV (Subgroup.zpowers y)) ≤ 6) {f : ℕ} (hf : 2 ≤ f)
    (hlie : LieModel (↥L ⧸ Subgroup.center ↥L) .POmegaPlus 4 2 f) :
    IsOmegaPlus ↥L 8 f ∧ NatOmegaPlus L ⊤ ⊥ 8 f := by
  classical
  obtain ⟨F, instF, instFin, instChar, hF, _hZ, ⟨e⟩⟩ :=
    w135c2_omPlus_model hctx (by norm_num) hlie
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
  obtain ⟨γ, T, hT⟩ := omq_omPlus_core_four hF hf hρ hy2' hρy hrank
  exact w135c2_omPlus_natural_of_equiv (n := 4) (by norm_num) hF (γ.trans e)
    (ρ := ρ.comp γ.toMonoidHom) (θ := θ) (fun s w => hθ (γ s) w) T hT

theorem w135c2_omPlus_four_f2
    {W : Type} [CommGroup W] [Finite W] {Y L : Subgroup (MulAut W)}
    {t : MulAut W} (hW : ∀ w : W, w ^ 2 = 1) (hctx : Is135Context Y L) (htY : t ∈ Y)
    (ht2 : orderOf t = 2) (hm : E3.mQuot ⊤ (fixV (Subgroup.zpowers t)) ≤ 3) {f : ℕ}
    (hf : 2 ≤ f) (hlie : LieModel (↥L ⧸ Subgroup.center ↥L) .POmegaPlus 4 2 f) :
    W4Lem13_5Concl W Y L t := by
  obtain ⟨y, hyL, hy1, hyy, hym⟩ := w135c2_psu_outer_involution hW hctx htY ht2
  have hy2 : orderOf y = 2 := orderOf_eq_prime (by rwa [pow_two]) hy1
  obtain ⟨hIs, hNat⟩ :=
    w135c2_omPlus_four_natural_of_le_six hW hctx hyL hy2 (by omega) hf hlie
  exact w135c2_natural hctx htY ht2 hW
    (Or.inl ⟨8, f, Or.inr (Or.inr (Or.inl ⟨hIs, hNat⟩))⟩)

end CFSG.LocalAnalysis.WeakClosure81

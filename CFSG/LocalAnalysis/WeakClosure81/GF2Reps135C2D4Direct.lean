module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2ExcRank
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2ExcTri
import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2D4ClassA
import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2D4ClassB
import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2D4Outer
import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2Ctx
import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135Ctx
public import CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisExc.BinRep
public import CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisExc.OffenderData
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LiftSaturate
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.SL2ModulesAlt5Split
public import CFSG.LocalAnalysis.QuasithinUnique.K1.EvenClassicalFamily
public import CFSG.LocalAnalysis.QuasithinUnique.K1.EvenClassicalLinearStrong
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2Defs
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2ExcPeriodic
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2ExcTag
public import CFSG.Quasithin.Background.FFC4Pair
public import CFSG.Quasithin.Background.FFC4Tr2
public import CFSG.Quasithin.Background.SmithB42L2L32
public import CFSG.Quasithin.Background.SmithB42L2Nat
public import CFSG.Quasithin.Background.SmithB51LnRealB

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
open CFSG.Blueprint (LieModel)


variable {W : Type} [CommGroup W] [Finite W] {Y L : Subgroup (MulAut W)} {t : MulAut W}

theorem w135c2_four_le_mQuot_trialityD4_direct (hW : ∀ w : W, w ^ 2 = 1)
    (hctx : Is135Context Y L) (htY : t ∈ Y) (ht2 : orderOf t = 2) {n f : ℕ}
    (hlie : LieModel (↥L ⧸ Subgroup.center ↥L) .trialityD4 n 2 f) :
    4 ≤ E3.mQuot ⊤ (fixV (Subgroup.zpowers t)) := by
  classical
  have hq : IsQuasisimple ↥L := hctx.2.2.2.2.1
  have hodd : Odd (Nat.card (Subgroup.center ↥L)) := w135_odd_card_center hctx
  have hX := CFSG.Blueprint.LieModel.chevalleyExceptionalModel hlie (by decide)
  have hZ : Subgroup.center ↥L = ⊥ := by
    have : Group.IsPerfect ↥L := hq.1
    have h0 := CFSG.SectionRank.triality_even_perfect_odd_cover_trivial hX
      (QuotientGroup.mk' (Subgroup.center ↥L)) (QuotientGroup.mk'_surjective _)
      (QuotientGroup.ker_mk' _).le
      (by rw [QuotientGroup.ker_mk']; exact hodd)
    rwa [QuotientGroup.ker_mk'] at h0
  obtain ⟨hf, K, _, _, σ, hK, hσ, ⟨e⟩⟩ :=
    CFSG.QuasithinUnique.Setup.X6.exists_mulEquiv_triality_model hX
  have hrk : 24 * f ≤ rk W := w135c2_twentyFour_mul_le_rk_of_triality hW hctx hlie
  haveI hchar : CharP K 2 := CFSG.Quasithin.B42D4.charP_two_of_card hf hK
  have hσ3 : σ.toRingHom ^ 3 = 1 := CFSG.Quasithin.B42D4.sigma_cube hK σ hσ
  by_cases htL : t ∈ L
  · let x : ↥L := ⟨t, htL⟩
    have htt : t * t = 1 := by
      have h := pow_orderOf_eq_one t
      rw [ht2, pow_two] at h
      exact h
    have ht1 : t ≠ 1 := by
      intro h
      rw [h, orderOf_one] at ht2
      omega
    have hx2 : x * x = 1 := by
      apply Subtype.ext
      change t * t = 1
      exact htt
    have hx1 : x ≠ 1 := fun h => ht1 (congrArg Subtype.val h)
    have hξ2 : CFSG.Quasithin.B42Disp.modelProj L e x *
        CFSG.Quasithin.B42Disp.modelProj L e x = 1 := by
      rw [← map_mul, hx2, map_one]
    have hξ1 : CFSG.Quasithin.B42Disp.modelProj L e x ≠ 1 := by
      intro h
      exact hx1 (CFSG.Quasithin.B45Tor.modelProj_injective L hZ e (by rw [h, map_one]))
    have hEq : E3.mQuot ⊤ (fixV (Subgroup.zpowers (x : MulAut W))) =
        E3.mQuot ⊤ (fixV (Subgroup.zpowers t)) := rfl
    rcases CFSG.Quasithin.B42D4.involution_conj σ hσ3
        (CFSG.Quasithin.B42Disp.modelProj L e x) hξ2 hξ1 with hA | hB
    · have h4x : 4 ≤ E3.mQuot ⊤ (fixV (Subgroup.zpowers (x : MulAut W))) :=
        w135c2_trialityD4_classA hf hK σ hσ e hW hctx hZ hrk hA
      rw [hEq] at h4x
      exact h4x
    · have h12x : 12 * f ≤ E3.mQuot ⊤ (fixV (Subgroup.zpowers (x : MulAut W))) :=
        w135c2_trialityD4_classB hf hK σ hσ e hW hZ hB
      rw [hEq] at h12x
      omega
  · exact w135c2_trialityD4_outer hf hK σ hσ e hW hctx hZ htY ht2 htL

end CFSG.LocalAnalysis.WeakClosure81

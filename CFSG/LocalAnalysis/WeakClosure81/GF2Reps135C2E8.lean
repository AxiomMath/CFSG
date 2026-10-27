module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2ExcGs
public import CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisExc.E8Reduction
import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2ExcPeriodic
import CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisExc.E8MinDegAll
public import CFSG.RankThree.PartOne.S11d.OutAbstract

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
open CFSG.Blueprint (LieModel ChevalleyExceptionalModel UntwistedChevalleyModel)
open CFSG.Blueprint.Chevalley
open CFSG.Quasithin.SmithCurtis CFSG.Quasithin.SmithCurtis.Chev
open CFSG.HardMathSupport.Cooperstein.Coordinator
open CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisExc


variable {W : Type} [CommGroup W] [Finite W] {Y L : Subgroup (MulAut W)} {t : MulAut W}

theorem w135c2_e8_le_rk (hW : ∀ w : W, w ^ 2 = 1) (hctx : Is135Context Y L) {n f : ℕ}
    (hlie : LieModel (↥L ⧸ Subgroup.center ↥L) .E8 n 2 f) : 248 ≤ rk W := by
  classical
  have hW' : ∀ w : W, w * w = 1 := fun w => by rw [← sq]; exact hW w
  have hmodel : ChevalleyExceptionalModel (↥L ⧸ Subgroup.center ↥L) .E8 2 f :=
    hlie.chevalleyExceptionalModel (by decide)
  have hadm : StatedLieAdmissible .E8 0 2 f := hmodel.1
  have hun : UntwistedChevalleyModel (↥L ⧸ Subgroup.center ↥L) .E8 (2 ^ f) := hmodel.2
  obtain ⟨K, _, _, hK, ⟨e0⟩⟩ := hun
  have hf : 1 ≤ f := hadm.2.1
  have hK2 : CharP K 2 :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
      Nat.prime_two hf hK
  have hql : CFSG.IsQuasisimple ↥L := hctx.2.2.2.2.1
  have hZ : Subgroup.center ↥L = ⊥ := center_eq_bot_of_E8 hql hf hK e0
  let eS : (↥L ⧸ Subgroup.center ↥L) ≃* adjointGroup .E8 K :=
    e0.trans (adjointQuotientEquiv K)
  let eL : (↥L ⧸ Subgroup.center ↥L) ≃* ↥L :=
    (QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot
  let ι : adjointGroup .E8 K ≃* ↥L := eS.symm.trans eL
  have hnt : Nontrivial (adjointGroup .E8 K) :=
    ⟨⟨xC .E8 K n8 1, 1, xC_ne_one n8 1⟩⟩
  obtain ⟨δ, m, k, _, _, _, ιK, ρ, hδ, hm, hρirr, hρinj, -, hWcard, -⟩ :=
    w135c2_periodic_data hW' (w135c2_x1IsIrrOn_of_ctx hctx) ι hf hK
  let : Algebra K k := ιK.toAlgebra
  have hρ : IsSimpleRep ρ :=
    (CFSG.QuasithinUnique.Setup.SL2Modules.isIrreducible_iff ρ).1 hρirr
  obtain ⟨y, χ, J, ht⟩ := exists_isChevType (hw := exists_weyl_neg_E8) (p := 2) hρ
  have hnper : ∀ (i : Fin Tag.E8.rank) (t : Kˣ),
      χ (dC .E8 K i t) ^ (2 ^ f) = χ (dC .E8 K i t) :=
    fun i t => chi_dC_pow_card hρ ht hK i t
  have hB := typeBound_of_minDeg hf hK (e8MinDeg K)
  have h248 : 248 ≤ m :=
    (hB k m ρ y χ J f hρ hρinj ht hf dvd_rfl hnper).1 (Nat.div_self (by omega))
  have hcard : Nat.card W = 2 ^ rk W :=
    card_eq_two_pow_of_isPGroup (isPGroup_two_of_sq_eq_one hW)
  have hrk : rk W = δ * m :=
    Nat.pow_right_injective (le_refl 2) (by
      change 2 ^ rk W = 2 ^ (δ * m)
      rw [← hcard, hWcard])
  calc 248 ≤ m := h248
    _ ≤ δ * m := Nat.le_mul_of_pos_left m (by omega)
    _ = rk W := hrk.symm

theorem w135c2_four_le_mQuot_e8 (hGS : GS03AlphaFor fun s _ _ => s = .E8)
    (hW : ∀ w : W, w ^ 2 = 1) (hctx : Is135Context Y L) (htY : t ∈ Y) (ht2 : orderOf t = 2)
    {n f : ℕ} (hlie : LieModel (↥L ⧸ Subgroup.center ↥L) .E8 n 2 f) :
    4 ≤ E3.mQuot ⊤ (fixV (Subgroup.zpowers t)) := by
  have h := w135c2_e8_le_rk hW hctx hlie
  exact w135c2_four_le_mQuot_of_gs03 hGS hW hctx htY ht2 rfl hlie (by simp only [gs03Bound]; omega)

end CFSG.LocalAnalysis.WeakClosure81

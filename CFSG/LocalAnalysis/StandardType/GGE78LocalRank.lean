module

public import CFSG.LocalAnalysis.StandardType.GGB36Defs
public import CFSG.LocalAnalysis.StandardType.GGSixLSixSevenA3ExcRank
public import CFSG.LocalAnalysis.StandardType.GGTableBExcBasic
public import CFSG.HardMathSupport.Meierfrankenfeld.Proving.E7Curtis.E7Arith
public import CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisExc.E8Arith
public import CFSG.LocalAnalysis.GLTheoremA.S12.CanonInnBridge
public import CFSG.LocalAnalysis.ComponentClassification.AssemblyBPredicates
public import CFSG.LieType.Simplicity.Exceptional
public import CFSG.GH74.GLS.IVK.Proofs2.OddTools
public import CFSG.GH74.GLS.Stage2.Local.P34Main
public import CFSG.GH74.GLS.Stage2.Local.P34S5A
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87CoatomAbs
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87GenCell
public import CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisExc.ChevIndep
public import CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisExc.GenPeriodic
public import CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisExc.OuterTwist
public import CFSG.HardMathSupport.Solomon.LocalBalance.ScpQuot
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Inputs
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec7Layer
public import CFSG.LocalAnalysis.EvenBN.Common.CommutatorFixed
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10FBase2
public import CFSG.LocalAnalysis.GLTheoremA.CatA.YS1011U64Types
public import CFSG.LocalAnalysis.GLTheoremA.S10.Inputs105
public import CFSG.LocalAnalysis.GLTheoremA.S10.InputsBeta
public import CFSG.LocalAnalysis.GLTheoremA.S10.InputsSetup
public import CFSG.LocalAnalysis.GLTheoremA.S11.Inputs119
public import CFSG.LocalAnalysis.GLTheoremA.S12.Bridge
public import CFSG.LocalAnalysis.GLTheoremA.S12.Prop123
public import CFSG.LocalAnalysis.GLTheoremA.Sec5Setup
public import CFSG.LocalAnalysis.GLTheoremB.Lemma911Proof
public import CFSG.SignalizerFunctorTheorem.Nonsolvable.SolComponent

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial

private lemma ltqRk_e7_recipe_data {R : Type} [Group R] {n : ℕ}
    (h : GGHasLabel (⟨.E7, 0, n⟩ : LargeEvenLabel) R) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = 2 ^ n ∧
      Nonempty (R ≃* LargeEvenCenterQuot (LargeEvenChevH (LargeEvenCartanE 7) K false)) := by
  simpa only [GGHasLabel, LargeEvenRawDatum, LargeEvenRecipeChevalley] using h

private lemma ltqRk_e8_recipe_data {R : Type} [Group R] {n : ℕ}
    (h : GGHasLabel (⟨.E8, 0, n⟩ : LargeEvenLabel) R) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = 2 ^ n ∧
      Nonempty (R ≃* LargeEvenCenterQuot (LargeEvenChevH (LargeEvenCartanE 8) K false)) := by
  simpa only [GGHasLabel, LargeEvenRawDatum, LargeEvenRecipeChevalley] using h

private lemma ltqRk_rank_goal {X : Type} [Group X] [Finite X]
    (hZ : Subgroup.center X = ⊥) {k : ℕ} (hk : k ≤ LargeEvenTwoLocalRank 3 X) (h6 : 6 ≤ k) :
    6 + (if 3 ∣ Nat.card (Subgroup.center X) then 1 else 0) ≤ LargeEvenTwoLocalRank 3 X := by
  rw [hZ, Subgroup.card_bot, if_neg (by decide : ¬ 3 ∣ (1 : ℕ)), add_zero]
  omega

theorem ggE78LocalRankThree_holds :
    GGE78LocalRankThree := by
  intro X _ _ lab hΛ htag hlab hperf
  obtain ⟨t, r, n⟩ := lab
  rcases htag with h7 | h8
  ·
    subst h7
    have hn : 1 ≤ n := hΛ.1
    have hr : r = 0 := hΛ.2
    subst hr
    obtain ⟨K, hKfield, hKfin, hKcard, hQK⟩ := ltqRk_e7_recipe_data hlab
    obtain ⟨eθ⟩ := hQK
    let eR : LargeEvenCenterQuot (LargeEvenChevH (LargeEvenCartanE 7) K false) ≃*
        ↥(adjointGroup Tag.E7 K) := TableBExc.recipeEquiv Tag.E7 K
    let hZk : Subgroup.center ↥(adjointGroup Tag.E7 K) = ⊥ :=
      CFSG.LieType.Chevalley.center_adjointGroup_eq_bot (τ := Tag.E7) (K := K)
    let eAdj : ↥(adjointGroup Tag.E7 K) ≃* AdjointQuotient Tag.E7 K :=
      ((QuotientGroup.quotientMulEquivOfEq hZk).trans QuotientGroup.quotientBot).symm
    let eC : (X ⧸ Subgroup.center X) ≃* AdjointQuotient Tag.E7 K := eθ.trans (eR.trans eAdj)
    haveI : CharP K 2 := finite_field_prime_power_characteristic Nat.prime_two hn hKcard
    have hsimple : IsSimpleGroup (X ⧸ Subgroup.center X) := by
      haveI : IsSimpleGroup (AdjointQuotient Tag.E7 K) :=
        (CFSG.LieType.Simplicity.isQuasisimple_adjointGroup_e7 K).2.1
      exact (MulEquiv.isSimpleGroup_congr eC).mpr inferInstance
    have hq : CFSG.IsQuasisimple X :=
      (CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native X).mp
        ⟨hperf, hsimple⟩
    have hZ : Subgroup.center X = ⊥ :=
      CFSG.HardMathSupport.Meierfrankenfeld.Proving.E7Curtis.center_eq_bot_of_E7 hq hn hKcard eC
    let eAdjX : ↥(adjointGroup Tag.E7 K) ≃* X :=
      eAdj.trans (eC.symm.trans (CFSG.LocalAnalysis.GLTheoremA.CanonInn.quotCenterEquivOfBot hZ))
    let χ : adjointGroup Tag.E7 K →* X := eAdjX.toMonoidHom
    have hχ : Function.Injective χ := eAdjX.injective
    rcases three_dvd_two_pow_pred_or_succ n with hdiv | hdiv
    ·
      have hp3 : (3 : ℕ).Prime := by norm_num
      have hpK : 3 ∣ Nat.card K - 1 := by rw [hKcard]; exact hdiv
      have h7r : 7 ≤ LargeEvenTwoLocalRank 3 X :=
        ExcFrames.rank_le_twoLocalRank (τ := Tag.E7) (by decide) hp3 hpK
          (TableBExc.isUnit_det_cartan_of_eq (τ := Tag.E7) hp3 det_cartan_E7 (by decide)) χ hχ
      exact ltqRk_rank_goal hZ h7r (by norm_num)
    ·
      have hp3 : (3 : ℕ).Prime := by norm_num
      have hpK : 3 ∣ Nat.card K + 1 := by rw [hKcard]; exact hdiv
      have h6r : 6 ≤ LargeEvenTwoLocalRank 3 X := by
        have h := rank_pred_le_twoLocalRank_of_half (τ := Tag.E7) hp3 χ hχ
          (ExcFramesHalf.ggExcHalfTwoLocalInput_E7 K 3 hp3 (by norm_num) hpK (Or.inl rfl))
        exact h
      exact ltqRk_rank_goal hZ h6r (by norm_num)
  ·
    subst h8
    have hn : 1 ≤ n := hΛ.1
    have hr : r = 0 := hΛ.2
    subst hr
    obtain ⟨K, hKfield, hKfin, hKcard, hQK⟩ := ltqRk_e8_recipe_data hlab
    obtain ⟨eθ⟩ := hQK
    let eR : LargeEvenCenterQuot (LargeEvenChevH (LargeEvenCartanE 8) K false) ≃*
        ↥(adjointGroup Tag.E8 K) := TableBExc.recipeEquiv Tag.E8 K
    let hZk : Subgroup.center ↥(adjointGroup Tag.E8 K) = ⊥ :=
      CFSG.LieType.Chevalley.center_adjointGroup_eq_bot (τ := Tag.E8) (K := K)
    let eAdj : ↥(adjointGroup Tag.E8 K) ≃* AdjointQuotient Tag.E8 K :=
      ((QuotientGroup.quotientMulEquivOfEq hZk).trans QuotientGroup.quotientBot).symm
    let eC : (X ⧸ Subgroup.center X) ≃* AdjointQuotient Tag.E8 K := eθ.trans (eR.trans eAdj)
    haveI : CharP K 2 := finite_field_prime_power_characteristic Nat.prime_two hn hKcard
    have hsimple : IsSimpleGroup (X ⧸ Subgroup.center X) := by
      haveI : IsSimpleGroup (AdjointQuotient Tag.E8 K) :=
        CFSG.LieType.Simplicity.isSimpleGroup_adjointQuotient_e8 K
      exact (MulEquiv.isSimpleGroup_congr eC).mpr inferInstance
    have hq : CFSG.IsQuasisimple X :=
      (CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native X).mp
        ⟨hperf, hsimple⟩
    have hZ : Subgroup.center X = ⊥ :=
      CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisExc.center_eq_bot_of_E8 hq hn hKcard eC
    let eAdjX : ↥(adjointGroup Tag.E8 K) ≃* X :=
      eAdj.trans (eC.symm.trans (CFSG.LocalAnalysis.GLTheoremA.CanonInn.quotCenterEquivOfBot hZ))
    let χ : adjointGroup Tag.E8 K →* X := eAdjX.toMonoidHom
    have hχ : Function.Injective χ := eAdjX.injective
    rcases three_dvd_two_pow_pred_or_succ n with hdiv | hdiv
    ·
      have hp3 : (3 : ℕ).Prime := by norm_num
      have hpK : 3 ∣ Nat.card K - 1 := by rw [hKcard]; exact hdiv
      have h8r : 8 ≤ LargeEvenTwoLocalRank 3 X :=
        ExcFrames.rank_le_twoLocalRank (τ := Tag.E8) (by decide) hp3 hpK
          (TableBExc.isUnit_det_cartan_of_eq (τ := Tag.E8) hp3 det_cartan_E8 (by decide)) χ hχ
      exact ltqRk_rank_goal hZ h8r (by norm_num)
    ·
      have hp3 : (3 : ℕ).Prime := by norm_num
      have hpK : 3 ∣ Nat.card K + 1 := by rw [hKcard]; exact hdiv
      have h7r : 7 ≤ LargeEvenTwoLocalRank 3 X := by
        have h := rank_pred_le_twoLocalRank_of_half (τ := Tag.E8) hp3 χ hχ
          (ExcFramesHalf.ggExcHalfTwoLocalInput_E8 K 3 hp3 (by norm_num) hpK (Or.inl rfl))
        exact h
      exact ltqRk_rank_goal hZ h7r (by norm_num)

end CFSG.StandardType

end

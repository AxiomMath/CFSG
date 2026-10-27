module

public import CFSG.LocalAnalysis.StandardType.GGTBRowExcFrame
public import CFSG.LocalAnalysis.StandardType.GGTBRowE6Equiv
public import CFSG.LocalAnalysis.StandardType.GGTBRowTwE6Parity
public import CFSG.LocalAnalysis.StandardType.GGNbrReflGenNonSplitTwE6Plus
public import CFSG.LocalAnalysis.StandardType.GGTableBTwE6Delta
public import CFSG.LocalAnalysis.StandardType.GGTableBTwE6RankOuter
public import CFSG.LocalAnalysis.StandardType.GGNbrInnerWeylTwE6Lift
public import CFSG.LocalAnalysis.StandardType.GGForkJrPumpLattice

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

theorem ggTwE6Row_ggTorusWeylFrameW_twE6Plus
    {n p : ℕ} (hn : 1 ≤ n) {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = (2 ^ n) ^ 2) (hp : p.Prime) (hp5 : 5 ≤ p) (hpn : p ∣ 2 ^ n + 1) :
    GGTorusWeylFrameW p 5 (TwE6Delta.RecipeR K n) (TwE6Delta.RecipeI K n) CoxeterMatrix.E₆ := by
  have hp2 : p ≠ 2 := by omega
  have hp3 : p ≠ 3 := by omega
  haveI : CharP K 2 := charP_two_of_card (K := K) (m := 2 * n) (by rw [hK, ← pow_mul, mul_comm])
  obtain ⟨e⟩ := TwE6Rank.exists_mulEquiv_graphFixedRootGroup hn hK (iterateFrobenius K 2 n)
    (fun c => iterateFrobenius_def 2 n c)
  exact ggTorusWeylFrameW_of_excPlusModelSCr (τ := Tag.E6) (M := CoxeterMatrix.E₆) hp hp2
    ggE6Row_coxeterGroupEquiv
    ggE6Row_coxeterGroupEquiv_simple
    (ggExcPlusWeylModelSCr_of_frameModelOn hp (TwE6Delta.center_recipeR_eq_bot hn hK)
      (fun φ hφ hφp => TwE6Delta.ggOutdiagPrime_twE6 hn hK hp hp3 φ hφ hφp)
      (TwE6Delta.ggCenterPrime_twE6 hn hK hp hp2 hp3)
      ((excPlusFrameModelOn_twE6Plus hp hp5 hn hpn K hK (iterateFrobenius K 2 n)
        (fun c => iterateFrobenius_def 2 n c)).of_mulEquiv e))

theorem ggTwE6Row_labelAll_frame
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {lab : LargeEvenLabel}
    (hlab : LargeEvenInLambda2 lab) (h : GGTBTwE6PlusLabel p lab) :
    LargeEvenLabelAll lab fun R _ I _ =>
      ∃ r, GGTorusLift p r R ∧ GGTorusWeylFrameW p r R I CoxeterMatrix.E₆ := by
  obtain ⟨htag, hpn, hp3⟩ := h
  have hp5 : 5 ≤ p := by
    have h2 := hp.two_le
    have h4 : p ≠ 4 := fun h4 => by subst h4; exact absurd hp (by norm_num)
    omega
  have hW : LargeEvenLabelAll lab fun R _ I _ =>
      GGTorusWeylFrameW p 5 R I CoxeterMatrix.E₆ :=
    TwE6Delta.labelAll htag fun K _ _ hK =>
      ggTwE6Row_ggTorusWeylFrameW_twE6Plus hlab.1 hK hp hp5 hpn
  refine (largeEvenLabelAll_and
    (largeEvenLabelAll_torusLift_twE6Add_holds hp hlab ⟨htag, hpn⟩) hW).mono
    fun _ _ _ _ ⟨hl, hw⟩ => ⟨5, ?_, hw⟩
  rwa [TwE6Delta.liftRank_of_ne hp3] at hl

theorem ggTwE6Row_labelAllGuard_frame
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {lab : LargeEvenLabel}
    (hlab : LargeEvenInLambda2 lab) (h : GGTBTwE6PlusLabel p lab) :
    LargeEvenLabelAll lab (LargeEvenSimpleGuard fun R _ I _ =>
      ∃ r, GGTorusLift p r R ∧ GGTorusWeylFrameW p r R I CoxeterMatrix.E₆) :=
  LargeEvenLabelAll.mono (fun _ _ _ _ hP _ _ => hP) (ggTwE6Row_labelAll_frame hp hp2 hlab h)

end CFSG.StandardType

end


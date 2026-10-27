module

public import CFSG.LocalAnalysis.StandardType.GGTwE6KGLPairs
import CFSG.HardMathSupport.Dickson.Bal207.CompShape
import CFSG.HardMathSupport.Dickson.Bal207.FamF42
import CFSG.LocalAnalysis.ComponentInitial.SymplecticFlagOrder
import CFSG.LocalAnalysis.SeitzReduction.F4PilotCatEvenExcOrders
import CFSG.LocalAnalysis.StandardType.GGRecipeFieldExcOut
import CFSG.LocalAnalysis.StandardType.GGTwE6KGLNoJ1MarkTriality
import CFSG.LocalAnalysis.StandardType.GGTwE6KGLNoJ1Ppd
import CFSG.LocalAnalysis.StandardType.Marking
import CFSG.Timmesfeld.Orders.ExceptionalTwisted
import CFSG.Timmesfeld.Orders.ExceptionalUntwisted
import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.SRTReeF4

public section

namespace CFSG.StandardType.SCFourCover

open CFSG CFSG.Assembly CFSG.Blueprint CFSG.Open TableB
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup)
open CFSG.HardMathSupport.Dickson.Bal207.FamF42 (F42CompType isoInvariant_f42CompType
  compShape_F4_two)

private theorem card_dvd_of_f42CompType_f4Two {Q : Type} [Group Q] (h : F42CompType Q) :
    Nat.card Q ∣ 1451520 := by
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := h
  rw [Nat.card_congr e.toEquiv]
  refine (Subgroup.card_quotient_dvd_card _).trans ?_
  rw [CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.card_statedSp, hF]
  decide +kernel

private theorem aPair_arith_f4Two (n : ℕ) (hn : 1 ≤ n) :
    ¬ ordA 2 (2 ^ (3 * n)) ∣ ordF4 (2 ^ 1) ∧ ¬ ordTwistedA 2 (2 ^ (3 * n)) ∣ ordF4 (2 ^ 1) := by
  have hP := CFSG.SeitzReduction.F4Pilot.EvenExc.profile_ordF4' (le_refl 1)
  have key : ∀ k, 9 ∣ k → ¬ (k ∣ 1 * 12 ∨ k ∣ 1 * 8 ∨ k ∣ 1 * 6 ∨ k ∣ 1 * 2) := by
    rintro k h9 (h | h | h | h) <;> · have := h9.trans h; omega
  obtain ⟨p, hp, hpM⟩ := exists_ppd_dvd_ordA_two_nine hn
  obtain ⟨p', hp', hpM'⟩ := exists_ppd_dvd_ordTwistedA_two_eighteen hn
  exact ⟨fun h => key _ ⟨n, rfl⟩ ((hP.prim p _ hp (by omega)).1 (hpM.trans h)),
    fun h => key _ ⟨2 * n, by ring⟩ ((hP.prim p' _ hp' (by omega)).1 (hpM'.trans h))⟩

section TriD4


private theorem f42CompType_of_isComponentOf_f4Two {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 2)
    {s : MulAut (LargeEvenCenterQuot (LargeEvenChevH LargeEvenCartanF4 K false))}
    (hs3 : s ^ 3 = 1) (hs1 : s ≠ 1)
    {J₁ : Subgroup (LargeEvenCenterQuot (LargeEvenChevH LargeEvenCartanF4 K false))}
    (hJ : CFSG.Open.IsComponentOf J₁ (fixSubgroup s)) :
    F42CompType (↥J₁ ⧸ Subgroup.center ↥J₁) := by
  let e : LargeEvenCenterQuot (LargeEvenChevH LargeEvenCartanF4 K false) ≃*
      Chevalley.adjointGroup .F4 K := recipeChevEquiv .F4 K
  have h3 : MulAut.congr e s ^ 3 = 1 := by rw [← map_pow, hs3, map_one]
  have h1 : MulAut.congr e s ≠ 1 := fun h => hs1 ((MulAut.congr e).map_eq_one_iff.1 h)
  exact (CFSG.HardMathSupport.Dickson.Bal207.CompShape.of_congr isoInvariant_f42CompType e
    (compShape_F4_two hK _ h3 h1)).type J₁ hJ

theorem ggInndiagOnCompAt_F4_two_triD4 {lab : LargeEvenLabel} (htag : lab.tag = .F4)
    (hn : lab.n = 1) : GGInndiagOnCompAt lab fun n l => l = ⟨.triD4, 0, n⟩ := by
  obtain ⟨t, r, g⟩ := lab
  dsimp only at htag hn
  subst htag hn
  intro Q hQ
  dsimp only [LargeEvenRawDatum] at hQ ⊢
  obtain ⟨K, i1, i2, hK, hq⟩ := hQ
  refine ⟨K, i1, i2, hK, hq, ?_⟩
  intro _ _ _ s _ n hs3 hs1 _ _ _ _ _ J₁ hJ₁ hmark _
  have hJ : CFSG.Open.IsComponentOf J₁ (fixSubgroup s) := by
    have hfix : ggFix s = fixSubgroup s := Subgroup.ext fun _ => Iff.rfl
    rw [← hfix]
    exact CFSG.Assembly.isComponentOf_iff_open.1 hJ₁
  have hd := card_dvd_of_f42CompType_f4Two
    (f42CompType_of_isComponentOf_f4Two (hK.trans (pow_one 2)) hs3 hs1 hJ)
  obtain ⟨-, lab', hlab, hraw⟩ := hmark
  obtain ⟨_, _, _, _, -, -, -, rfl⟩ := largeEvenRawDatum_exists hraw
  dsimp only [CFSG.Assembly.LargeEvenRawDatumLegacy] at hraw
  obtain ⟨L, _, _, hL, -, -, θ, -⟩ := hraw
  have hc : Nat.card (↥J₁ ⧸ Subgroup.center ↥J₁) = ordTrialityD4 (2 ^ n) :=
    (Nat.card_congr θ.toEquiv).trans
      (CFSG.Timmesfeld.ExceptionalOrders.card_of_twistedChevalleyModel_D4_two hlab.1
        (twistedChevalleyModel_largeEven .D4 hL))
  have h2 : ordTrialityD4 (2 ^ n) ≤ 1451520 := by
    rw [← hc]
    exact Nat.le_of_dvd (by norm_num) hd
  exact absurd ((ordTrialityD4_two_pow_le (g := 1) (n := n) hlab.1 (one_dvd n)).trans h2)
    (not_le.2 (by decide +kernel))

end TriD4

section APair


theorem ggInndiagOnCompAt_F4_two_aPair {lab : LargeEvenLabel} (hlab : LargeEvenInLambda2 lab)
    (htag : lab.tag = .F4) (hn : lab.n = 1) :
    GGInndiagOnCompAt lab fun n l => l = ⟨.A, 2, 3 * n⟩ ∨ l = ⟨.twA, 2, 3 * n⟩ := by
  have hc : LargeEvenLabelAll lab fun R _ _ _ => Nat.card R = ordF4 (2 ^ 1) := by
    obtain ⟨t, r, g⟩ := lab
    dsimp only at htag hn
    subst htag hn
    intro Q hQ
    dsimp only [LargeEvenRawDatum] at hQ ⊢
    obtain ⟨K, i1, i2, hK, hq⟩ := hQ
    exact ⟨K, i1, i2, hK, hq, CFSG.Timmesfeld.ExceptionalOrders.card_of_untwistedChevalleyModel_F4
      (untwistedChevalleyModel_largeEven .F4 hK)⟩
  exact ggInndiagOnCompAt_of_noJ1 hlab (fun n => 3 * n)
    (fun _ _ h => by rcases h with rfl | rfl <;> exact ⟨by simp, rfl⟩)
    (largeEvenLabelAll_noJ1_aPair_of_card hc (by decide +kernel)
      (fun n hn _ _ => Or.inl (aPair_arith_f4Two n hn).1)
      (fun n hn _ _ => Or.inl (aPair_arith_f4Two n hn).2))

end APair

end CFSG.StandardType.SCFourCover

end

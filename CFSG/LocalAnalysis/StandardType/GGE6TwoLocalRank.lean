module

public import CFSG.LocalAnalysis.StandardType.GGExcTwoCompList
public import CFSG.LocalAnalysis.StandardType.GGSixE6A24Centre
public import CFSG.LocalAnalysis.StandardType.GGTableBExcBasic
public import CFSG.Adapters.TauCetiExceptional.EvenBridgeE6E7
public import CFSG.HardMathSupport.Timmesfeld.Tables.Census.FieldBonusIso
public import CFSG.RankThree.PartTwo.Census.Exceptional.LocalRankThreeTwo
public import CFSG.LocalAnalysis.GLTheoremA.S12.CanonInnBridge
public import CFSG.CharacterTheory.Wreathed.BrauerWongTypes
public import CFSG.CharacterTheory.Wreathed.WreathCentralSquare
public import CFSG.HardMathSupport.Solomon.LocalBalance.ScpQuot
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Inputs
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec7Layer
public import CFSG.HardMathSupport.Timmesfeld.ComponentBalance.I_11_6_Defs
public import CFSG.HardMathSupport.Timmesfeld.Tables.Census.Witness
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
public import CFSG.LocalAnalysis.GLTheoremB.Lemma99Inputs
public import CFSG.LocalAnalysis.SignalizerFunctor
public import CFSG.Quasithin.Background.A3ComponentsAmbient
public import CFSG.SignalizerFunctorTheorem.Nonsolvable.SolComponent

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley

private lemma ltqLr_e6_recipe_data {R : Type} [Group R]
    (h : GGHasLabel (⟨.E6, 0, 1⟩ : LargeEvenLabel) R) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = 2 ∧
      Nonempty (R ≃* LargeEvenCenterQuot (LargeEvenChevH (LargeEvenCartanE 6) K false)) := by
  simpa only [GGHasLabel, LargeEvenRawDatum, LargeEvenRecipeChevalley, pow_one] using h

theorem ggE6TwoLocalRankThree_holds :
    GGE6TwoLocalRankThree := by
  intro X _ _ hperf hlabel
  obtain ⟨K, hKfield, hKfin, hKcard, hQK⟩ := ltqLr_e6_recipe_data hlabel
  obtain ⟨eθ⟩ := hQK
  let eR : LargeEvenCenterQuot (LargeEvenChevH (LargeEvenCartanE 6) K false) ≃*
      ↥(adjointGroup (Tag.E6) K) := TableBExc.recipeEquiv Tag.E6 K
  let hZk : Subgroup.center ↥(adjointGroup (Tag.E6) K) = ⊥ :=
    CFSG.LieType.Chevalley.center_adjointGroup_eq_bot (τ := Tag.E6) (K := K)
  let eAdj : ↥(adjointGroup (Tag.E6) K) ≃* AdjointQuotient Tag.E6 K :=
    ((QuotientGroup.quotientMulEquivOfEq hZk).trans QuotientGroup.quotientBot).symm
  let eC : (X ⧸ Subgroup.center X) ≃* AdjointQuotient Tag.E6 K :=
    eθ.trans (eR.trans eAdj)
  have hL : CFSG.Blueprint.LieModel (X ⧸ Subgroup.center X) CFSG.Open.StatedLieTag.E6 0 2 1 := by
    refine Or.inr (Or.inl ⟨rfl, by decide, ?_⟩)
    refine ⟨⟨Nat.prime_two, le_refl 1, rfl⟩, ?_⟩
    exact ⟨K, hKfield, hKfin, by rw [pow_one]; exact hKcard, ⟨eC⟩⟩
  have hZ : Subgroup.center X = ⊥ := ggSixE6A24_center_eq_bot X hperf hL
  let q : TauCeti.PrimePower := ⟨2, 1, Nat.prime_two, by norm_num⟩
  have hqcard : q.card = 2 := by simp [q, TauCeti.PrimePower.card_def]
  have hq2 : q.p = 2 := rfl
  have hv : (TauCeti.LieTypeIndex.E6 q).Valid := by simp
  have hKq : Nat.card K = q.card := by rw [hKcard, hqcard]
  obtain ⟨eB⟩ := CFSG.TauCetiBridge.Even.untwistedBridgeEven_E6 q hv hq2 K hKq
  let eXY : X ≃* (TauCeti.CFSGIndex.lie ⟨TauCeti.LieTypeIndex.E6 q, hv⟩).Group :=
    ((CFSG.LocalAnalysis.GLTheoremA.CanonInn.quotCenterEquivOfBot hZ).symm.trans eC).trans eB
  haveI : Finite (TauCeti.CFSGIndex.lie ⟨TauCeti.LieTypeIndex.E6 q, hv⟩).Group :=
    Finite.of_equiv _ eXY.toEquiv
  have hkY : 4 ≤ CFSG.Open.twoLocalPrimeRank 3
      (TauCeti.CFSGIndex.lie ⟨TauCeti.LieTypeIndex.E6 q, hv⟩).Group :=
    CFSG.RankThree.PartTwo.Census.Exceptional.four_le_localRank_three_E6_two q hv hqcard
  have hcongr : CFSG.Open.GLATwoLocalRank 3 X =
      CFSG.Open.GLATwoLocalRank 3
        (TauCeti.CFSGIndex.lie ⟨TauCeti.LieTypeIndex.E6 q, hv⟩).Group :=
    (CFSG.HardMathSupport.Timmesfeld.Tables.Census.glaTwoLocalRank_congr (p := 3)
      (by norm_num) eXY).symm
  show 4 ≤ CFSG.Open.GLATwoLocalRank 3 X
  rw [hcongr]
  exact hkY

end CFSG.StandardType

end

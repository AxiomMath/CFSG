module

public import CFSG.LocalAnalysis.StandardType.GGTwE6ToralNonsplit
public import CFSG.LocalAnalysis.StandardType.GGSixLayerCXNonsplitTwE6Label
public import CFSG.LocalAnalysis.StandardType.GGLayerAbelianInd
public import CFSG.LocalAnalysis.StandardType.GGLayerSubCoreFamily
public import CFSG.Adapters.TauCetiExceptional.EvenAll
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.Basic
public import CFSG.HardMathSupport.Meierfrankenfeld.LieOdd.ExcOrderTwisted

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg.Exceptional CFSG.SeitzReduction CFSG.Yardstones.Md0ec50421ce4
  CFSG.LocalAnalysis.GLTheoremA

section Input


@[expose] def GGTwE6LayerCentInvolTrivial : Prop :=
  ∀ f : ℕ, 1 ≤ f → ∀ p : ℕ, p.Prime → p ≠ 2 →
    ∀ A : Subgroup (MulAut ↥(graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * f))
      (frobQ 2 f))), IsPGroup p A → (∀ a ∈ A, ∀ b ∈ A, a * b = b * a) →
      A ≤ LayerSixE.twInndiagAut f → ¬ GGTwE6InndiagHighNonsplit f A →
        ¬ GGTwE6InndiagHighSplit f A →
          ∀ z ∈ CFSG.Open.GLALayer (LayerSixE.autFix A),
            (∀ y ∈ CFSG.Open.GLALayer (LayerSixE.autFix A), z * y = y * z) → z ^ 2 = 1 → z = 1

end Input

section Reduction


namespace TwE6LayerRest

theorem isChevSimple_graphFixedRootGroup (f : ℕ) (hf : 1 ≤ f) :
    IsChevSimple 2 ↥(graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * f)) (frobQ 2 f)) := by
  have hZ : Subgroup.center ↥(graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * f))
      (frobQ 2 f)) = ⊥ :=
    CFSG.HardMathSupport.Meierfrankenfeld.LieOdd.center_graphFixedRootGroup_E6_eq_bot (frobQ 2 f)
  obtain ⟨eD⟩ := TwE6Nonsplit.nonempty_quotient_center_equiv_derivedCentralQuotient_ad f hf
  let q : TauCeti.PrimePower := ⟨2, f, Nat.prime_two, hf⟩
  have hv : (TauCeti.LieTypeIndex.twistedE6 q).Valid := TauCeti.LieTypeIndex.valid_twistedE6 _
  have hK : Nat.card (GaloisField 2 (2 * f)) = q.card ^ TwistTag.E6.order := by
    rw [TwE6Toral.card_galoisField_two_mul f hf, TauCeti.PrimePower.card_def]
    rfl
  obtain ⟨eB⟩ := CFSG.TauCetiBridge.Even.chevalleyBridgesAll.twistedE6 q hv
    (GaloisField 2 (2 * f)) hK (frobQ 2 f) (fun x => by
      rw [TauCeti.PrimePower.card_def]
      exact frobQ_apply 2 f x)
  exact CFSG.HardMathSupport.Solomon.Coordinator.LieComp.isChevSimple_of_lie ⟨_, hv⟩
    (TauCeti.LieTypeIndex.characteristic_twistedE6 q)
    (((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).symm.trans
      (eD.trans eB))

end TwE6LayerRest

theorem ggTwE6InndiagCoreRestTwoInput_of_layerCentre (hZ : GGTwE6LayerCentInvolTrivial) :
    GGTwE6InndiagCoreRestTwoInput := by
  intro f hf p hp hp2 A hA hAc hAD hn hs
  haveI : Finite ↥(graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * f)) (frobQ 2 f)) :=
    Subtype.finite
  have hq := TwE6Nonsplit.isQuasisimple_graphFixedRootGroup f hf
  have hZ0 : Subgroup.center ↥(graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * f))
      (frobQ 2 f)) = ⊥ :=
    CFSG.HardMathSupport.Meierfrankenfeld.LieOdd.center_graphFixedRootGroup_E6_eq_bot (frobQ 2 f)
  let eZ : ↥(graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * f)) (frobQ 2 f)) ≃*
      (↥(graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * f)) (frobQ 2 f)) ⧸
        Subgroup.center ↥(graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * f))
          (frobQ 2 f))) :=
    ((QuotientGroup.quotientMulEquivOfEq hZ0).trans QuotientGroup.quotientBot).symm
  haveI := hq.2.1
  haveI hS : IsSimpleGroup ↥(graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * f))
      (frobQ 2 f)) := eZ.isSimpleGroup
  have hnc : ∃ a b : ↥(graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * f)) (frobQ 2 f)),
      a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := hq.2.2
    obtain ⟨a', rfl⟩ := QuotientGroup.mk_surjective a
    obtain ⟨b', rfl⟩ := QuotientGroup.mk_surjective b
    exact ⟨a', b', fun h => hab (by rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, h])⟩
  have hEq : LayerSixE.autFix A = I142.centFix A :=
    Subgroup.ext fun x => LayerSixE.mem_autFix.trans I142.mem_centFix.symm
  have hperf : ∀ P : Subgroup ↥(graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * f))
      (frobQ 2 f)), P ≤ LayerSixE.autFix A → ⁅P, P⁆ = P →
        P ≤ CFSG.Open.GLALayer (LayerSixE.autFix A) := by
    intro P hP hPp
    rw [hEq] at hP ⊢
    exact LayerAbelian.lieSemisimpleCentAbelian _ hS hnc
      (TwE6LayerRest.isChevSimple_graphFixedRootGroup f hf) p hp hp2 A hA hAc P hP hPp
  exact LayerCores.exists_subCoreFamily_of_layer (LayerSixE.autFix A) hperf
    (hZ f hf p hp hp2 A hA hAc hAD hn hs)

theorem ggTwE6InndiagCoreRestInput_of_layerCentre (hZ : GGTwE6LayerCentInvolTrivial) :
    GGTwE6InndiagCoreRestInput :=
  ggTwE6InndiagCoreRestInput_of_two (ggTwE6InndiagCoreRestTwoInput_of_layerCentre hZ)

end Reduction

end CFSG.StandardType

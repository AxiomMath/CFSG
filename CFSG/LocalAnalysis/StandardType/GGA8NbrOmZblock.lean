module

public import CFSG.LocalAnalysis.StandardType.GGA8NbrOmDefs
public import CFSG.LocalAnalysis.StandardType.GGA8NbrSpJSp4
public import CFSG.LocalAnalysis.StandardType.GGSixSeventeenWitOmBlock
public import CFSG.LocalAnalysis.StandardType.GGTableBOrthRestOddLayer
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotMainGraphOmegaMinusPiecesOrders
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotQ2OverlapOmMinus
public import CFSG.RankThree.PartOne.S11d.OrthModels
public import CFSG.LocalAnalysis.AGLEmbedding.TimmesfeldRouteAux
public import CFSG.ClassicalInvolution.ModelFacts.PairFrameExcLevi
public import CFSG.LocalAnalysis.ComponentClassification.ExcSelectorEvenTriality
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X7bPairs
public import CFSG.LocalAnalysis.SeitzReduction.E6PilotCTFieldFamily
public import CFSG.LocalAnalysis.SeitzReduction.E6PilotFieldNormalizePSL
public import CFSG.LocalAnalysis.SeitzReduction.E6PilotLeviPerp
public import CFSG.LocalAnalysis.SeitzReduction.E7PilotFieldNormalizeAutMain
public import CFSG.LocalAnalysis.SeitzReduction.E8PilotQ2PositionWork
public import CFSG.LocalAnalysis.SeitzReduction.E8PilotSwapLift
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotCTGraphRange
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotGraphParamFinal
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotGraphParamSpinCover
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotGraphRowRange
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotMainGraphOmegaPlusIota
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2RowNeighbour
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2SmallJ
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotBLiftAniso
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotCatCovers
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotHR7iii
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotWeakCT
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotHR14ModelUnitary
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotHR14OmegaOuterMinus
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotHR14PartnerCoset
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotHR14PartnerSp
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotHR14Transfer
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotKindCTUAlignMain
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotOmegaRowUniqueStep
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2RowOmega
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2RowOmegaClass
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2RowOmegaUnitaryRows
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2UnitaryCTQuotRows
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2UnitaryCTRows
public import CFSG.LocalAnalysis.SeitzReduction.UnitaryPilotUniqueTypeGraph
public import CFSG.RankThree.PartOne.S11d.LieGoodConclusion
public import CFSG.RankThree.PartOne.S11d.OutClassicalTwo
public import CFSG.RankThree.PartOne.S11d.OutLinear
public import CFSG.RankThree.PartOne.S11d.OutSymplectic
public import CFSG.RankThree.PartOne.S11d.OutUnitary

public section

namespace CFSG.StandardType

open Polynomial Module Multiplicative CFSG.Assembly CFSG.RankThree.PartOne.KCPrimary
  CFSG.RankThree.PartOne.KCOrthogonal
open CFSG.Open (StatedClassicalModel)
open CFSG.RankThree.Classical2 (orthDerived)

namespace A8Coord

theorem omZblock_thirteen_dvd {A : Subgroup (OmV ≃ₗ[GaloisField 2 3] OmV)} (hAΩ : A ≤ omΩ)
    (F : SevOm.Frame omQ 7 A 3) (hdim : ∀ i, finrank (GaloisField 2 3) (F.U i) = 2)
    {β : Fin 3 → ZMod 7} {j : Fin 3} (hβj : β j ≠ 0) (hβ0 : ∀ i, i ≠ j → β i = 0)
    {J : Subgroup (OmV ≃ₗ[GaloisField 2 3] OmV)}
    (hJ : IsComponentOf J (omΩ ⊓ Subgroup.centralizer {F.ι (ofAdd β)}))
    (hfix : finrank (GaloisField 2 3) (fixedSpace (F.ι (ofAdd β))) = 6)
    (hJB : J ≤ supportedBlock omQ (F.ι (ofAdd β)) (X - 1))
    (hall : ∀ u ∈ supportedBlock omQ (F.ι (ofAdd β)) (X - 1), u ^ 7 = 1 → u ∈ J) :
    13 ∣ Nat.card J ∧ Subgroup.center J = ⊥ := by
  let a : OmV ≃ₗ[GaloisField 2 3] OmV := F.ι (ofAdd β)
  let W : Submodule (GaloisField 2 3) OmV := fixedSpace a
  let R : QuadraticForm (GaloisField 2 3) W := omQ.comp W.subtype
  haveI : Finite (OmV ≃ₗ[GaloisField 2 3] OmV) :=
    Finite.of_injective (fun e : OmV ≃ₗ[GaloisField 2 3] OmV => (e : OmV → OmV))
      fun e₁ e₂ h => LinearEquiv.ext (congrFun h)
  have hK8 : Nat.card (GaloisField 2 3) = 8 := by
    rw [GaloisField.card 2 3 (by norm_num)]; norm_num
  have hQnd : (QuadraticMap.polarBilin omQ).Nondegenerate :=
    CFSG.ComponentClassification.CatalogueBOrthogonalPointIsometry.polar_nondegenerate_isometry
      (CFSG.ComponentClassification.CatalogueBOrthogonalPointData.coordinateMinusIsometry 4
        (GaloisField 2 3) (by norm_num)
        (CFSG.LieType.Universal.minusCoeffs 2 3).1 (CFSG.LieType.Universal.minusCoeffs 2 3).2)
      (CFSG.LieType.Universal.Spin.nondegenerate_polarBilin_quadMinus_of_finite
        (K := GaloisField 2 3) (n := 4) (CFSG.LieType.Universal.minusCoeffs_irr 2 3))
  have hx : OddOrderIsometry omQ 7 a :=
    F.oddOrderIsometry hQnd (by norm_num) (by norm_num) hAΩ (ofAdd β)
  have hRnd : (QuadraticMap.polarBilin R).Nondegenerate := hx.polarBilin_fixed_nondegenerate
  have hW6 : finrank (GaloisField 2 3) W = 6 := hfix
  have h6 : 6 ≤ finrank (GaloisField 2 3) W := by omega
  have hns : ¬ (finrank (GaloisField 2 3) W = 4 ∧
      ∃ S : Submodule (GaloisField 2 3) W, finrank (GaloisField 2 3) S = 2 ∧
        ∀ x ∈ S, R x = 0) := by
    rintro ⟨h4, -⟩
    omega
  have hSFDq : CFSG.IsQuasisimple ↥(supportedFixedDerived omQ a) :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv (supportedFixedDerivedEquiv hx).symm
      (LayerPDiv.isQuasisimple_commutator_of_not_split hRnd (by omega) hns).1
  have hJperf : CFSG.IsQuasisimple J :=
    (CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native J).1 hJ.2.2
  have hJJ : ⁅J, J⁆ = J := LayerFacts.ggCommutator_eq_of_isQuasisimple hJperf
  have hJSFD : J ≤ supportedFixedDerived omQ a := by
    rw [hx.supportedFixedDerived_eq, ← hJJ]
    exact Subgroup.commutator_mono hJB hJB
  have hSFle : supportedFixedDerived omQ a ≤ omΩ ⊓ Subgroup.centralizer {a} :=
    le_inf hx.supportedFixedDerived_le_orthDerived
      (supportedFixedDerived_le_isometryCentralizer.trans inf_le_right)
  have hSFcomp : CFSG.Assembly.IsComponentOf (supportedFixedDerived omQ a)
      (omΩ ⊓ Subgroup.centralizer {a}) :=
    ⟨hSFle, LayerCores.ggSubnormal_of_normal hSFle (fun u hu g hg =>
        hx.conj_mem_supportedFixedDerived
          (Subgroup.mem_inf.mpr
            ⟨orthDerived_le_orthogonalGroup (Subgroup.mem_inf.mp hu).1,
              (Subgroup.mem_inf.mp hu).2⟩) hg),
      (CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native _).mpr hSFDq⟩
  have hJne : J ≠ ⊥ := by
    rintro hbot
    obtain ⟨p, q, hpq⟩ := hJperf.2.2
    haveI : Subsingleton ↥J := by rw [hbot]; infer_instance
    exact hpq (Subsingleton.elim (p * q) (q * p))
  have hJeq : J = supportedFixedDerived omQ a := by
    rcases CFSG.LocalAnalysis.ComponentInitial.isComponentOf_eq_or_commute hJ hSFcomp with
      heq | hcomm
    · exact heq
    · exfalso
      have hle : J ≤ ⊥ := by
        have h1 : ⁅J, J⁆ ≤ ⁅J, supportedFixedDerived omQ a⁆ :=
          Subgroup.commutator_mono le_rfl hJSFD
        rw [hcomm] at h1
        rw [hJJ] at h1
        exact h1
      exact hJne (le_bot_iff.mp hle)
  have hcardJ : Nat.card J = Nat.card (orthDerived R) := by
    rw [hJeq]
    exact Nat.card_congr (supportedFixedDerivedEquiv hx).toEquiv
  have hcenterJ : Subgroup.center J = ⊥ := by
    rw [hJeq]
    exact CFSG.AGLEmbedding.center_eq_bot_of_mulEquiv (supportedFixedDerivedEquiv hx)
      (CFSG.StandardType.OrthRestOdd.orthDerived_facts R hRnd h6).2.1
  have h13R : 13 ∣ Nat.card (orthDerived R) := by
    rcases CFSG.GroupTheory.WeirSylow.exists_isometry_quadPlus_or_quadMinus (n := 3) R hRnd
      (by norm_num) (by rw [hW6]) with he | ⟨b, c, hirr, he⟩
    · obtain ⟨e⟩ := he
      rw [Nat.card_congr (CFSG.RankThree.PartOne.orthDerivedEquiv e).toEquiv]
      rw [show Nat.card (orthDerived (CFSG.LieType.Universal.Spin.quadPlus 3 (GaloisField 2 3))) =
          Nat.card (CFSG.Open.StatedOmega (CFSG.Open.StatedQuadPlus 3 (GaloisField 2 3))) by
        rw [CFSG.SeitzReduction.F4Pilot.statedOmega_quadPlus_three_eq_map,
          Subgroup.card_map_of_injective (MulEquiv.injective _)]]
      rw [CFSG.SeitzReduction.F4Pilot.natCard_statedOmega_quadPlus_three_any,
        CFSG.SeitzReduction.F4Pilot.ordSL_four, hK8]
      norm_num
    · obtain ⟨e⟩ := he
      rw [Nat.card_congr (CFSG.RankThree.PartOne.orthDerivedEquiv e).toEquiv]
      rw [show Nat.card
            (orthDerived (CFSG.LieType.Universal.Spin.quadMinus 3 (GaloisField 2 3) b c)) =
          Nat.card (CFSG.Open.StatedOmega (CFSG.Open.StatedQuadMinus 3 (GaloisField 2 3) b c)) by
        rw [CFSG.SeitzReduction.F4Pilot.statedOmega_quadMinus_eq_map,
          Subgroup.card_map_of_injective (MulEquiv.injective _)]]
      rw [CFSG.SeitzReduction.F4Pilot.natCard_statedOmega_quadMinus_three hirr,
        CFSG.SeitzReduction.F4Pilot.ordSU_four, hK8]
      norm_num
  exact ⟨hcardJ.symm ▸ h13R, hcenterJ⟩

theorem ggA8Nbr_omZblock_not_le_K {G : Type} [Group G] [Finite G] (φ : ↥omΩ →* G)
    (hinj : Function.Injective φ) {J : Subgroup (OmV ≃ₗ[GaloisField 2 3] OmV)} (hJΩ : J ≤ omΩ)
    (h13 : 13 ∣ Nat.card J) (hZ : Subgroup.center J = ⊥) {K : Subgroup G}
    (hKm : StatedClassicalModel (K ⧸ Subgroup.center K) .PSL 9 2 1)
    (hle : (J.comap omΩ.subtype).map φ ≤ K) : False := by
  let J' : Subgroup G := (J.comap omΩ.subtype).map φ
  have hJ'K : J' ≤ K := hle
  have hcard : Nat.card J' = Nat.card J := by
    show Nat.card ((J.comap omΩ.subtype).map φ) = Nat.card J
    rw [Subgroup.card_map_of_injective (f := φ) hinj]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hJΩ).toEquiv
  have h13' : 13 ∣ Nat.card J' := hcard ▸ h13
  have hZK : J' ⊓ (Subgroup.center K).map K.subtype = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    intro g hg
    obtain ⟨hgJ', hgZ⟩ := Subgroup.mem_inf.mp hg
    obtain ⟨y, hy, hyval⟩ := Subgroup.mem_map.mp hgJ'
    obtain ⟨k, hkcenter, hkval⟩ := Subgroup.mem_map.mp hgZ
    have hyJ : omΩ.subtype y ∈ J := hy
    have hcenter_y : (⟨omΩ.subtype y, hyJ⟩ : J) ∈ Subgroup.center J := by
      rw [Subgroup.mem_center_iff]
      intro x
      apply Subtype.ext
      let x' : ↥omΩ := ⟨(x : OmV ≃ₗ[GaloisField 2 3] OmV), hJΩ x.2⟩
      have hx'mem : x' ∈ J.comap omΩ.subtype := by
        rw [Subgroup.mem_comap]
        simpa [x'] using x.2
      have hmem : φ x' ∈ K :=
        hJ'K (Subgroup.mem_map.mpr ⟨x', hx'mem, rfl⟩)
      have hc := Subgroup.mem_center_iff.mp hkcenter ⟨φ x', hmem⟩
      have hc' := congrArg (fun t : ↥K => (t : G)) hc
      simp only [Subgroup.coe_mul] at hc'
      have hcomm : φ x' * φ y = φ y * φ x' := by
        rw [hyval, ← hkval]
        exact hc'
      have hmul : x' * y = y * x' :=
        hinj (by rw [map_mul, map_mul]; exact hcomm)
      have h := congrArg (fun t : ↥omΩ => (t : OmV ≃ₗ[GaloisField 2 3] OmV)) hmul
      simpa [x', Subgroup.coe_mul] using h
    have hy1 : omΩ.subtype y = 1 := by
      have h1 : (⟨omΩ.subtype y, hyJ⟩ : J) = 1 := by
        have hmem : (⟨omΩ.subtype y, hyJ⟩ : J) ∈ (⊥ : Subgroup J) := by
          rw [← hZ]; exact hcenter_y
        exact Subgroup.mem_bot.mp hmem
      simpa using congrArg (fun t : J => (t : OmV ≃ₗ[GaloisField 2 3] OmV)) h1
    have hy1' : y = 1 := Subtype.ext (by simpa using hy1)
    calc g = φ y := hyval.symm
      _ = φ 1 := by rw [hy1']
      _ = 1 := map_one φ
  have hdvd : Nat.card J' ∣ Nat.card (K ⧸ Subgroup.center K) :=
    a8j4_card_dvd_quotient_center hJ'K hZK
  exact a8j4_not_thirteen_dvd_centerQuotient hKm (h13'.trans hdvd)

end A8Coord

end CFSG.StandardType

end

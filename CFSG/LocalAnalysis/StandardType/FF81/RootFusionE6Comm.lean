module

public import Certificates.Certificate3951
public import CFSG.LocalAnalysis.SeitzReduction.EPilotFusionEntrywise
public import CFSG.LocalAnalysis.SeitzReduction.LongRootPairsRoots
import CFSG.LocalAnalysis.SeitzReduction.LongRootPairs
import CFSG.LocalAnalysis.SeitzReduction.E6PilotClassesRoots
import CFSG.LocalAnalysis.SeitzReduction.E6PilotClassesLevi
import CFSG.LocalAnalysis.SeitzReduction.EPilotRootSL2Basic
public import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
public import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.theorem_3_3
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section3.Basic
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter2.Basic
public import CFSG.Walter.JRFacts
import CFSG.Assembly.OrderReductions.InvertedSubgroup
import CFSG.Assembly.OrderReductions.OddInversion
import CFSG.CharacterTheory.Semidihedral.OddFieldLift
import CFSG.GroupTheory.LocalCores.Fitting
import CFSG.LieType.Chevalley.C2E6StandardFixedData
import CFSG.LieType.Chevalley.C2E6UnitaryFourImages
import CFSG.LieType.Chevalley.E6SecondGraphFullCentralizer
import CFSG.LieType.Chevalley.SimplyLacedFieldTwoCover
import CFSG.LinearAlgebra.LinearGroups.CoordinateData
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBGraphFieldArithmetic
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBGraphFieldUnitaryData
import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogG2EvenCanonicalField
import CFSG.LocalAnalysis.ComponentInitial.LinearCoverFour
import CFSG.LocalAnalysis.ComponentInitial.LinearInvolutionFixedField
import CFSG.LocalAnalysis.ComponentInitial.SylowPointRecovery

public section

namespace CFSG.StandardType.FF81

open CFSG.Blueprint.Chevalley CFSG.SeitzReduction

theorem exists_commute_conj_of_conj_eq_pinnedElt
    {G : Type} [Group G] [Finite G] {Y : Subgroup G} {K : Type} [Field K] [Finite K] [CharP K 2]
    (φ : ↥Y ≃* adjointGroup .E6 K) {t : G} (htY : t ∈ Y) (ht : orderOf t = 2)
    {c : adjointGroup .E6 K}
    (hc : c * φ ⟨t, htY⟩ * c⁻¹ = EPilot.pinnedElt .E6 (highRoot .E6) (1 : K))
    {b : G} (hbY : b ∈ Y) (hb : orderOf b = 3) (hinv : t * b * t⁻¹ = b⁻¹)
    {x : G} (hxY : x ∈ Y) (hx : orderOf x = 2) :
    ∃ y ∈ Y, Commute x (y * b * y⁻¹) := by
  let H := adjointGroup .E6 K
  let T : H := φ ⟨t, htY⟩
  let B : H := φ ⟨b, hbY⟩
  let X : H := φ ⟨x, hxY⟩
  have hT2 : orderOf T = 2 := by
    have hY2 : orderOf (⟨t, htY⟩ : Y) = 2 := by
      rw [← Subgroup.orderOf_coe (⟨t, htY⟩ : Y)]
      simpa using ht
    exact (φ.orderOf_eq ⟨t, htY⟩).trans hY2
  have hB3 : orderOf B = 3 := by
    have hY3 : orderOf (⟨b, hbY⟩ : Y) = 3 := by
      rw [← Subgroup.orderOf_coe (⟨b, hbY⟩ : Y)]
      simpa using hb
    exact (φ.orderOf_eq ⟨b, hbY⟩).trans hY3
  have hX2 : orderOf X = 2 := by
    have hY2 : orderOf (⟨x, hxY⟩ : Y) = 2 := by
      rw [← Subgroup.orderOf_coe (⟨x, hxY⟩ : Y)]
      simpa using hx
    exact (φ.orderOf_eq ⟨x, hxY⟩).trans hY2
  have hTBT : T * B * T⁻¹ = B⁻¹ := by
    have h : (⟨t, htY⟩ : Y) * ⟨b, hbY⟩ * ⟨t, htY⟩⁻¹ = ⟨b, hbY⟩⁻¹ :=
      Subtype.ext (by simpa using hinv)
    have h' := congrArg φ h
    simpa only [map_mul, map_inv] using h'
  have hT2' : T * T = 1 := by
    have h := pow_orderOf_eq_one T
    rw [hT2] at h
    simpa [pow_two] using h
  have hB3' : B * B * B = 1 := by
    have h := pow_orderOf_eq_one B
    rw [hB3] at h
    rwa [pow_three'] at h
  have hBinv : B⁻¹ = B * B := by
    exact (eq_inv_of_mul_eq_one_right (by rw [← mul_assoc]; exact hB3')).symm
  have hBinv2 : B⁻¹ * B⁻¹ = B := by
    rw [hBinv]
    calc B * B * (B * B) = (B * B * B) * B := by group
      _ = 1 * B := by rw [hB3']
      _ = B := by group
  have hcMod :
      ((c : H) : ModGL .E6 K) * (T : ModGL .E6 K) * (((c : H) : ModGL .E6 K))⁻¹ =
        pinnedX .E6 K (highRoot .E6) 1 := by
    have h := congrArg (Subtype.val) hc
    simpa [T, EPilot.pinnedElt] using h
  let Ash : ModGL .E6 K := ((c⁻¹ : H) : ModGL .E6 K)
  let Bc : ModGL .E6 K := ((B * c⁻¹ : H) : ModGL .E6 K)
  let U : Subgroup (ModGL .E6 K) := rootSubgroup .E6 K (highRoot .E6)
  let J : Subgroup (ModGL .E6 K) :=
    U.map (MulAut.conj Ash).toMonoidHom ⊔ U.map (MulAut.conj Bc).toMonoidHom
  have hP_mem : pinnedX .E6 K (highRoot .E6) 1 ∈ U :=
    Subgroup.subset_closure ⟨1, rfl⟩
  have hT_eq : (T : ModGL .E6 K) =
      (MulAut.conj Ash) (pinnedX .E6 K (highRoot .E6) 1) := by
    rw [MulAut.conj_apply]
    calc (T : ModGL .E6 K)
        = ((c : H) : ModGL .E6 K)⁻¹ * (((c : H) : ModGL .E6 K) * (T : ModGL .E6 K) *
            (((c : H) : ModGL .E6 K))⁻¹) * ((c : H) : ModGL .E6 K) := by group
      _ = ((c : H) : ModGL .E6 K)⁻¹ * pinnedX .E6 K (highRoot .E6) 1 *
            ((c : H) : ModGL .E6 K) := by rw [hcMod]
      _ = Ash * pinnedX .E6 K (highRoot .E6) 1 * Ash⁻¹ := by
            simp only [Ash, Subgroup.coe_inv, inv_inv]
  have hT_mem : (T : ModGL .E6 K) ∈ J := by
    rw [hT_eq]
    exact Subgroup.mem_sup_left
      (Subgroup.mem_map_of_mem (MulAut.conj Ash).toMonoidHom hP_mem)
  have hBTB_eq : (B : ModGL .E6 K) * (T : ModGL .E6 K) * ((B : ModGL .E6 K))⁻¹ =
      (MulAut.conj Bc) (pinnedX .E6 K (highRoot .E6) 1) := by
    rw [hT_eq]
    simp only [MulAut.conj_apply, Ash, Bc, Subgroup.coe_mul, Subgroup.coe_inv]
    group
  have hBTB_mem : (B : ModGL .E6 K) * (T : ModGL .E6 K) * ((B : ModGL .E6 K))⁻¹ ∈ J := by
    rw [hBTB_eq]
    exact Subgroup.mem_sup_right
      (Subgroup.mem_map_of_mem (MulAut.conj Bc).toMonoidHom hP_mem)
  have hTBTm : (T : ModGL .E6 K) * (B : ModGL .E6 K) * ((T : ModGL .E6 K))⁻¹ =
      ((B : ModGL .E6 K))⁻¹ := by
    simpa using congrArg (fun z : H => (z : ModGL .E6 K)) hTBT
  have hT2m : (T : ModGL .E6 K) * (T : ModGL .E6 K) = 1 := by
    simpa using congrArg (fun z : H => (z : ModGL .E6 K)) hT2'
  have hBinv2m : ((B : ModGL .E6 K))⁻¹ * ((B : ModGL .E6 K))⁻¹ = (B : ModGL .E6 K) := by
    simpa using congrArg (fun z : H => (z : ModGL .E6 K)) hBinv2
  have hB_eq : (B : ModGL .E6 K) =
      (T : ModGL .E6 K) * ((B : ModGL .E6 K) * (T : ModGL .E6 K) *
        ((B : ModGL .E6 K))⁻¹) := by
    rw [show (T : ModGL .E6 K) * ((B : ModGL .E6 K) * (T : ModGL .E6 K) *
          ((B : ModGL .E6 K))⁻¹) =
        ((T : ModGL .E6 K) * (B : ModGL .E6 K) * ((T : ModGL .E6 K))⁻¹) *
          ((T : ModGL .E6 K) * (T : ModGL .E6 K)) * ((B : ModGL .E6 K))⁻¹ by group,
      hTBTm, hT2m, mul_one, hBinv2m]
  have hB_mem : (B : ModGL .E6 K) ∈ J := by
    rw [hB_eq]
    exact J.mul_mem hT_mem hBTB_mem
  have hxAS : Ash ∈ adjointGroup .E6 K := (c⁻¹).2
  have hyAS : Bc ∈ adjointGroup .E6 K := (B * c⁻¹).2
  have hAS := isPGroup_or_eq_conj_of_conj_highRoot (τ := .E6) (K := K) (p := 2)
    (x := Ash) (y := Bc) hxAS hyAS
  have hnotP : ¬ IsPGroup 2 ↥J := by
    intro hP
    have hBm3 : orderOf (B : ModGL .E6 K) = 3 := by
      have h := orderOf_injective (Subgroup.subtype H) (Subgroup.subtype_injective H) B
      rw [hB3] at h
      exact h
    obtain ⟨k, hk⟩ := hP.exists_orderOf_dvd_pow (⟨(B : ModGL .E6 K), hB_mem⟩ : ↥J)
    rw [Subgroup.orderOf_mk, hBm3] at hk
    have h32 : 3 ∣ 2 := (by norm_num : Nat.Prime 3).dvd_of_dvd_pow hk
    norm_num at h32
  rcases hAS with hP | ⟨c', hc', hjoin⟩
  · exact absurd hP hnotP
  · have hB_img : (B : ModGL .E6 K) ∈
        (EPilot.highRootSL2 .E6 K).map (MulAut.conj c').toMonoidHom := by
      change (B : ModGL .E6 K) ∈
        (rootSubgroup .E6 K (highRoot .E6) ⊔ rootSubgroup .E6 K (-highRoot .E6)).map
          (MulAut.conj c').toMonoidHom
      rw [← hjoin]
      exact hB_mem
    obtain ⟨a, ha, haB⟩ := Subgroup.mem_map.1 hB_img
    have haB' : (c' : ModGL .E6 K) * a * (c' : ModGL .E6 K)⁻¹ = (B : ModGL .E6 K) := by
      simpa [MulAut.conj_apply] using haB
    let aH : H := ⟨a, EPilot.highRootSL2_le_adjointGroup ha⟩
    let cH : H := ⟨c', hc'⟩
    obtain ⟨κ, e, he, -, -⟩ :=
      E6Pilot.exists_conj_eq_e6Rep_mem_a5Levi (K := K) (y := X) hX2
    have hcomm_ea : Commute (E6Pilot.e6Rep K κ : ModGL .E6 K) a := by
      have h := (Subgroup.mem_centralizer_iff.1
        (E6Pilot.coe_e6Rep_mem_centralizer_highRootSL2 (K := K) κ)) a ha
      exact h.symm
    have hcomm_H : Commute (E6Pilot.e6Rep K κ : H) aH := by
      apply Commute.of_map (f := Subgroup.subtype H) (Subgroup.subtype_injective H)
      simpa [aH] using hcomm_ea
    have hX_eq : X = (e : H)⁻¹ * E6Pilot.e6Rep K κ * e := by
      calc X = (e : H)⁻¹ * (e * X * e⁻¹) * e := by group
        _ = (e : H)⁻¹ * E6Pilot.e6Rep K κ * e := by rw [he]
    have hcomm_Ha : Commute X ((e : H)⁻¹ * aH * e) := by
      rw [hX_eq]
      have h := hcomm_H.map (MulAut.conj (e : H)⁻¹)
      simpa only [MulAut.conj_apply, inv_inv] using h
    have haH_eq : aH = cH⁻¹ * B * cH := by
      apply Subtype.ext
      simp only [aH, cH, Subgroup.coe_mul, Subgroup.coe_inv]
      rw [← haB']
      group
    let wH : H := (e : H)⁻¹ * cH⁻¹
    have hcomm_wH : Commute X (wH * B * wH⁻¹) := by
      rw [haH_eq] at hcomm_Ha
      have harg : (e : H)⁻¹ * (cH⁻¹ * B * cH) * e = wH * B * wH⁻¹ := by
        simp only [wH]
        group
      rwa [harg] at hcomm_Ha
    let y : Y := φ.symm wH
    refine ⟨(y : G), y.2, ?_⟩
    have hXsymm : φ.symm X = ⟨x, hxY⟩ := by simp [X]
    have hBsymm : φ.symm (wH * B * wH⁻¹) = y * ⟨b, hbY⟩ * y⁻¹ := by
      simp [y, B, map_mul, map_inv]
    have hcommY : Commute (φ.symm X) (φ.symm (wH * B * wH⁻¹)) := hcomm_wH.map φ.symm
    have hcommG := hcommY.map (Subgroup.subtype Y)
    simpa [hXsymm, hBsymm] using hcommG

end CFSG.StandardType.FF81

module

public import CFSG.Timmesfeld.Transvection.OddBC2RelStatement
public import CFSG.Timmesfeld.Transvection.OddUnitary
public import Certificates.Certificate43
public import Certificates.Certificate82
public import Certificates.Certificate83
public import Certificates.Certificate84
public import Certificates.Certificate85
public import Certificates.Certificate86
public import Certificates.Certificate87
public import Certificates.Certificate88
public import Certificates.Certificate89
public import Certificates.Certificate90
public import Certificates.Certificate91
public import Certificates.Certificate92
public import Certificates.Certificate93
public import Certificates.Certificate94
public import Certificates.Certificate95
public import Certificates.Certificate96
public import Certificates.Certificate97
public import Certificates.Certificate98
public import Certificates.Certificate99
public import Certificates.Certificate100
public import Certificates.Certificate101
public import Certificates.Certificate102
public import Certificates.Certificate103
public import Certificates.Certificate104
public import Certificates.Certificate105
public import Certificates.Certificate106
public import Certificates.Certificate107
public import Certificates.Certificate108
public import Certificates.Certificate109
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate117

import CFSG.Timmesfeld.Transvection.OddBC2Pos
import CFSG.Timmesfeld.Transvection.OddLiftFrobenius
import CFSG.Timmesfeld.Transvection.OddPairsFrame
import CFSG.Timmesfeld.Transvection.OddUnitaryMain
public import CFSG.Fischer.Assembly
public import CFSG.Fischer.Classification.Milestone
public import CFSG.Fischer.NoF25.Local
public import CFSG.LocalAnalysis.LargeEvenClassification.C8FourSubgroupExhaustion
public import CFSG.LocalAnalysis.LargeEvenClassification.C8FourSubgroupRanks
public import CFSG.LocalAnalysis.LargeEvenClassification.CyclicCongruenceCut
public import CFSG.LocalAnalysis.LargeEvenClassification.CyclicFourLarge
public import CFSG.LocalAnalysis.LargeEvenClassification.CyclicTwoFourGenerators
public import CFSG.LocalAnalysis.LargeEvenClassification.MacWilliamsReduction
public import CFSG.LocalAnalysis.LargeEvenClassification.SmallCfourFullObstruction
public import CFSG.LocalAnalysis.LargeEvenClassification.SmallCfourProperSubgroups
public import CFSG.Sporadic.FischerOddCore.Fi24AlmostSimple
public import CFSG.Sporadic.FischerOddCore.Fi24R2CompBase
public import CFSG.Sporadic.FischerOddCore.FischerOuterBasic
public import CFSG.Sporadic.Schreier.MathieuOddCoreWords
public import CFSG.Sporadic.Th.Max3.Data
public import CFSG.Timmesfeld.ARS.CaseEFrame
public import CFSG.Timmesfeld.ARS.CaseMLevi
public import CFSG.Timmesfeld.ARS.Sec12Center
public import CFSG.Timmesfeld.ARS.Sec13Closed
public import CFSG.Timmesfeld.ARS.Sec13Maximal
public import CFSG.Timmesfeld.Special.TwoCore
public import CFSG.Timmesfeld.Transvection.OddBC2Statement
import CFSG.LinearAlgebra.LinearGroups.CoordinateData
import CFSG.LocalAnalysis.ProperTwoGeneratedCore.AschbacherCanonicalRemaining
import CFSG.LocalAnalysis.ProperTwoGeneratedCore.ExceptionalEightPlaneCentralizer
import CFSG.LocalAnalysis.ShultStronglyClosedTI.UnitaryRootAutomorphism
import CFSG.Permutation.BurnsideSchur
import CFSG.Timmesfeld.Moufang.Three
import CFSG.Timmesfeld.Transvection.OddResidueBlock

public section

namespace CFSG.Timmesfeld.Transvection

open CFSG.Timmesfeld.ARS CFSG.LieType CFSG.LieType.Universal CFSG.LieType.Universal.Unitary
  CFSG.LieType.BorelTits CFSG.Timmesfeld.Transvection.Pres
open CFSG.SeitzReduction.F4Pilot (suCongr)
open scoped commutatorElement

theorem oddFrameBC2Statement_of_heisRelations (hrel : OddFrameHeisRelations) :
    OddFrameBC2Statement := by
  intro H _ Δ h hML hq F _ _ _ n hFn hn hcard r hr hm P Q hF hns R hR htop htr θ₀ hθr₀
    hθk₀ hθo₀ hθc₀ hθmem₀ hd₀
  have hθ'r₀ := (IsMaxFrame.su3_residue_oddPrevLift hFn hr hm h.cls.root hF hns hR hθr₀
    hθc₀ hθmem₀).1
  rcases hrel H Δ h hML hq F n hFn hn hcard r hr hm P Q hF hns R hR htop htr θ₀ hθr₀ hθk₀
    hθo₀ hθc₀ hθmem₀ hd₀ with ⟨hss, hsm⟩ | ⟨hss, hsm⟩
  · refine ⟨θ₀, hθr₀, hθc₀, ?_⟩
    exact SURelations.HasFrameImages.extendsToHom_pairRoots_bc2_pos_toHom hFn hr hm h hML hq
      hF.toIsFrame hcard hR hd₀ hθr₀ hθ'r₀ hss hsm
  · let e : SU (unitaryInvolution F 2 n) 3 →* SU (unitaryInvolution F 2 n) 3 :=
      (suCongr (σ := unitaryInvolution F 2 n) (σ' := unitaryInvolution F 2 n)
        (unitaryInvolution F 2 n) (fun _ => rfl) 3).toMonoidHom
    have he : ∀ u v : F,
        e (suHeis (unitaryInvolution F 2 n) (unitaryInvolution_involutive hFn)
          (Nat.not_even_iff_odd.mpr (Exists.intro 1 rfl)) (Sum.inl (0 : Fin (3 / 2))) u v) =
        suHeis (unitaryInvolution F 2 n) (unitaryInvolution_involutive hFn)
          (Nat.not_even_iff_odd.mpr (Exists.intro 1 rfl)) (Sum.inl (0 : Fin (3 / 2)))
          (unitaryInvolution F 2 n u) (unitaryInvolution F 2 n v) := by
      intro u v
      exact suCongr_suHeis (unitaryInvolution_involutive hFn)
        (Nat.not_even_iff_odd.mpr (Exists.intro 1 rfl)) (unitaryInvolution F 2 n) (fun _ => rfl)
        (Sum.inl (0 : Fin (3 / 2))) u v
    have hesurj : Function.Surjective e :=
      (suCongr (σ := unitaryInvolution F 2 n) (σ' := unitaryInvolution F 2 n)
        (unitaryInvolution F 2 n) (fun _ => rfl) 3).surjective
    have hrange : (θ₀.comp e).range = residueGroup Δ P Q (cLastIdx r hr) := by
      rw [MonoidHom.range_comp, MonoidHom.range_eq_top_of_surjective e hesurj,
        Subgroup.map_top]
      exact hθr₀
    have hchord : (θ₀.comp e).comp (su3Chord (unitaryInvolution F 2 n)) =
        R.lastBlock hFn (even_two_mul r) hm := by
      rw [MonoidHom.comp_assoc,
        suCongr_comp_su3Chord hFn (unitaryInvolution F 2 n) (fun _ => rfl) (fun _ hc => hc),
        hθc₀]
    have hθ'r : (oddPrevLift hFn hr (R.toHom hFn (even_two_mul r) hm) (θ₀.comp e)).range =
        residueGroup Δ P Q (cPrevIdx r hr) := by
      rw [oddPrevLift_comp, MonoidHom.range_comp,
        MonoidHom.range_eq_top_of_surjective e hesurj, Subgroup.map_top]
      exact hθ'r₀
    have hd : OddFrameCompatible hFn hr (R.toHom hFn (even_two_mul r) hm) (θ₀.comp e) :=
      SURelations.HasFrameImages.oddFrameCompatible_toHom hFn hr hm hR hrange hchord
    refine ⟨θ₀.comp e, hrange, hchord, ?_⟩
    exact SURelations.HasFrameImages.extendsToHom_pairRoots_bc2_pos_toHom hFn hr hm h hML hq
      hF.toIsFrame hcard hR hd hrange hθ'r
      (fun u v u' v' h₁ h₂ =>
        commutatorElement_suHeis_oddPrevLift_comp (hFn := hFn) (hr := hr)
          (Ψ₀ := R.toHom hFn (even_two_mul r) hm) (θ := θ₀) (e := e) he
          (ξ := fun x => R.ξ (Sum.inl (cPrevIdx r hr)) (Sum.inl (cLastIdx r hr)) x)
          hss u v u' v' h₁ h₂)
      (fun s u v h₁ =>
        commutatorElement_short_suHeis_comp (hFn := hFn) (hr := hr)
          (Ψ₀ := R.toHom hFn (even_two_mul r) hm) (θ := θ₀) (e := e) he
          (ξ₁ := fun x => R.ξ (Sum.inl (cPrevIdx r hr)) (Sum.inr (cLastIdx r hr)) x)
          (ξ₂ := fun x => R.ξ (Sum.inl (cPrevIdx r hr)) (Sum.inl (cLastIdx r hr)) x)
          hsm s u v h₁)

theorem oddUnitaryStatement_of_heisRelations (hrel : OddFrameHeisRelations) :
    OddUnitaryStatement :=
  oddUnitaryStatement_of_bc2 (oddFrameBC2Statement_of_heisRelations hrel)

end CFSG.Timmesfeld.Transvection

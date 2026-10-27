module

public import Certificates.Kernel.D42Tri.RhoPen0
public import Certificates.Kernel.D42Tri.RhoPen1
public import Certificates.Kernel.D42Tri.RhoPen2
public import Certificates.Kernel.D42Tri.RhoPen3
public import Certificates.Kernel.D42Tri.RhoHs0
public import Certificates.Kernel.D42Tri.RhoHs1
public import Certificates.Kernel.OmegaEight.Bridge3009
public import CFSG.HardMathSupport.Dickson.Bal207.D42TriInputs
public import CFSG.Certificates.Kernel.Spor.MulHSound
public import CFSG.Certificates.Kernel.Spor.MulHFSound
public import CFSG.Certificates.Kernel.Spor.BaseMaskGlue
import CFSG.Certificates.Kernel.Common.ForallTree
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Certificates.Kernel.Census.SiftSound
public import CFSG.Certificates.Kernel.Spor.BaseMaskSound
public import CFSG.GroupTheory.LocalCores.Fitting
public import CFSG.LieType.Steinberg.Classical.SpinFrame
public import CFSG.LieType.Steinberg.Exceptional.E6E7
public import CFSG.LieType.Steinberg.Families
public import CFSG.LieType.Steinberg.G2
public import CFSG.LieType.Universal.Spin.Generation
public import CFSG.LieType.Universal.Spin.OddCT
public import CFSG.LieType.Universal.Spin.PlusCT
public import CFSG.LieType.Universal.Spin.Structure
public import CFSG.LieType.Universal.SpinOmega
public import CFSG.LieType.Universal.Unitary
public import CFSG.LocalAnalysis.ComponentClassification.AS76bDefs
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.GeneralizedFitting
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasFive
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasSix
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalReflectionSplitting
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplitCoverModel
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplitSylow
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.NativeBridgeBase
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.NativeCheckBase
public import CFSG.LocalAnalysis.SectionRank.ClassicalOdd
public import CFSG.LocalAnalysis.SectionRank.EvenCover.LinearStep
public import CFSG.LocalAnalysis.SectionRank.SporadicCover
public import CFSG.Sporadic.M23.M23Group
public import CFSG.Sporadic.SmallOddCore.CheckSpec
public import CFSG.Sporadic.Th.F2Spec
public import TauCeti.LinearAlgebra.CliffordAlgebra.Monomials

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelD42Tri

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.PEnum CFSG.KS.MulH
open CFSG.Sporadic.Th.Native CFSG.Sporadic.SmallOddCore.Native CFSG.EvenSmallLie.OmegaEight
open CFSG.HardMathSupport.Dickson.Bal207.D42Tri CertificateChecks.KernelO8

#kc_forall_tree pe_all
  (fun s => penumSlK 360 9 (mask 9) (360 * 9) true RC.G RC.GI 8 RC.cnt RC.T RC.PL RC.POS RC.SRT
    RC.SRI (600 * s) 600 = true) 24 CertificateChecks.KernelD42Tri.ch17628pe_

#kc_forall_tree hs_all
  (fun s => slK RC.cnt (hsortPtKF 360 9 (mask 9) RC.cnt RC.T RC.HS RC.HSI) (1200 * s) 1200 = true)
  12 CertificateChecks.KernelD42Tri.ch17628hsF_

theorem rcBind : bAnd(allN 8 (fun j => bAnd(Nat.beq (RC.G j) (AP.S j),
      bAnd(Nat.beq (RC.GI j) (pinv (AP.S j)), pm (AP.S j)))), Nat.beq RC.R (AP.S 8)) = true := by
  quickRfl

theorem rc_cnt : RC.cnt = 14400 := Nat.eq_of_beq_eq_true rcCnt

theorem rcCanon_parts : (∀ j < 8, canonK 360 9 (mask 9) (360 * 9) (RC.G j) = true ∧
      canonK 360 9 (mask 9) (360 * 9) (RC.GI j) = true) ∧
    canonK 360 9 (mask 9) (360 * 9) RC.R = true ∧ szOK 360 9 = true := by
  have h := rcCanon
  simp only [bAnd_iff] at h
  exact ⟨fun j hj => by simpa only [bAnd_iff] using allN_spec h.1 j hj, h.2⟩

theorem rcBind_parts : (∀ j < 8, RC.G j = AP.S j ∧ RC.GI j = pinv (AP.S j) ∧ pm (AP.S j) = true) ∧
    RC.R = AP.S 8 := by
  have h := rcBind
  simp only [bAnd_iff] at h
  refine ⟨fun j hj => ?_, Nat.eq_of_beq_eq_true h.2⟩
  have h' := allN_spec h.1 j hj
  simp only [bAnd_iff] at h'
  exact ⟨Nat.eq_of_beq_eq_true h'.1, Nat.eq_of_beq_eq_true h'.2.1, h'.2.2⟩

theorem arrTable_unpack (X : Nat) :
    CFSG.ComponentClassification.J2Cover.arrTable 360 (unpack 360 9 X) = tabT (unpack 360 9 X) := by
  apply Array.ext (by simp [CFSG.ComponentClassification.J2Cover.arrTable, tabT, unpack])
  intro i h1 h2
  simp [CFSG.ComponentClassification.J2Cover.arrTable, tabT, unpack]

theorem gens_tabs : TabsOK 360 9 8 RC.G (omGT ()) := by
  refine ⟨by simp [omGT], fun j hj => ⟨?_, (rcCanon_parts.1 j hj).1⟩⟩
  rw [getElem!_pos _ j (by simpa [omGT] using hj)]
  simp only [omGT, List.getElem_toArray, List.getElem_map, List.getElem_range]
  rw [gen_get (by omega), ← (rcBind_parts.1 j hj).1, arrTable_unpack]

theorem ginv_tabs : TabsOK 360 9 8 RC.GI (omGI ()) := by
  refine ⟨by simp [omGI], fun j hj => ⟨?_, (rcCanon_parts.1 j hj).2⟩⟩
  obtain ⟨-, e2, hp⟩ := rcBind_parts.1 j hj
  rw [getElem!_pos _ j (by simpa [omGI] using hj)]
  simp only [omGI, List.getElem_toArray, List.getElem_map, List.getElem_range]
  rw [gen_get (by omega), invCand_pinv hp, ← e2, arrTable_unpack]

theorem genArrs_eight' : genArrs[8]! = rhoArr := by
  have hlen : rootPairs.length = 8 := rfl
  rw [genArrs, getElem!_pos _ 8 (by simp [hlen]), Array.getElem_append_right (by simp [hlen])]
  simp [hlen]

theorem hRec_size' (cnt : Nat) (T PL : Nat → Nat) : (hRec 360 9 cnt T PL).1.size = cnt := by
  simp [hRec]

theorem rho_tab : rhoTbl () = tabT (unpack 360 9 RC.R) := by
  rw [rhoTbl, ← genArrs_eight', gen_get (by norm_num), ← rcBind_parts.2, arrTable_unpack]

theorem rhoClass_ok : rhoClassCheck = true := by
  have hp : ∀ i < RC.cnt, penumPtK 360 9 (mask 9) (360 * 9) true RC.G RC.GI 8 RC.cnt RC.T RC.PL
      RC.POS RC.SRT RC.SRI i = true := by
    intro i hi
    rw [rc_cnt] at hi
    have hb : i / 600 < 24 := by omega
    exact CFSG.KS.BaseMask.penumSl_spec (pe_all (i / 600) hb) (by omega) (by omega)
      (by rw [rc_cnt]; exact hi)
  have hs : ∀ i < RC.cnt, hsortPtK 360 9 (mask 9) RC.cnt RC.T RC.HS RC.HSI i = true := by
    intro i hi
    rw [← hsortPtKF_eq]
    have hi' := hi
    rw [rc_cnt] at hi'
    have hb : i / 1200 < 12 := by omega
    exact slK_spec (hs_all (i / 1200) hb) i (by omega) (by omega) hi
  obtain ⟨e, ht, hd⟩ := conjH_sound rcCanon_parts.2.2 gens_tabs ginv_tabs rho_tab rcHd hp hs
  unfold rhoClassCheck
  simp only
  rw [e, ht, hd, hRec_size', rc_cnt]
  decide

end CertificateChecks.KernelD42Tri

end

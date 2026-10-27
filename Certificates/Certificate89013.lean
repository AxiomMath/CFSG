module

public import Certificates.Data.CFSGNative.AS91.M24Geom
import CFSG.Certificates.Kernel.M24G.OrbitsSound
import Certificates.Kernel.M24G.TrioSextsEq
import Certificates.Kernel.M24G.SextFactsChecks
import Certificates.Kernel.M24G.LookChecks

public section

namespace CertificateChecks.Batch89013

open CFSG.KC.M24G CFSG.Quasithin.H13.AS91.M24G

private theorem uTabs_lt : ∀ g ∈ Native.uTabs, ∀ x ∈ g.toList, x < 24 := by decide

private theorem check_holds : Native.sextFactsCheck () = true := by
  rw [sextFactsCheck_eq, trioSexts_eq, trioList_eq, sextList_eq]
  simp only [toArray_getElem!_eq_getD]
  rw [sextFactsF_xi1 (xi1' := fun q => (maskL ((xiCls fun q => SL.getD q default).getD 1 [])).testBit q)
    fun p hp q hq => (xiCls_mask _ (tsRows_lt TSC.rows hp q hq)).symm]
  rw [← lookW_eq LookC.tl, ← lookW_eq LookC.ts, ← lookW_eq LookC.sl]
  refine sextFactsF_mono (fun hu => ?_) (fun cls h => ?_) (fun cls h => ?_) SextFactsC.ok
  · rw [← hu]
    exact all_congr_mem fun g hg => by rw [imgSext_eq (uTabs_lt g hg)]
  · rw [sextSteps_eq_sextStepsK sextList_eq (replay_facts sextReplay_ok).1 SextC.length SextC.items
      uTabs_lt, ← lookW_eq LookC.sl]
    exact classOrbitCheck_of_classOrbitK h
  · rw [trioSteps_eq_trioStepsK trioList_eq (replay_facts trioReplay_ok).1 TrioC.length TrioC.items
      uTabs_lt, ← lookW_eq LookC.tl]
    exact classOrbitCheck_of_classOrbitK h

end CertificateChecks.Batch89013

namespace Certificates

open CertificateChecks

theorem certificate89013 : CFSG.Quasithin.H13.AS91.M24G.Native.sextFactsCheck () = true :=
  CertificateChecks.Batch89013.check_holds

end Certificates

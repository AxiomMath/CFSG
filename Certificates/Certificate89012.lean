module

public import Certificates.Data.CFSGNative.AS91.M24Geom
import CFSG.Certificates.Kernel.M24G.OrbitsSound
import Certificates.Kernel.M24G.TrioSextsEq
import Certificates.Kernel.M24G.DeltaChecks
import Certificates.Kernel.M24G.LookChecks

public section

namespace CertificateChecks.Batch89012

open CFSG.KC.M24G CFSG.Quasithin.H13.AS91.M24G

private theorem lTabs_lt : ∀ g ∈ Native.lTabs, ∀ x ∈ g.toList, x < 24 := by decide

private theorem check_holds : Native.deltaCheck () = true := by
  rw [deltaCheck_eq, trioSexts_eq, trioList_eq]
  simp only [toArray_getElem!_eq_getD]
  rw [← lookW_eq LookC.tl, ← lookW_eq LookC.ts]
  refine deltaCkF_mono (fun cls h => ?_) DeltaC.ok
  rw [trioSteps_eq_trioStepsK trioList_eq (replay_facts trioReplay_ok).1 TrioC.length TrioC.items
    lTabs_lt, ← lookW_eq LookC.tl]
  exact classOrbitCheck_of_classOrbitK h

end CertificateChecks.Batch89012

namespace Certificates

open CertificateChecks

theorem certificate89012 : CFSG.Quasithin.H13.AS91.M24G.Native.deltaCheck () = true :=
  CertificateChecks.Batch89012.check_holds

end Certificates

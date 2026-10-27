module

public import Certificates.Data.CFSGNative.AS91.M24Geom
import CFSG.Certificates.Kernel.M24G.DualSound
import Certificates.Kernel.M24G.ListsEq
import Certificates.Kernel.M24G.TrioChecks
import Certificates.Kernel.M24G.DualChecks

public section

namespace CertificateChecks.Batch89017

open CFSG.KC.M24G CFSG.Quasithin.H13.AS91.M24G

private theorem check_holds : Native.sextDualCheck () = true := by
  have hLU : (List.range Native.nTrio).filter
      (fun p => Native.trioIn TL.toArray[p]! SL.toArray[0]!) = DualD.LU :=
    filter_range_eq_of_allIdx (f := fun x => Native.trioIn x SL.toArray[0]!) TrioC.length
      DualC.lu_ok DualC.lu_asc DualC.lu_lt
  have htr : ∀ a ∈ DualD.LU, TL.toArray[a]! = tabLU DualD.LU DualD.TU a := by
    have h := DualC.tu_ok
    rw [List.all_eq_true] at h
    exact fun a ha => beq_iff_eq.1 (h a ha)
  rw [sextDualCheck_eq, sextTrios_trioSexts (by decide), trioList_eq, sextList_eq, hLU,
    dualCk_congr htr]
  exact DualC.dual_ok

end CertificateChecks.Batch89017

namespace Certificates

open CertificateChecks

theorem certificate89017 : CFSG.Quasithin.H13.AS91.M24G.Native.sextDualCheck () = true :=
  CertificateChecks.Batch89017.check_holds

end Certificates

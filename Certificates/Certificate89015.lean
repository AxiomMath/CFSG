module

public import Certificates.Data.CFSGNative.AS91.M24Geom
import CFSG.Certificates.Kernel.M24G.C311Sound
import Certificates.Kernel.M24G.TrioSextsEq
import Certificates.Kernel.M24G.DualChecks
import Certificates.Kernel.M24G.C311Checks

public section

namespace CertificateChecks.Batch89015

open CFSG.KC.M24G CFSG.Quasithin.H13.AS91.M24G

private theorem check_holds : Native.stmt311Check () = true := by
  have hLU : Native.sextTrios TS.toArray 0 = DualD.LU := by
    unfold Native.sextTrios
    exact filter_range_eq_of_allIdx (f := fun r => r.contains 0) C311C.ts_length C311C.lu_ts
      DualC.lu_asc DualC.lu_lt
  have htu : ∀ a ∈ DualD.LU, TL.toArray[a]! = tabLU DualD.LU DualD.TU a := by
    have h := DualC.tu_ok
    rw [List.all_eq_true] at h
    exact fun a ha => beq_iff_eq.1 (h a ha)
  have hru : ∀ a ∈ DualD.LU, TS.toArray[a]! = tabRow DualD.LU C311D.RU a := by
    have h := C311C.ru_ok
    rw [List.all_eq_true] at h
    exact fun a ha => beq_iff_eq.1 (h a ha)
  exact stmt311Check_of trioList_eq trioSexts_eq TrioC.length C311C.ts_length hLU htu hru
    C311C.ds_ok C311C.ds_len C311C.a_ok C311C.nb_ok C311C.b_ok

end CertificateChecks.Batch89015

namespace Certificates

open CertificateChecks

theorem certificate89015 : CFSG.Quasithin.H13.AS91.M24G.Native.stmt311Check () = true :=
  CertificateChecks.Batch89015.check_holds

end Certificates

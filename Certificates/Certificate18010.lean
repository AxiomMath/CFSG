module

public import CFSG.LocalAnalysis.SteinbergCCHSChecksCertificate18010Inputs
import Certificates.Kernel.HSCover18010.Glue
public import Certificates.Data.CFSGNative.HS.Data

public section

namespace Certificates

open CertificateChecks

open CFSG.CosetTable CFSG.LieType.Multipliers in
theorem certificate18010 : (
    Finite (PG 3 CFSG.LocalAnalysis.HigmanSimsCover.rels) ∧
      Nat.card (PG 3 CFSG.LocalAnalysis.HigmanSimsCover.rels) ≤ 44352000
  ) ∧ (
    Finite (PG 3 CFSG.LocalAnalysis.HigmanSimsCover.coverWs) ∧
      Nat.card (PG 3 CFSG.LocalAnalysis.HigmanSimsCover.coverWs) ≤ 88704000
  ) ∧ (
    2 ∣ orderOf (PresentedGroup.mk
      {r : FreeGroup (Fin 3) | r ∈ CFSG.LocalAnalysis.HigmanSimsCover.coverWs.map FreeGroup.mk}
      (FreeGroup.mk CFSG.LocalAnalysis.HigmanSimsCover.kerWord))
  ) ∧ (
    CFSG.Sporadic.Bridge.TwoGen.Native.vecRelCheck CFSG.Sporadic.HS.Native.hsData
      (CFSG.LocalAnalysis.HigmanSimsCover.hsWords.map (List.map fun l => (l.1.val, l.2))) = true
  ) :=
  ⟨KernelHS18010.presented_bound, KernelHS18010.cover_bound, KernelHS18010.kerWord_order,
    KernelHS18010.hs_check⟩

end Certificates

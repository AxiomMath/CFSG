module

public import CFSG.Sporadic.Recognition.HSPinnedIdentInputs
public import CFSG.Sporadic.Recognition.HSGraphModelInputs
public import Certificates.Data.CFSGNative.Recognition.HSPinnedData
import Certificates.Kernel.HSIdent.Check
import CFSG.Certificates.Kernel.HSIdentSound

public section

namespace Certificates

open CertificateChecks

open CFSG.Sporadic.Recognition.HSGraph CFSG.ComponentClassification.WittDesign
  CFSG.Sporadic.Recognition.HSPinned CFSG.Sporadic.Recognition.HSPinned.Native in
theorem certificate6102 : (∀ i j : Fin 100, isoFun i = isoFun j → i = j)
    ∧ (∀ i j : Fin 100, adjB i.val j.val = true ↔
      (hsGraph hexads).Adj (modelVertAtF (isoFun i)) (modelVertAtF (isoFun j))) :=
  ⟨CFSG.KC.HSIdent.isoFun_injective_of KernelHSIdent.injCheck_ok,
    CFSG.KC.HSIdent.iso_check_of KernelHSIdent.identCheck_ok⟩

end Certificates

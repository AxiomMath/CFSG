module

public import CFSG.LocalAnalysis.ComponentClassification.CatFactsSmallPSp43ModelData
public import CFSG.GH74.KGroups.NativeChecks2
public meta import CFSG.GH74.KGroups.NativeChecks2
public meta import CFSG.Fischer.Classification.PartIII.Beta.Data
import Certificates.Kernel.Sporadic.PSp45.Facts
import Certificates.Kernel.Sporadic.PSp45.Neg
public meta import Mathlib

public section

open CFSG CFSG.ComponentClassification CFSG.ComponentClassification.CatFactsSmall
open CFSG.ComponentClassification.CatFactsSmall.PSp43 CFSG.GH74.KGroups CFSG.Certificates
open CFSG.Sporadic.Schreier Subgroup CFSG.Fischer.Classification.Beta

local notation "P45" => Equiv.Perm (Fin 45)

public section

namespace Certificates

open CertificateChecks

open CFSG CFSG.ComponentClassification CFSG.ComponentClassification.CatFactsSmall in
open CFSG.ComponentClassification.CatFactsSmall.PSp43 CFSG.GH74.KGroups CFSG.Certificates in
open CFSG.Sporadic.Schreier Subgroup CFSG.Fischer.Classification.Beta in
theorem certificate2012 : (QP45.check = true ∧ QP45.orderCertificate = 25920)
    ∧ (QA45.check = true ∧ QA45.orderCertificate = 51840)
    ∧ ((List.finRange 45).all (fun j => QP45.sift (tauPerm j) 0) = true)
    ∧ (orderIs x45 2 = true ∧ orderIs y45 5 = true ∧
      pairInvB ws45 x45 y45 = true
    )
    ∧ (NativeChecks.pairCountE QP45 2 5 ws45 = 51840)
    ∧ (normCheck QP45 QA45.original.toList x45 y45 = true)
    ∧ (CFSG.KGroups.Native.centTrivA 45 (NativeChecks.enumA QA45)
      (NativeChecks.toA x45) (NativeChecks.toA y45) = true
    ) := KernelSpor.PSp45.facts

end Certificates

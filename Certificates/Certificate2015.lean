
module

public import Certificates.Certificate2015Base

public import CFSG.LocalAnalysis.ComponentClassification.CatFactsSmallQ3P45Inputs
public meta import CFSG.LocalAnalysis.ComponentClassification.CatFactsSmallPSp43Model
public meta import CFSG.LocalAnalysis.ComponentClassification.CatFactsSmallArrChecks
public meta import CFSG.LocalAnalysis.ComponentClassification.CatFactsSmallQ3Gen
public meta import CFSG.GH74.KGroups.Checks3
import Certificates.Kernel.Census.CatFacts.C2015

public section

open CFSG CFSG.ComponentClassification CFSG.ComponentClassification.CatFactsSmall
open CFSG.ComponentClassification.CatFactsSmall.PSp43 CFSG.GH74.KGroups CFSG.Certificates
open CFSG.Sporadic.Schreier Subgroup CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
open CFSG.KGroups.Native CFSG.GH74.KGroups.NativeChecks

public section

namespace Certificates

open CertificateChecks

open CFSG CFSG.ComponentClassification CFSG.ComponentClassification.CatFactsSmall in
open CFSG.ComponentClassification.CatFactsSmall.PSp43 CFSG.GH74.KGroups CFSG.Certificates in
open CFSG.Sporadic.Schreier Subgroup CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native in
open CFSG.KGroups.Native CFSG.GH74.KGroups.NativeChecks in
local notation "P45" => Equiv.Perm (Fin 45)

theorem certificate2015 : (noNilpA 45 (enumA QA45) ((enumA QP45).filter oddTestA) 405 = true)
    ∧ (admCheckA (elemsTab QA45) QP45 five45A s045 admConj = true)
    ∧ (QA45.sift s045 0 = true)
    ∧ (QL45.check = true ∧ QL45.orderCertificate = 360)
    ∧ (oddNormalCheck (elemsT QL45) 45 = true)
    ∧ (((elemsT QP45).filter (fun g => decide (g * s045 = s045 * g))).length = 720)
    ∧ (QP45.sift la1 0 = true ∧ QP45.sift lb1 0 = true ∧ QP45.sift lb2 0 = true ∧
      la1 * s045 = s045 * la1 ∧ lb1 * s045 = s045 * lb1 ∧ lb2 * s045 = s045 * lb2
    )
    ∧ (QQ45.check = true ∧ QQ45.orderCertificate = 32)
    ∧ ((elemsT QQ45).all (fun q => QQ45.sift (g045 * q * g045⁻¹) 0) = true ∧
      QQ45.sift g045 0 = false ∧ QQ45.sift (g045 * g045) 0 = true ∧ QP45.sift g045 0 = true ∧
      QP45.sift (s045 * (g045⁻¹ * s045 * g045)) 0 = true ∧
      (q0gens.all fun q => QA45.sift q 0 && decide (q * s045 = s045 * q)) = true
    )
    ∧ (((elemsT QA45).filter (fun g => decide (g * s045 = s045 * g))).length = 2 ^ 5 * 45) := KernelCatFacts.facts2015

end Certificates

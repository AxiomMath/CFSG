
module

public import CFSG.LocalAnalysis.ComponentClassification.CatFactsSmallQ3A8DataInputs
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsSmallQ3A8
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsSmallQ3Gen
public import CFSG.GH74.KGroups.Checks3
public import Certificates.Data.Kernel.Census.CatFacts.PkDefs

public section

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace CertificateChecks.KernelCatFacts

open CFSG.ComponentClassification.CatFactsSmall CFSG.ComponentClassification.CatFactsSmall.A8
  CFSG.Certificates.Kernel.PkEnum

theorem adm2014K : ((elemsV QS8).all fun s => !(decide (s * s = 1)) || siftP QA8 s 0 ||
    (admConj.any fun k => decide (k * s8 * k⁻¹ = s)) ||
    ((elemsV QA8).filter fun x => decide (x ^ 5 = 1) && !decide (x = 1)).all fun x =>
      !(decide (x * s = s * x))) = true := by
  decide +kernel

theorem ql8_2014K : QL8.check = true ∧ QL8.orderCertificate = 360 := by
  constructor <;> decide +kernel

theorem oddNormal2014K : oddNormalCheck (elemsV QL8) 45 = true := by
  decide +kernel

theorem cA2014K : ((elemsV QA8).filter (fun g => decide (g * s8 = s8 * g))).length = 720 := by
  decide +kernel

theorem qq8_2014K : QQ8.check = true ∧ QQ8.orderCertificate = 32 := by
  constructor <;> decide +kernel

theorem g08_2014K : (elemsV QQ8).all (fun q => QQ8.sift (g08 * q * g08⁻¹) 0) = true ∧
    QQ8.sift g08 0 = false ∧ QQ8.sift (g08 * g08) 0 = true := by
  refine ⟨?_, ?_, ?_⟩ <;> decide +kernel

theorem cS2014K :
    ((elemsV QS8).filter (fun g => decide (g * s8 = s8 * g))).length = 2 ^ 5 * 45 := by
  decide +kernel

theorem neg2014K : ((elemsV QA8).filter (fun g => decide (g * s8 = s8 * g))).length ≠ 721 ∧
    ((elemsV QS8).all fun s => !(decide (s * s = 1)) || siftP QA8 s 0 ||
      (([] : List (Equiv.Perm (Fin 8))).any fun k => decide (k * s8 * k⁻¹ = s)) ||
      ((elemsV QA8).filter fun x => decide (x ^ 5 = 1) && !decide (x = 1)).all fun x =>
        !(decide (x * s = s * x))) = false := by
  constructor <;> decide +kernel

end CertificateChecks.KernelCatFacts

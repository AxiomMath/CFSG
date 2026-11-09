
module

public import CFSG.LocalAnalysis.ComponentClassification.CatFactsSmallQ3A8DataInputs
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsSmallQ3A8
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsSmallQ3Gen
public import CFSG.GH74.KGroups.Checks3
public import Certificates.Data.Kernel.Census.CatFacts.PkDefs
public import Mathlib.GroupTheory.Perm.Cycle.Concrete

public section

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace CertificateChecks.KernelCatFacts

open CFSG.ComponentClassification.CatFactsSmall CFSG.ComponentClassification.CatFactsSmall.A8
  CFSG.Certificates.Kernel.PkEnum

theorem admSwap2014K : ∀ x y : Fin 8, x ≠ y →
    (admConj.any fun k => decide (k * s8 * k⁻¹ = Equiv.swap x y)) = true := by
  decide +kernel

@[expose] def onC2014 : List (Equiv.Perm (Fin 8)) :=
  [c[2, 3] * c[4, 5, 6, 7], c[2, 3] * c[4, 5, 7, 6], c[4, 6] * c[5, 7], c[2, 4, 3, 6, 7],
    c[2, 4, 5, 3, 7], c[2, 5, 7, 4, 6], c[3, 4, 7, 6, 5]]

theorem on2014K : (elemsV QL8).all (fun x => decide (x = 1) || decide (x ^ 4 = 1) ||
    onC2014.any fun c => decide ((x * c * x⁻¹ * c⁻¹) ^ 4 = 1) && !decide (x * c * x⁻¹ * c⁻¹ = 1)) =
    true := by
  decide +kernel

theorem onS2014K : onC2014.all (fun c => siftP QL8 c 0) = true := by
  decide +kernel

theorem ql8_2014K : QL8.check = true ∧ QL8.orderCertificate = 360 := by
  constructor <;> decide +kernel

theorem qq8_2014K : QQ8.check = true ∧ QQ8.orderCertificate = 32 := by
  constructor <;> decide +kernel

theorem g08_2014K : (elemsV QQ8).all (fun q => QQ8.sift (g08 * q * g08⁻¹) 0) = true ∧
    QQ8.sift g08 0 = false ∧ QQ8.sift (g08 * g08) 0 = true := by
  refine ⟨?_, ?_, ?_⟩ <;> decide +kernel

theorem neg2014K : (elemsV QL8).all (fun x => decide (x = 1) || decide (x ^ 4 = 1) ||
      (onC2014.take 6).any fun c => decide ((x * c * x⁻¹ * c⁻¹) ^ 4 = 1) &&
        !decide (x * c * x⁻¹ * c⁻¹ = 1)) = false ∧
    ((([] : List (Equiv.Perm (Fin 8))).any fun k =>
      decide (k * s8 * k⁻¹ = Equiv.swap (0 : Fin 8) 1)) = false) := by
  constructor <;> decide +kernel

end CertificateChecks.KernelCatFacts

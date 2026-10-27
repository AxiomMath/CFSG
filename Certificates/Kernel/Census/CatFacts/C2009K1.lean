
module

public import Certificates.Data.Kernel.Census.CatFacts.C2009Defs

public section

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace CertificateChecks.KernelCatFacts

open CFSG.ComponentClassification.CatFactsSmall CFSG.ComponentClassification.CatFactsSmall.PSp43
  CFSG.Certificates.Kernel.PkEnum CFSG.GH74.KGroups CFSG.Sporadic.Schreier

theorem comm2009K : (q0gens.all fun q => decide (q * cfTau = cfTau * q) &&
    decide (q * cfZ = cfZ * q)) = true ∧ g045⁻¹ * cfZ * g045 = cfZ := by
  constructor <;> decide +kernel

theorem z2009K : (elemsV QQ45).all (fun w => !siftP QL45 w 0 || !decide (w * w = 1) ||
      decide (w = 1) || decide (w = cfZ) ||
      (elemsV QQ45).any (fun v => siftP QL45 v 0 && !decide (w * v = v * w))) = true := by
  decide +kernel

theorem qh2009K : schP cfQH = true ∧ orderV cfQH = 64 := by
  constructor <;> decide +kernel

theorem qr2009K : schP cfQR = true ∧ orderV cfQR = 128 := by
  constructor <;> decide +kernel

theorem r2009K : (cfRgens.all fun x => siftP QA45 x 0 &&
      decide (x * (cfTau * cfZ) = cfTau * cfZ * x)) = true ∧
    (elemsV cfQR).all (fun x => !(cfRgens.all fun g => decide (g * x = x * g)) ||
      decide (x = 1) || decide (x = cfTau * cfZ)) = true ∧
    siftP cfQR (cfTau * cfZ) 0 = true ∧ (cfTau * cfZ) * (cfTau * cfZ) = 1 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide +kernel

theorem card2009K : ((elemsV QQ45).filter fun x => siftP QL45 x 0).length = 8 ∧
    ((elemsV QL45).filter fun x => decide (x * cfTau = cfTau * x)).length = 24 ∧
    ((elemsV cfQR).filter fun x => decide (x * cfZ = cfZ * x)).length = 64 := by
  refine ⟨?_, ?_, ?_⟩ <;> decide +kernel

theorem qeq2009K : (q0gens.all fun q => siftP QL45 q 0 || siftP QL45 (q * cfTau⁻¹) 0 ||
      siftP QL45 (q * s045⁻¹) 0 || siftP QL45 (q * s045⁻¹ * cfTau⁻¹) 0) = true ∧
    siftP QQ45 cfTau 0 = true ∧ siftP QQ45 s045 0 = true := by
  refine ⟨?_, ?_, ?_⟩ <;> decide +kernel

theorem elt2009K : siftP cfQR cfTzu 0 = true ∧ siftP cfQR cfTzv 0 = true ∧
    cfTzu * cfTzv * cfTzu⁻¹ * cfTzv⁻¹ = cfTau * cfZ ∧ siftP QP45 cfK0 0 = true ∧
    cfK0⁻¹ * cfZ * cfK0 = cfTau := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

theorem qd2009K : schP cfQD1 = true ∧ orderV cfQD1 = 8 ∧ schP cfQD2 = true ∧
    orderV cfQD2 = 8 ∧ schP cfQD12 = true ∧ orderV cfQD12 = 64 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

end CertificateChecks.KernelCatFacts

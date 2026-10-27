
module

public import Certificates.Data.Kernel.Census.CatFacts.C2009Defs

public section

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace CertificateChecks.KernelCatFacts

open CFSG.ComponentClassification.CatFactsSmall CFSG.ComponentClassification.CatFactsSmall.PSp43
  CFSG.Certificates.Kernel.PkEnum CFSG.Certificates.Kernel.CatFacts CFSG.GH74.KGroups
  CFSG.Sporadic.Schreier

theorem orb2009K : (cfOz.all fun p => decide (p.2⁻¹ * cfZ * p.2 = p.1) && siftP QA45 p.2 0 &&
      (cfEgens.all fun e => siftP cfQE (p.2 * e * p.2⁻¹) 0)) = true ∧
    (cfOzt.all fun p => decide (p.2⁻¹ * (cfZ * cfTau) * p.2 = p.1) && siftP QA45 p.2 0 &&
      (cfEgens.all fun e => siftP cfQE (p.2 * e * p.2⁻¹) 0)) = true ∧
    (cfOz.map Prod.fst).Nodup ∧ (cfOzt.map Prod.fst).Nodup ∧
    (elemsV cfQE).all (fun w => decide (w = 1) || decide (w ∈ cfOz.map Prod.fst) ||
      decide (w ∈ cfOzt.map Prod.fst)) = true ∧
    (cfOz.all fun p => siftP cfQE p.1 0) = true ∧ (cfOzt.all fun p => siftP cfQE p.1 0) = true := by
  repeat' apply And.intro
  all_goals decide +kernel

theorem esub2009K : (cfEgens.all fun x => decide (x ∈ cfOzt.map Prod.fst)) = true := by
  decide +kernel

theorem normal2009K : (elemsV cfQR).all (fun w => !decide (w * w = 1) || siftP QP45 w 0 ||
    decide (w ∈ cls1P) ||
    (elemsV cfQR).any (fun r => !decide (w * (r * w * r⁻¹) = r * w * r⁻¹ * w)) ||
    decide (((elemsV cfQR).filter fun y => decide (y * y = 1) && !decide (y ∈ cls1P) &&
      (elemsV cfQR).all fun r => decide (y * (r * w * r⁻¹) = r * w * r⁻¹ * y)).length < 16)) =
      true := by
  decide +kernel

theorem misc2009K : (elemsV cfQE).all (fun e => decide (e * s045 * e⁻¹ * s045⁻¹ = 1) ||
      decide (e * s045 * e⁻¹ * s045⁻¹ = cfCE)) = true ∧ s045 * s045 = 1 ∧
    siftP cfQE cfE1 0 = true ∧ cfE1 * s045 * cfE1⁻¹ * s045⁻¹ = cfCE ∧ cfCE * cfCE = 1 ∧
    cfCE ≠ 1 ∧ siftP cfQR cfEe 0 = true ∧ siftP QP45 cfEe 0 = true ∧
    cfEn1 * cfEn2 * cfEn1⁻¹ * cfEn2⁻¹ = cfEe ∧ cfEe * cfEe = 1 ∧
    (cfEgens.all fun g => decide (g * cfEe = cfEe * g)) = false ∧ siftP QA45 cfEn1 0 = true ∧
    siftP QA45 cfEn2 0 = true ∧ (cfEgens.all fun e => siftP cfQE (cfEn1 * e * cfEn1⁻¹) 0) = true ∧
    (cfEgens.all fun e => siftP cfQE (cfEn2 * e * cfEn2⁻¹) 0) = true := by
  repeat' apply And.intro
  all_goals decide +kernel

theorem e32_2009K : (elemsV cfQR).all (fun x => !decide (x * x = 1) || decide (x = 1) ||
    decide (x ∈ cfB) || decide (((elemsV cfQR).filter fun y => decide (y * y = 1) &&
      decide (y * x = x * y)).length < 32)) = true := by
  decide +kernel

end CertificateChecks.KernelCatFacts

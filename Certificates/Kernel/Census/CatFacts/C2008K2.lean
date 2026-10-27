
module

public import CFSG.LocalAnalysis.ComponentClassification.CatFactsSmallConfA8Inputs
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsSmallQ3A8Data
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsSmallConfChecks2
public import Certificates.Data.Kernel.Census.CatFacts.PkDefs

public section

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace CertificateChecks.KernelCatFacts

open CFSG.ComponentClassification.CatFactsSmall CFSG.ComponentClassification.CatFactsSmall.A8
  CFSG.Certificates.Kernel.PkEnum CFSG.Sporadic.Schreier

theorem cfComm2008K : (q0gens.all fun q => decide (q * cfTau = cfTau * q) &&
    decide (q * cfZ = cfZ * q)) = true ∧ g08⁻¹ * cfZ * g08 = cfZ := by
  constructor <;> decide +kernel

theorem cfZ2008K : (elemsV QQ8).all (fun w => !siftP QL8 w 0 || !decide (w * w = 1) ||
    decide (w = 1) || decide (w = cfZ) ||
    (elemsV QQ8).any (fun v => siftP QL8 v 0 && !decide (w * v = v * w))) = true := by
  decide +kernel

theorem cfQH2008K : schP cfQH = true ∧ orderV cfQH = 64 := by
  constructor <;> decide +kernel

theorem cfQR2008K : schP cfQR = true ∧ orderV cfQR = 128 := by
  constructor <;> decide +kernel

theorem cfR2008K : (cfRgens.all fun x => siftP QS8 x 0 &&
    decide (x * (cfTau * cfZ) = cfTau * cfZ * x)) = true ∧
    (elemsV cfQR).all (fun x => !(cfRgens.all fun g => decide (g * x = x * g)) ||
      decide (x = 1) || decide (x = cfTau * cfZ)) = true ∧
    siftP cfQR (cfTau * cfZ) 0 = true ∧ (cfTau * cfZ) * (cfTau * cfZ) = 1 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide +kernel

theorem cfCardR2008K : ((elemsV QQ8).filter fun x => siftP QL8 x 0).length = 8 ∧
    ((elemsV QL8).filter fun x => decide (x * cfTau = cfTau * x)).length = 24 ∧
    ((elemsV cfQR).filter fun x => decide (x * cfZ = cfZ * x)).length = 64 := by
  refine ⟨?_, ?_, ?_⟩ <;> decide +kernel

theorem cfQeq2008K : (q0gens.all fun q => siftP QL8 q 0 || siftP QL8 (q * cfTau⁻¹) 0 ||
    siftP QL8 (q * s8⁻¹) 0 || siftP QL8 (q * s8⁻¹ * cfTau⁻¹) 0) = true ∧
    siftP QQ8 cfTau 0 = true ∧ siftP QQ8 s8 0 = true := by
  refine ⟨?_, ?_, ?_⟩ <;> decide +kernel

theorem cfElt2008K : siftP cfQR cfTzu 0 = true ∧ siftP cfQR cfTzv 0 = true ∧
    cfTzu * cfTzv * cfTzu⁻¹ * cfTzv⁻¹ = cfTau * cfZ ∧ siftP QA8 cfK0 0 = true ∧
    cfK0⁻¹ * cfZ * cfK0 = cfTau := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

theorem cfQD2008K : schP cfQD1 = true ∧ orderV cfQD1 = 8 ∧ schP cfQD2 = true ∧
    orderV cfQD2 = 8 ∧ schP cfQD12 = true ∧ orderV cfQD12 = 64 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

theorem cfD2008K : orderIs cfR1 4 = true ∧ orderIs cfR2 4 = true ∧ cfS1 * cfS1 = 1 ∧
    cfS2 * cfS2 = 1 ∧ cfS1 * cfR1 * cfS1⁻¹ = cfR1⁻¹ ∧ cfS2 * cfR2 * cfS2⁻¹ = cfR2⁻¹ ∧
    cfR1 * cfR1 = cfZ ∧ cfR2 * cfR2 = cfTau ∧ cfZ * cfZ = 1 ∧ cfTau * cfTau = 1 ∧
    ([cfR1, cfS1, cfR2, cfS2].all fun x => siftP cfQR x 0 && decide (x * cfZ = cfZ * x)) = true ∧
    ([cfR1, cfS1].all fun x => [cfR2, cfS2].all fun y => decide (y * x = x * y)) = true ∧
    ((List.range 4).all fun k => !decide (cfS1 = cfR1 ^ k)) = true ∧
    ((List.range 4).all fun k => !decide (cfS2 = cfR2 ^ k)) = true ∧
    (elemsV cfQD1).all (fun x => decide (x = 1) || !siftP cfQD2 x 0) = true ∧
    (elemsV cfQD1).all (fun x => decide ((cfR1 * x = x * cfR1 ∧ cfS1 * x = x * cfS1) ↔
      (x = 1 ∨ x = cfZ))) = true ∧
    (elemsV cfQD2).all (fun x => decide ((cfR2 * x = x * cfR2 ∧ cfS2 * x = x * cfS2) ↔
      (x = 1 ∨ x = cfTau))) = true := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

theorem cfQF2008K : schP cfQF1 = true ∧ orderV cfQF1 = 16 ∧ schP cfQF2 = true ∧
    orderV cfQF2 = 16 ∧ schP cfQF3 = true ∧ orderV cfQF3 = 16 ∧
    schP cfQRz = true ∧ orderV cfQRz = 64 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

theorem cfF2008K : (cfFgens.all fun x => siftP cfQR x 0 && decide (x * cfZ = cfZ * x)) = true ∧
    (elemsV cfQF1).all (fun x => decide (x * x = 1)) = true ∧
    (elemsV cfQF2).all (fun x => decide (x * x = 1)) = true ∧
    (elemsV cfQF3).all (fun x => decide (x * x = 1)) = true ∧
    siftP cfQRz cfZ 0 = true ∧ siftP cfQRz cfTau 0 = true ∧ siftP cfQRz cfR1 0 = true ∧
    siftP cfQRz cfR2 0 = true ∧ (cfFgens.all fun x => decide (x * cfZ = cfZ * x) &&
      decide (x * cfTau = cfTau * x)) = true ∧
    (elemsV cfQRz).all (fun x => !(cfFgens.all fun g => decide (g * x = x * g)) ||
      (decide (x = 1) || decide (x = cfZ) || decide (x = cfTau) || decide (x = cfZ * cfTau))) =
      true ∧
    (elemsV cfQRz).all (fun x => decide (x * x = 1) || decide (x * x = cfZ) ||
      decide (x * x = cfTau) || decide (x * x = cfZ * cfTau)) = true := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

theorem cfQE2008K : schP cfQE = true ∧ orderV cfQE = 16 := by
  constructor <;> decide +kernel

theorem cfE2008K : (cfEgens.all fun x => siftP cfQR x 0 && siftP QA8 x 0) = true ∧
    (elemsV cfQE).all (fun x => decide (x * x = 1)) = true ∧ siftP cfQE cfZ 0 = true ∧
    siftP cfQE cfTau 0 = true := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide +kernel

theorem cfEUniq2008K : ((elemsV cfQR).filter fun x => siftP QA8 x 0).all (fun x =>
    !decide (x * x = 1) || siftP cfQE x 0 || decide ((((elemsV cfQR).filter fun x =>
      siftP QA8 x 0).filter fun y => decide (y * y = 1) && decide (y * x = x * y)).length <
        16)) = true := by
  decide +kernel

theorem cfOrb2008K : (cfOz.all fun p => decide (p.2⁻¹ * cfZ * p.2 = p.1) && siftP QS8 p.2 0 &&
      (cfEgens.all fun e => siftP cfQE (p.2 * e * p.2⁻¹) 0)) = true ∧
    (cfOzt.all fun p => decide (p.2⁻¹ * (cfZ * cfTau) * p.2 = p.1) && siftP QS8 p.2 0 &&
      (cfEgens.all fun e => siftP cfQE (p.2 * e * p.2⁻¹) 0)) = true ∧
    (cfOz.map Prod.fst).Nodup ∧ (cfOzt.map Prod.fst).Nodup ∧
    (elemsV cfQE).all (fun w => decide (w = 1) || decide (w ∈ cfOz.map Prod.fst) ||
      decide (w ∈ cfOzt.map Prod.fst)) = true ∧
    (cfOz.all fun p => siftP cfQE p.1 0) = true ∧ (cfOzt.all fun p => siftP cfQE p.1 0) = true := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

theorem cfEwit2008K : (cfEgens.all fun x => (cfOz.map Prod.fst).any fun u =>
    (cfOz.map Prod.fst).any fun v => decide (x = u * v)) = true := by
  decide +kernel

theorem cfNormal2008K : (elemsV cfQR).all (fun w => !decide (w * w = 1) || siftP QA8 w 0 ||
    (fun y => decide (y ∈ cfCls1C)) w ||
    (elemsV cfQR).any (fun r => !decide (w * (r * w * r⁻¹) = r * w * r⁻¹ * w)) ||
    decide (((elemsV cfQR).filter fun y => decide (y * y = 1) &&
      !(fun y => decide (y ∈ cfCls1C)) y &&
      (elemsV cfQR).all fun r => decide (y * (r * w * r⁻¹) = r * w * r⁻¹ * y)).length < 16)) =
      true := by
  decide +kernel

theorem cfMisc2008K : (elemsV cfQE).all (fun e => decide (e * s8 * e⁻¹ * s8⁻¹ = 1) ||
      decide (e * s8 * e⁻¹ * s8⁻¹ = cfCE)) = true ∧ s8 * s8 = 1 ∧
    siftP cfQE cfE1 0 = true ∧ cfE1 * s8 * cfE1⁻¹ * s8⁻¹ = cfCE ∧ cfCE * cfCE = 1 ∧
    cfCE ≠ 1 ∧ siftP cfQR cfEe 0 = true ∧ siftP QA8 cfEe 0 = true ∧
    cfEn1 * cfEn2 * cfEn1⁻¹ * cfEn2⁻¹ = cfEe ∧ cfEe * cfEe = 1 ∧
    (cfEgens.all fun g => decide (g * cfEe = cfEe * g)) = false ∧ siftP QS8 cfEn1 0 = true ∧
    siftP QS8 cfEn2 0 = true ∧ (cfEgens.all fun e => siftP cfQE (cfEn1 * e * cfEn1⁻¹) 0) = true ∧
    (cfEgens.all fun e => siftP cfQE (cfEn2 * e * cfEn2⁻¹) 0) = true := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

theorem cfE322008K : (elemsV cfQR).all (fun x => !decide (x * x = 1) || decide (x = 1) ||
    decide (x ∈ cfB) || decide (((elemsV cfQR).filter fun y => decide (y * y = 1) &&
      decide (y * x = x * y)).length < 32)) = true := by
  decide +kernel

end CertificateChecks.KernelCatFacts

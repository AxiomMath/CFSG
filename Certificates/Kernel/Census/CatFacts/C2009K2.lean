
module

public import Certificates.Data.Kernel.Census.CatFacts.C2009Defs

public section

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace CertificateChecks.KernelCatFacts

open CFSG.ComponentClassification.CatFactsSmall CFSG.ComponentClassification.CatFactsSmall.PSp43
  CFSG.Certificates.Kernel.PkEnum CFSG.GH74.KGroups CFSG.Sporadic.Schreier

theorem d2009K : orderIs cfR1 4 = true ∧ orderIs cfR2 4 = true ∧ cfS1 * cfS1 = 1 ∧
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
  repeat' apply And.intro
  all_goals decide +kernel

theorem qf2009K : schP cfQF1 = true ∧ orderV cfQF1 = 16 ∧ schP cfQF2 = true ∧
    orderV cfQF2 = 16 ∧ schP cfQF3 = true ∧ orderV cfQF3 = 16 ∧
    schP cfQRz = true ∧ orderV cfQRz = 64 := by
  repeat' apply And.intro
  all_goals decide +kernel

theorem f2009K : (cfFgens.all fun x => siftP cfQR x 0 && decide (x * cfZ = cfZ * x)) = true ∧
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
  repeat' apply And.intro
  all_goals decide +kernel

theorem qe2009K : schP cfQE = true ∧ orderV cfQE = 16 := by
  constructor <;> decide +kernel

theorem e2009K : (cfEgens.all fun x => siftP cfQR x 0 && siftP QP45 x 0) = true ∧
    (elemsV cfQE).all (fun x => decide (x * x = 1)) = true ∧ siftP cfQE cfZ 0 = true ∧
    siftP cfQE cfTau 0 = true := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide +kernel

theorem eUniq2009K : ((elemsV cfQR).filter fun x => siftP QP45 x 0).all (fun x =>
    !decide (x * x = 1) || siftP cfQE x 0 || decide ((((elemsV cfQR).filter fun x =>
      siftP QP45 x 0).filter fun y => decide (y * y = 1) && decide (y * x = x * y)).length <
        16)) = true := by
  decide +kernel

end CertificateChecks.KernelCatFacts

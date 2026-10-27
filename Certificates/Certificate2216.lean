
module


public import CFSG.Sporadic.Schreier.ONCheckSmallAuxInputs
import Certificates.Kernel.Sporadic.ON5.FinalP

public section

namespace Certificates

open CertificateChecks

open CFSG CFSG.ONSchreier CFSG.ONSchreier.Native CFSG.PSL3Four.Native in
theorem certificate2216 : (Data.T32Chain.generators.all (fun g => g.size == 32) = true ∧
      pisInv 32 Data.T32z (pinvCand 32 Data.T32z) = true ∧ Data.T32z.size = 32 ∧
      CFSG.PSL3Four.Native.enumOK 32 Data.T32Chain.generators t32Enum = true ∧ t32Enum.tabs.size = 512 ∧
      (t32Enum.tabs.filter fun x => Data.T32Chain.generators.all fun g =>
        CFSG.PSL3Four.Native.comp 32 x g == CFSG.PSL3Four.Native.comp 32 g x).toList = [idTab 32, Data.T32z]
    )
    ∧ (Data.M120Chain.generators.all (fun g => g.size == 120) = true ∧
      Data.D120Generators.all (fun g => g.size == 120) = true ∧
      Data.D120Generators.size = 4 ∧
      allBelowN 4 (fun j => pisInv 120 Data.D120Generators[j]!
        (pinvCand 120 Data.D120Generators[j]!)) = true ∧
      CFSG.PSL3Four.Native.enumOK 120 Data.M120Chain.generators m120Enum = true ∧ m120Enum.tabs.size = 40320 ∧
      (m120Enum.tabs.filter fun x => Data.D120Generators.all fun g =>
        CFSG.PSL3Four.Native.comp 120 x g == CFSG.PSL3Four.Native.comp 120 g x).size = 2 ∧
      allBelowN 4 (fun j => memFull 120
        (cLevels 120 Data.M120Chain.base (allSteps Data.M120Chain.strongGenerators
          (pinvs 120 Data.M120Chain.strongGenerators) Data.M120Chain.base))
        (allInvSteps Data.M120Chain.strongGenerators
          (pinvs 120 Data.M120Chain.strongGenerators) Data.M120Chain.base)
        Data.M120Chain.base Data.D120Generators[j]!) = true
    )
    ∧ (fixedSet 120 ((levIdx Data.PSL120Chain.strongGenerators Data.PSL120Chain.base 1).map
      fun j => Data.PSL120Chain.strongGenerators[j]!).toArray = [0]
    )
    ∧ (Data.targetFanoBlocks.size = 120 ∧
      allBelowN 120 (fun i => Data.targetFanoBlocks[i]!.size == 7 &&
        sortedOK Data.targetFanoBlocks[i]! &&
        Data.targetFanoBlocks[i]!.all (fun x => decide (x < 21))) = true ∧
      allBelowN 120 (fun i => allBelowN 120 fun k => i == k ||
        Data.targetFanoBlocks[i]!.toList != Data.targetFanoBlocks[k]!.toList) = true ∧
      Data.PSL120Chain.generators.size = 12 ∧ Data.PSL21Chain.generators.size = 12 ∧
      allBelowN 12 (fun j => allBelowN 120 fun i =>
        decide ((Data.PSL120Chain.generators[j]!)[i]! < 120) &&
          sortedImage Data.PSL21Chain.generators[j]! Data.targetFanoBlocks[i]! ==
            Data.targetFanoBlocks[(Data.PSL120Chain.generators[j]!)[i]!]!.toList) = true
    ) :=
  ⟨KernelSpor.ON5K.t32_part, KernelSpor.ON5K.m120_part_proved, KernelSpor.ON5K.psl_part,
    KernelSpor.ON5K.fano_part⟩

end Certificates

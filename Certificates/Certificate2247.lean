module

public import CFSG.Sporadic.Schreier.RuCheckBasicInputs
import Certificates.Kernel.SporSch.Ru.Basic2247
import Certificates.Kernel.SporSch.Ru.Tree2247

public section

namespace Certificates

open CertificateChecks

open CFSG CFSG.Sporadic CFSG.Sporadic.RuSchreier CFSG.Monster.B.Co2.Native CFSG.Certificates.Native in
theorem certificate2247 : (isInvA 4060 ruA0A (ruInv ruA0A) = true ∧ isInvA 4060 ruA1A (ruInv ruA1A) = true ∧
      ruCRunA.2.2 = true ∧ ruNRunA.2.2 = true ∧
      isInvA 4060 ruN0A (ruInv ruN0A) = true ∧ isInvA 4060 ruN1A (ruInv ruN1A) = true ∧
      isInvA 4060 ruC0A (ruInv ruC0A) = true ∧ isInvA 4060 ruC1A (ruInv ruC1A) = true ∧
      isInvA 4060 ruWA (ruInv ruWA) = true ∧ isInvA 4060 ruHA (ruInv ruHA) = true ∧
      isInvA 4060 ruNs0A (ruInv ruNs0A) = true ∧ isInvA 4060 ruNs1A (ruInv ruNs1A) = true ∧
      (∀ i < 4, isInvA 4060 ruSGensA[i]! (ruInv ruSGensA[i]!) = true) ∧
      ruWordsLettersOK = true
    )
    ∧ (ruLayoutOK ruBytes4060 4060 45 = true ∧ ruLayoutOK ruBytes1920 1920 41 = true ∧
      ruLayoutOK ruBytes80 80 8 = true ∧
      (∀ L < 45, isInvA 4060 (ruArr4060 L) (invCand 4060 (ruArr4060 L)) = true) ∧
      (∀ L < 41, isInvA 1920 (ruArr1920 L) (invCand 1920 (ruArr1920 L)) = true) ∧
      (∀ L < 8, isInvA 80 (ruArr80 L) (invCand 80 (ruArr80 L)) = true) ∧
      ruBytesPts.size = 3 * 10120 ∧ (∀ f < 9, ∀ i < (ruPtsOffsets.getD f (0, 0)).2,
        (ruPtList f)[i]! < 4060) ∧
      ruBytesTree.size = 6 * 593774 ∧
      ruDerivOK ruCGenCount 7 ruCDerivations = true ∧ ruDerivOK ruNGenCount 6 ruNDerivations = true ∧
      ruDerivOK ruJoinGenCount 18 ruJoinDerivations = true ∧
      ruDerivOK ruCFaithfulGenCount 7 ruCFaithfulDerivations = true ∧
      ruDerivOK ruCQuotient80GenCount 8 ruCQuotient80Derivations = true ∧
      ruDerivOK ruSGenCount 7 ruSDerivations = true ∧ ruDerivOK ruKGenCount 10 ruKDerivations = true ∧
      ruDerivOK ruJGenCount 10 ruJDerivations = true ∧ ruDerivOK ruRGenCount 7 ruRDerivations = true ∧
      (∀ k < 12, ruCSmallPartition.getD k 0 < 6) ∧ (∀ k < 28, ruNSmallPartition.getD k 0 < 7) ∧
      ruCSmallOrbit.length = 12 ∧ ruCSmallPartition.length = 12 ∧ ruNSmallOrbit.length = 28 ∧
      ruNSmallPartition.length = 28 ∧ (∀ x ∈ ruCSmallOrbit, x < 4060) ∧
      (∀ x ∈ ruNSmallOrbit, x < 4060) ∧ (∀ b ∈ ruQuotientBits, b < 8)
    ) :=
  KernelSporSch.Ru2247.facts KernelSporSch.RuTree.size

end Certificates

end

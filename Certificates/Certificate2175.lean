
module

public import Certificates.Certificate2175Base
import Certificates.Kernel.SporSch.J4S.NoCPBase

public import CFSG.Sporadic.Schreier.J4SNoCompData
public meta import CFSG.Sporadic.Schreier.J4SNoCompData
import Certificates.Kernel.SporSch.J4S.NoCP

public section

namespace Certificates

open CertificateChecks

open CFSG CFSG.Sporadic CFSG.Sporadic.J4Schreier CFSG.Sporadic.J4Schreier.NoComp in
theorem certificate2175 : (∀ l < 7,
      ((Finset.range 2048).filter fun a => CFSG.Sporadic.J4Schreier.NoComp.etaV unMats repVecs[l]! a = repVecs[l]!).card =
        repCounts[l]! ∧
      ∀ a < 2048, CFSG.Sporadic.J4Schreier.NoComp.etaV unMats repVecs[l]! a = repVecs[l]! ∨
        O.vne (CFSG.Sporadic.J4Schreier.NoComp.etaV unMats repVecs[l]! a) repVecs[l]! = true
    )
    ∧ (bilB rootBits repVecs[2]! = true ∧ bilB rootBits repVecs[3]! = false)
    ∧ (outsideOK unMats CFSG.Sporadic.J4Schreier.NoComp.conjTab = true)
    ∧ ((∀ a ∈ dList, a < 2048) ∧ (∀ a ∈ dList, ∀ b ∈ dList, a ^^^ b ∈ dList) ∧
      (∀ i < 276, ∀ i' < 276, orb14.1[i]! ^^^ 1 = orb14.1[i']! → orb14.1[i]! ∈ dList) ∧
      (∀ j < 7, 1 ≤ j → ((List.range 276).any fun i => orb14.1[i]! == chainBase[j]!) = true ∧
        ((List.range 276).any fun i => orb14.1[i]! == chainBase[j]! ^^^ 1) = true) ∧
      ∀ l < 7, 1 ≤ l → ∀ i < 276, orb14.1[i]! ∉ dSets[l]!
    )
    ∧ ((∀ e ∈ kdData, app11W e.2.2 1 = e.1 ∧ ∀ a ∈ dList,
        CFSG.Sporadic.J4Schreier.NoComp.etaV unMats repVecs[e.2.1]! (app11W e.2.2 a) = repVecs[e.2.1]!) ∧
      ∀ l ∈ [5, 6], ∀ dd ∈ dSets[l]!, (kdData.any fun e => e.1 == dd && e.2.1 == l) = true
    )
    ∧ (∀ j ∈ [1, 2, 3, 4, 5, 6], (chainWords[j - 1]!).size = chainCnt[j]! ∧
      ∀ k < chainCnt[j]!, ((chainWords[j - 1]!)[k]!).all (· < 8) = true ∧
        (∀ i < j, swApp sTab (chainWords[j - 1]!)[k]! chainBase[i]! = chainBase[i]!) ∧
        swApp sTab (chainWords[j - 1]!)[k]! chainBase[j]! < 2048 ∧
        ∀ k' < chainCnt[j]!, swApp sTab (chainWords[j - 1]!)[k]! chainBase[j]! =
          swApp sTab (chainWords[j - 1]!)[k']! chainBase[j]! → k = k'
    ) := KernelSporSch.J4NoCP.facts

end Certificates

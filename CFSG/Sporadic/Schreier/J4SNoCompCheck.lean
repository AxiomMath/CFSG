
module

public import CFSG.Sporadic.Schreier.J4SNoCompCheckBase

public import CFSG.Sporadic.Schreier.J4SNoCompData
public meta import CFSG.Sporadic.Schreier.J4SNoCompData
public import Certificates.Certificate2175

public section

namespace CFSG.Sporadic.J4Schreier.NoComp

theorem fix_check : ∀ l < 7,
    ((Finset.range 2048).filter fun a => etaV unMats repVecs[l]! a = repVecs[l]!).card =
      repCounts[l]! ∧
    ∀ a < 2048, etaV unMats repVecs[l]! a = repVecs[l]! ∨
      O.vne (etaV unMats repVecs[l]! a) repVecs[l]! = true :=
  Certificates.certificate2175.1

theorem bil_check : bilB rootBits repVecs[2]! = true ∧ bilB rootBits repVecs[3]! = false :=
  Certificates.certificate2175.2.1

theorem outside_check : outsideOK unMats conjTab = true :=
  Certificates.certificate2175.2.2.1

theorem td_check : (∀ a ∈ dList, a < 2048) ∧ (∀ a ∈ dList, ∀ b ∈ dList, a ^^^ b ∈ dList) ∧
    (∀ i < 276, ∀ i' < 276, orb14.1[i]! ^^^ 1 = orb14.1[i']! → orb14.1[i]! ∈ dList) ∧
    (∀ j < 7, 1 ≤ j → ((List.range 276).any fun i => orb14.1[i]! == chainBase[j]!) = true ∧
      ((List.range 276).any fun i => orb14.1[i]! == chainBase[j]! ^^^ 1) = true) ∧
    ∀ l < 7, 1 ≤ l → ∀ i < 276, orb14.1[i]! ∉ dSets[l]! :=
  Certificates.certificate2175.2.2.2.1

theorem kd_check : (∀ e ∈ kdData, app11W e.2.2 1 = e.1 ∧ ∀ a ∈ dList,
      etaV unMats repVecs[e.2.1]! (app11W e.2.2 a) = repVecs[e.2.1]!) ∧
    ∀ l ∈ [5, 6], ∀ dd ∈ dSets[l]!, (kdData.any fun e => e.1 == dd && e.2.1 == l) = true :=
  Certificates.certificate2175.2.2.2.2.1

theorem chain_check : ∀ j ∈ [1, 2, 3, 4, 5, 6], (chainWords[j - 1]!).size = chainCnt[j]! ∧
    ∀ k < chainCnt[j]!, ((chainWords[j - 1]!)[k]!).all (· < 8) = true ∧
      (∀ i < j, swApp sTab (chainWords[j - 1]!)[k]! chainBase[i]! = chainBase[i]!) ∧
      swApp sTab (chainWords[j - 1]!)[k]! chainBase[j]! < 2048 ∧
      ∀ k' < chainCnt[j]!, swApp sTab (chainWords[j - 1]!)[k]! chainBase[j]! =
        swApp sTab (chainWords[j - 1]!)[k']! chainBase[j]! → k = k' :=
  Certificates.certificate2175.2.2.2.2.2

end CFSG.Sporadic.J4Schreier.NoComp

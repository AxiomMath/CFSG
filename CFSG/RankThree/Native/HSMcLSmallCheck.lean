module

public import CFSG.RankThree.Native.HSMcLAuxData
public import CFSG.Sporadic.Schreier.PairHSCert
public import Certificates.Data.CFSGNative.Schreier.Check
public meta import CFSG.RankThree.Native.HSMcLAuxData
public meta import CFSG.RankThree.Native.HSMcLSmallData
public meta import CFSG.Sporadic.Schreier.PairHSCert
public meta import CFSG.Sporadic.Schreier.PairMcLCert
public meta import CFSG.Sporadic.SmallOddCore.McLData
public meta import CFSG.Monster.B.Fischer.InducedData
public meta import Certificates.Data.CFSGNative.Schreier.Check
public meta import Certificates.Data.CFSGNative.SmallOddCore.Check
public import CFSG.RankThree.Native.HSMcLSmallCheckInputs
public import Certificates.Certificate8129

public noncomputable section

namespace CFSG.RankThree.Native

open CFSG.Monster.B.Co2.Native CFSG.Certificates.Native CFSG.Sporadic.Schreier

theorem hs100_chain_check :
    rawChainOK 100 (hs100StrongArrs.extract 0 2) hs100StrongArrs hs100BaseArr hs100Words 1 =
        true ∧
      rawOrbitSizes 100 hs100StrongArrs hs100BaseArr = [100, 77, 60, 12, 8] ∧
      eqA 100 (compA 100 (hs100Arr 15) (hs100Arr 15)) (idA 100) = true ∧
      isInvA 100 (hs100Arr 15) (invCand 100 (hs100Arr 15)) = true ∧
      allLt 100 (fun x => x == 0 || (List.range 15).any fun j =>
        (hs100StrongArrs[j]!)[0]! == 0 && (hs100StrongArrs[j]!)[x]! != x) = true :=
  Certificates.certificate8129.1

theorem hs100R_chain_check :
    rawChainOK 100 (hs100RArrs.extract 0 3) hs100RArrs hs100RBaseArr hs100RWords 1 = true ∧
      rawOrbitSizes 100 hs100RArrs hs100RBaseArr = [100, 77, 16, 45, 8, 2] ∧
      eqA 100 hs100RArrs[0]! (hs100Arr 0) = true ∧ eqA 100 hs100RArrs[1]! (hs100Arr 1) = true ∧
      eqA 100 hs100RArrs[2]! (hs100Arr 15) = true :=
  Certificates.certificate8129.2.1

theorem mcl275R_chain_check :
    rawChainOK 275 (mcl275RArrs.extract 0 3) mcl275RArrs mcl275RBaseArr mcl275RWords 1 = true ∧
      rawOrbitSizes 275 mcl275RArrs mcl275RBaseArr = [275, 112, 81, 45, 16] ∧
      eqA 275 mcl275RArrs[0]! mclStrongArrs[0]! = true ∧
      eqA 275 mcl275RArrs[1]! mclStrongArrs[1]! = true ∧
      eqA 275 mcl275RArrs[2]! (CFSG.Sporadic.SmallOddCore.Native.natArr
        CFSG.Sporadic.SmallOddCore.mclOuterTbl) = true ∧
      isInvA 275 (CFSG.Sporadic.SmallOddCore.Native.natArr CFSG.Sporadic.SmallOddCore.mclOuterTbl)
        (invCand 275 (CFSG.Sporadic.SmallOddCore.Native.natArr
          CFSG.Sporadic.SmallOddCore.mclOuterTbl)) = true :=
  Certificates.certificate8129.2.2.1

@[expose] def hs100PairHas (x i : ℕ) : Bool := hs100Kappa1[x]! == i || hs100Kappa2[x]! == i

theorem hs100_kappa_check :
    allLt 3850 (fun x => decide (hs100Kappa1[x]! < hs100Kappa2[x]!) &&
        decide (hs100Kappa2[x]! < 100)) = true ∧
      hs100KappaEquiv hsStrongArrs[0]! (hs100Arr 0) = true ∧
      hs100KappaEquiv hsStrongArrs[1]! (hs100Arr 1) = true :=
  Certificates.certificate8129.2.2.2.1

theorem hs100Kappa_facts :
    Function.Injective hs100Kappa ∧ (∀ x, (hs100Kappa x).card = 2) ∧ hs100Kappa 0 = {0, 78} ∧
      ∀ i : Fin 100, (Finset.univ.filter fun x => i ∈ hs100Kappa x).card = 77 :=
  Certificates.certificate8129.2.2.2.2

end CFSG.RankThree.Native

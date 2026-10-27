module

public import CFSG.Sporadic.Co1.Module.LeechOddChecksInputs
public import Certificates.Data.Kernel.Co1Odd71
public import CFSG.Certificates.Kernel.Co1F2Sound

@[expose] public section

namespace CFSG.Sporadic.Co1.Module.Odd

open CFSG.Sporadic.SmallF2.Native CFSG.Sporadic.Co1.OddNative CFSG.KD.Co1Odd CFSG.KC.Co1F2
  CFSG.KC.M1F2

def zOneLitOK : Prop :=
  (zIdx[1]!).map rr = Z1G.map (unpackR 24) ∧ treeOK71 Z1G Z1P Z1Par Z1Lab 1344 = true ∧
    distinctL Z1P = true ∧ canonL Z1P = true ∧ noConjOK Z1P Z1W = true

def zTwoLitOK : Prop :=
  (zIdx[2]!).map rr = Z2G.map (unpackR 24) ∧ treeOK71 Z2G Z2P Z2Par Z2Lab 96 = true ∧
    distinctL Z2P = true ∧ canonL Z2P = true

noncomputable def orbitYLitOK : Bool := orbitOK (Z2P.map (unpackR 24)) yList

noncomputable def outerLitOK : Bool :=
  (List.range Z2P.length).all fun i => Z2P.getD i 0 == idF 24 || !invK (Z2P.getD i 0) ||
    rankOK (Z2P.getD i 0) (Z2W.getD i []) ||
      (decide ((Z2W.getD i []).getD 0 0 < 2 ^ 24) &&
        outerTest (unpackR 24 (Z2P.getD i 0)) ((Z2W.getD i []).getD 0 0))

end CFSG.Sporadic.Co1.Module.Odd

end

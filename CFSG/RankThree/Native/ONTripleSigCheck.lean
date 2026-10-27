module

public import Certificates.Certificate8146

public section

namespace CFSG.RankThree.Native.ONTriple

theorem sig_check :
    (∀ j < 2, ∀ l < 4, eM ((rL.getD j []).getD l 0) =
      (((lineWords.getD j []).getD l []).map fun k => eM (if k = 0 then rN1 else rN2)).prod) ∧
    (∀ j < 2, ∀ m < 3, ∀ i < 3,
      eM (vRegI j m i) * eM (rX.getD 0 0) = eM (rX.getD 0 0) * eM (vRegI j m i)) ∧
    (MapsB (eM rY1) (sYList.getD 0 []) ∧ MapsB (eM rY3) (sYList.getD 1 [])) ∧
    eM rX12 = eM (rX.getD 1 0) * eM (rX.getD 2 0) :=
  Certificates.certificate8146

end CFSG.RankThree.Native.ONTriple

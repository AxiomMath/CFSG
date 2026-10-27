module

public import Certificates.Certificate8137

public section

namespace CFSG.RankThree.Native.ONTriple

theorem aut_check :
    (∀ k : Fin 8, gM k ∈ Subgroup.closure (Set.range fun i : Fin 9 => eM (yRegs.getD i.val 0))) ∧
    (let t := ([0, 1, 1].map fun k => eM (if k = 0 then rN1 else rN2)).prod ^ 3;
      t * eM (rX.getD 0 0) = eM (rX.getD 0 0) * t ∧ t ^ 4 = 1 ∧ MapsB t [3, 4, 5, 2, 1, 0]) ∧
    (∀ i < 3, eM (rC.getD i 0) * eM (rX.getD 0 0) = eM (rX.getD 0 0) * eM (rC.getD i 0)) ∧
    eM rK1 = (eM (rC.getD 0 0))⁻¹ * (eM (rC.getD 1 0))⁻¹ * eM (rC.getD 0 0) * eM (rC.getD 1 0) ∧
    eM rK2 = (eM (rC.getD 0 0))⁻¹ * (eM (rC.getD 2 0))⁻¹ * eM (rC.getD 0 0) * eM (rC.getD 2 0) :=
  Certificates.certificate8137

end CFSG.RankThree.Native.ONTriple

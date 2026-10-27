module

public import CFSG.RankThree.Native.ONTripleMatSound
public import CFSG.RankThree.Native.ONTripleAutCheckInputs
import Certificates.Kernel.Misc.ON.AutFacts

public section

namespace Certificates

open CertificateChecks

open CertificateChecks.KernelMisc.ON

open CFSG CFSG.RankThree CFSG.RankThree.Native CFSG.RankThree.Native.ONTriple in
theorem certificate8137 :
    (∀ k : Fin 8, gM k ∈ Subgroup.closure (Set.range fun i : Fin 9 => eM (yRegs.getD i.val 0))) ∧
    (let t := ([0, 1, 1].map fun k => eM (if k = 0 then rN1 else rN2)).prod ^ 3;
      t * eM (rX.getD 0 0) = eM (rX.getD 0 0) * t ∧ t ^ 4 = 1 ∧ MapsB t [3, 4, 5, 2, 1, 0]) ∧
    (∀ i < 3, eM (rC.getD i 0) * eM (rX.getD 0 0) = eM (rX.getD 0 0) * eM (rC.getD i 0)) ∧
    eM rK1 = (eM (rC.getD 0 0))⁻¹ * (eM (rC.getD 1 0))⁻¹ * eM (rC.getD 0 0) * eM (rC.getD 1 0) ∧
    eM rK2 = (eM (rC.getD 0 0))⁻¹ * (eM (rC.getD 2 0))⁻¹ * eM (rC.getD 0 0) * eM (rC.getD 2 0) :=
  ⟨gM_mem_closureY, t4_factsK, c_factsK⟩

end Certificates

module

public import Certificates.Data.AE6CertE
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3A6SEdge
import Certificates.Kernel.AE6CertE.Final
import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3A6EdgeRels

public section

namespace Certificates

open CertificateChecks

open Certificates.AE6CertE Certificates.AE6Model
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3 in
theorem certificate517611 :
    (∀ p ∈ ([([0, 2, 4, 6], 4096), ([0, 2, 3, 4, 5, 6, 7], 1290240),
        ([0, 1, 2, 3, 4, 5, 6], 1290240), ([0, 1, 2, 3, 4, 6, 7], 1290240), ([0, 1, 2, 4, 6], 12288),
        ([0, 2, 3, 4, 6], 12288), ([0, 2, 4, 5, 6], 12288), ([0, 2, 4, 6, 7], 12288),
        ([0, 2, 4, 5, 6, 7], 36864), ([0, 1, 2, 4, 5, 6], 36864), ([0, 1, 2, 4, 6, 7], 36864)] :
        List (List ℕ × ℕ)),
      Nat.card (Subgroup.closure {g | g ∈ eGens p.1}) = p.2) ∧
    (∀ k < 3, ∀ j < 315, ∀ x < 8, x ≠ eOmit.getD k 0 → ∃ j' < 315,
      aeWord (curtisPerms ()) (eWordOf k j) * (curtisPerms ()).getD x 1 *
        (aeWord (curtisPerms ()) (eWordOf k j'))⁻¹ ∈ Subgroup.closure {g | g ∈ eGens [0, 2, 4, 6]}) ∧
    (∀ k < 3, ∀ j < 315, ∀ i ∈ eWordOf k j, (curtisPerms ()).getD i 1 ∈
      Subgroup.closure {g | g ∈ eGens [0, 2, 4, 6]} ⊔
        Subgroup.zpowers (aeWord (curtisPerms ()) (eWordOf k j))) ∧
    ∀ k, ∀ r ∈ A6.curtisRels,
      A6.curtisEval (List.ofFn fun i => A6.curtisGen (A6S.ae6EdgeSwap k i)) r = 1 :=
  ⟨KernelAE6CertE.e517611_orders, KernelAE6CertE.e517611_graph, KernelAE6CertE.e517611_letters,
    fun k => CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3.A6S.curtisRels_edgeSwap k⟩

end Certificates

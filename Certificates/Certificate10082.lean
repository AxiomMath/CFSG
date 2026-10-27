module

public import Certificates.Data.CFSGNative.Co2Smith.Pin
import Certificates.Kernel.Co2SmithS.Seeds
import Certificates.Kernel.Co2SmithS.PinK
import CFSG.Certificates.Kernel.Co2SmithS.PinSound
public import CFSG.Sporadic.Co2Smith.CheckInputs

public section

open CFSG.Sporadic.Co2Smith

namespace CertificateChecks.KernelCo2SmithS

open CFSG.KC.Co1F2 CFSG.KC.Co2InvS CFSG.KC.Co2SmithS CFSG.Sporadic.Co2Smith.Native
  CFSG.Sporadic.SmallF2.Native

private theorem frameNe_ok : frameNeOK seedRowsArr = true := by
  have h := frame0_ok
  simp only [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h
  have e : (fRows seedRowsArr)[0]! = mRows seedRowsArr frameWords[0]! := by
    unfold fRows
    rw [getElem!_pos _ 0 (by simp [frameWords]), getElem!_pos frameWords 0 (by simp [frameWords])]
    simp
  unfold frameNeOK
  rw [e, mRows_eq h.1, idRows_eq, bne, unpack_beq (wK_lt _ _) IDP_lt]
  exact h.2

private theorem sr_ok :(List.range 8).all (fun k => (stdRows ())[k]! == unpackR 8 (SR k)) = true := by
  decide +kernel

private theorem pin_bounds :pinRels.all (fun r => r.1.all (· < 8)) = true := by decide +kernel

private theorem pinUnique_ok :pinUniqueOK () = true := by
  have hS := sr_ok
  have hb := pin_bounds
  simp only [List.all_eq_true, List.mem_range, beq_iff_eq, decide_eq_true_eq] at hS hb
  exact pinUniqueOK_of hS hb pin_ok

end CertificateChecks.KernelCo2SmithS

namespace Certificates

open CertificateChecks

open CFSG.Sporadic.Co2Smith in
theorem certificate10082 :
    (Native.frameNeOK seedRowsArr = true)
    ∧ (Native.pinUniqueOK = true) :=
  ⟨KernelCo2SmithS.frameNe_ok, KernelCo2SmithS.pinUnique_ok⟩

end Certificates

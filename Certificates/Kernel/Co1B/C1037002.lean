module

public import Certificates.Kernel.Co1B.Chk1037002
public import Certificates.Kernel.Co1B.C129071

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelCo1B.C1037002

open CFSG.KS.SporSch.M24 CFSG.KS.Raw CFSG.Sporadic.Co1Schreier.Native CFSG.Sporadic.Co1Block
  CFSG.HardMathSupport.Cooperstein.Coordinator.FFSporadic CertificateChecks.KernelCo1B.C129070

@[expose] noncomputable def LB : List Rows := (List.range BC.N).map fun i => unpack 24 24 (BC.M i)

@[expose] noncomputable def LBI : List Rows :=
  (List.range BC.N).map fun i => unpack 24 24 (BC.MI i)

theorem hb : (Nat.beq (BC.M 0) CFSG.KD.Co1B.SA && Nat.beq (BC.M 1) CFSG.KD.Co1B.SB &&
    Nat.beq (BC.M 2) C1037002.IA) = true ∧ BC.N = 551 := by
  have h := C1037002.kb
  rw [Bool.and_eq_true] at h
  exact ⟨h.1, Nat.eq_of_beq_eq_true h.2⟩

theorem hD : dag [aR, bR, iotaARows] (dispHeis ++ dispBC) = (LB, LBI, true) := by
  have h := dagWK_sound (base3 C129071.iotaA_u' hb.1) kD
  rwa [decWords_encWordK] at h

theorem iotaC_u : iotaCRows = unpack 24 24 C1037002.IC := C129071.iotaC_u

theorem gB {i : Nat} (hi : i < 551) : LB.getD i (one ()) = unpack 24 24 (BC.M i) :=
  getD_range_unpack (by rw [hb.2]; exact hi)

open Certificates in
open CFSG.HardMathSupport.Cooperstein.Coordinator.FFSporadic in
theorem c1037002 : dispBCCheck () = true := by
  unfold dispBCCheck
  simp only [hD, Bool.true_and, dispIXB, dispIYB, dispIXC, dispIYC]
  rw [gB (by decide : 547 < 551), gB (by decide : 548 < 551), gB (by decide : 549 < 551),
    gB (by decide : 550 < 551), aR_u', iotaC_u, heisK_sound kHB, heisK_sound kHC, Bool.and_self]

end CertificateChecks.KernelCo1B.C1037002

end

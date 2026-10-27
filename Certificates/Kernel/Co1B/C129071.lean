module

public import CFSG.HardMathSupport.Cooperstein.Coordinator.FFSporadic.Co1DispCheck
public meta import CFSG.Sporadic.Co1Block.TwoAData
public meta import CFSG.Sporadic.Co1Block.IotaData
public meta import CFSG.Sporadic.Co1Block.Iota
public meta import CFSG.Sporadic.Co1Block.CentCheck
public meta import CFSG.Sporadic.Schreier.Co1ChainCheck
public meta import CFSG.Sporadic.Schreier.Co1StabCheck
public meta import CFSG.Sporadic.Schreier.Co1ThreeLocal
public meta import CFSG.Sporadic.Schreier.Co1StabData
public meta import Certificates.Data.CFSGNative.Co1Schreier.Base
public meta import Certificates.Data.CFSGNative.Co1.Data
public meta import Certificates.Data.CFSGNative.Co1.Involutions
public meta import Certificates.Data.CFSGNative.Co1.TwoB
public meta import Certificates.Data.CFSGNative.HS.SmallF2
public import Certificates.Kernel.Co1B.Chk129071
public import Certificates.Kernel.Co1B.C129070

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelCo1B.C129071

open CFSG.KS.SporSch.M24 CFSG.KS.Raw CFSG.Sporadic.Co1Schreier.Native CFSG.Sporadic.Co1Block
  CFSG.HardMathSupport.Cooperstein.Coordinator.FFSporadic CertificateChecks.KernelCo1B.C129070

theorem iotaC_u : iotaCRows = unpack 24 24 IC :=
  CertificateChecks.KernelCo1B.iotaC_eq.trans (unpackR_eq_unpack _)

@[expose] noncomputable def LH : List Rows := (List.range H.N).map fun i => unpack 24 24 (H.M i)

@[expose] noncomputable def LHI : List Rows := (List.range H.N).map fun i => unpack 24 24 (H.MI i)

@[expose] noncomputable def LC : List Rows := (List.range C.N).map fun i => unpack 24 24 (C.M i)

@[expose] noncomputable def LCI : List Rows := (List.range C.N).map fun i => unpack 24 24 (C.MI i)

theorem hH : (Nat.beq (H.M 0) CFSG.KD.Co1B.SA && Nat.beq (H.M 1) CFSG.KD.Co1B.SB &&
    Nat.beq (H.M 2) C129071.IA) = true ∧ H.N = 391 := by
  have h := kbH
  rw [Bool.and_eq_true] at h
  exact ⟨h.1, Nat.eq_of_beq_eq_true h.2⟩

theorem hC : (Nat.beq (C.M 0) CFSG.KD.Co1B.SA && Nat.beq (C.M 1) CFSG.KD.Co1B.SB &&
    Nat.beq (C.M 2) IC) = true ∧ C.N = 5 := by
  have h := kbC
  rw [Bool.and_eq_true] at h
  exact ⟨h.1, Nat.eq_of_beq_eq_true h.2⟩

theorem iotaA_u' : iotaARows = unpack 24 24 C129071.IA := C129070.iotaA_u

theorem hDH : dag [aR, bR, iotaARows] dispHeis = (LH, LHI, true) := by
  have h := dagWK_sound (base3 iotaA_u' hH.1) kDH
  rwa [decWords_encWordK] at h

theorem hDC : dag [aR, bR, iotaCRows] dispDihD = (LC, LCI, true) := by
  have h := dagWK_sound (base3 iotaC_u hC.1) kDC
  rwa [decWords_encWordK] at h

theorem gH {i : Nat} (hi : i < 391) : LH.getD i (one ()) = unpack 24 24 (H.M i) :=
  getD_range_unpack (by rw [hH.2]; exact hi)

theorem gC {i : Nat} (hi : i < 5) : LC.getD i (one ()) = unpack 24 24 (C.M i) :=
  getD_range_unpack (by rw [hC.2]; exact hi)

open Certificates in
open CFSG.HardMathSupport.Cooperstein.Coordinator.FFSporadic in
theorem c129071 : dispCheck () = true := by
  obtain ⟨c1, c2, c3, c4⟩ := dihK_sound kDihC
  obtain ⟨a1, a2, a3, a4⟩ := dihK_sound kDihA
  unfold dispCheck dispHeisCheck dispDihCheck
  simp only [hDH, hDC, Bool.true_and, dispIX, dispIY, dispIC, dispIA1]
  rw [gH (by decide : 389 < 391), gH (by decide : 390 < 391), gC (by decide : 3 < 5),
    gC (by decide : 4 < 5), iotaA_u', iotaC_u, aR_u', Bool.and_eq_true]
  refine ⟨heisK_sound kHeis, ?_⟩
  simp only [c1, c2, c3, c4, a1, a2, a3, a4, Bool.and_self]

end CertificateChecks.KernelCo1B.C129071

end

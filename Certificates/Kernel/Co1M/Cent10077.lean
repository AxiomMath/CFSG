
module

public import Certificates.Kernel.Co1M.Base10077
public import Certificates.Kernel.Co1Cover.Bridge
public import Certificates.Kernel.Co1B.C2046
public import CFSG.Sporadic.Co1.Module.TwoBDataInputs
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Sporadic.Co1.Module.TwoBTree

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelCo1M

open CFSG.KC.Co1M CFSG.KD.Co1M CFSG.KC.Co1F2 CFSG.Sporadic.Co1.Module.TwoB
  CFSG.Sporadic.SmallF2.Native

theorem c77_prog : progK 24 RB77 progB 3 = true := by quickRfl

theorem c77_regs : regsRowsB = (RB77.map (unpackR 24)).toArray := by
  rw [regsRowsB, initRowsB, CertificateChecks.KernelCo1Cover.rowsA_eq,
    CertificateChecks.KernelCo1Cover.rowsB_eq, CertificateChecks.KernelCo1B.rowsSB_eq,
    ← prog_sound c77_prog]
  rfl

theorem c77_rrB (i : Nat) : rrB i = (RB77.map (unpackR 24)).toArray[i]?.getD (idRows 24) := by
  rw [rrB, c77_regs]

theorem c77_A : ((yIdx ++ sIdx ++ eIdx).all fun i =>
    mulRows 24 (rrB i) CFSG.Sporadic.Co1.Module.rowsSB == mulRows 24 CFSG.Sporadic.Co1.Module.rowsSB (rrB i)) =
      true := by
  simp only [c77_rrB, CertificateChecks.KernelCo1B.rowsSB_eq]
  quickRfl

theorem c77_B : ((sIdx ++ eIdx).all fun i =>
    CFSG.Sporadic.Co1.InvNative.isFixedN (transposeRows 24 (rrB i)) CFSG.Sporadic.Co1.Module.code4) = true := by
  simp only [c77_rrB]
  quickRfl

theorem c77_valid (i : Nat) : CFSG.Sporadic.Co1.InvNative.validRows (rrB i) = true := by
  rw [c77_rrB]
  cases h : (RB77.map (unpackR 24)).toArray[i]? with
  | none =>
    rw [Option.getD_none, CertificateChecks.KernelCo1B.idRows_eq]
    exact validRows_unpackR _
  | some a =>
    rw [Option.getD_some]
    obtain ⟨x, -, rfl⟩ := List.mem_map.1 (List.mem_toArray.1 (Array.mem_of_getElem? h))
    exact validRows_unpackR x

theorem c77_C : ((yIdx ++ sIdx ++ eIdx ++ [43]).all fun i =>
    CFSG.Sporadic.Co1.InvNative.validRows (rrB i)) = true :=
  List.all_eq_true.2 fun i _ => c77_valid i

theorem c77_D : (mulRows 24 (rrB gIdx) (rrB 43) == idRows 24) = true := by
  simp only [c77_rrB]
  quickRfl

theorem c77_E : CFSG.Sporadic.Co1.InvNative.orderIs (rrB 40) 3 = true := by
  simp only [c77_rrB]
  quickRfl

theorem c77_F : CFSG.Sporadic.Co1.InvNative.orderIs (rrB 42) 5 = true := by
  simp only [c77_rrB]
  quickRfl

theorem c77_centB : centB = true := by
  unfold centB
  rw [c77_A, c77_B, c77_C, c77_D, c77_E, c77_F]
  rfl

end CertificateChecks.KernelCo1M

end

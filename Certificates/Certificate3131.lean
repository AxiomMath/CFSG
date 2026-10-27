
module

public import Certificates.Certificate3131Base

public import CFSG.Monster.B.GSide.MuFourOmegaInputs
public import CFSG.Monster.B.GSide.MuFourGeneric
public import Certificates.Data.CFSGNative.MonsterB.Short
public import Certificates.Data.CFSGNative.Mathieu.M24
public import CFSG.Certificates.Kernel.AxisPlane.Orbit
public import Certificates.Data.Kernel.VisFrame.Gens
public import Certificates.Data.CFSGNative.MonsterB.Co2Chain
public import Certificates.Data.CFSGNative.MonsterB.Co2Matrix
public import CFSG.Monster.B.TwoA.Unitary.OrbitInputs
public import CFSG.Monster.B.TwoA.Unitary.WStabInputs
public import CFSG.Monster.B.TwoA.Unitary.Stab891Inputs
public import CFSG.Monster.B.TwoA.Unitary.Orbit1408Inputs
public import CFSG.Monster.B.TwoA.Unitary.Bridge
public import CFSG.Monster.B.TwoA.Unitary.ActionInputs
public import Certificates.Kernel.MonsterB.Co2Mem
public import CFSG.Certificates.Kernel.MonsterB.U6OrbSound
import CFSG.Certificates.Kernel.Common.Harness

public section

open CFSG.Monster.B CFSG.Monster.B.GSide CFSG.KC.Co2Mem CFSG.KLie.CT CertificateChecks.KernelMonB

namespace CertificateChecks.Batch3131

open CFSG.Monster.B CFSG.Monster.B.GSide CFSG.KC.Co2Mem CFSG.KLie.CT CertificateChecks.KernelMonB

set_option maxRecDepth 100000

theorem k24606 : memK 2300 24 (Co2V.F 0) 24606 = true := by quickRfl

theorem kBound : allN 2300 (fun t => Nat.blt (vecF t) (pw2 22)) = true := by quickRfl

theorem vectors_all_lt : Co2.Native.vectors.all (fun x => decide (x < 2 ^ 22)) = true := by
  rw [vectors_all_iff]
  intro t ht
  have h := (CFSG.KC.U6Orb.allN_iff _ _).1 kBound t ht
  rw [Nat.blt_eq, CFSG.KC.U6Orb.pw2_eq] at h
  exact decide_eq_true h

end CertificateChecks.Batch3131

namespace Certificates

open CertificateChecks.Batch3131 in
open CFSG.Monster.B CFSG.Monster.B.GSide in

theorem certificate3131 : (Co2.Native.vectors.all (fun x => decide (x < 2 ^ 22)) = true)
    ∧ (Co2.Native.vectors.contains 24606 = true)
    ∧ (Co2.Native.vectors.contains 2652785 = true)
    ∧ (bWcode 24606 2652785 ≠ 0) :=
  ⟨vectors_all_lt, (vectors_contains_eq _).trans k24606,
    (vectors_contains_eq _).trans k2652785, bW_q₁_q₂⟩

end Certificates

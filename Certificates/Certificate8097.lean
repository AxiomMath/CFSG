module

public import Certificates.Data.TripleCoverLift.Co3
public import Certificates.Data.TripleCoverLift.Co2
public import Certificates.Data.TripleCoverLift.Th
public import Certificates.Data.CFSGNative.SectionRank.F2
import CFSG.Certificates.Kernel.OpsV4Sound
import CFSG.Certificates.Kernel.OpsKSound
import Certificates.Kernel.Census.LiftF2
import all CFSG.Blueprint.NativeSporadic

public section

set_option maxRecDepth 400000

namespace CertificateChecks.Batch8097

open CFSG.RankThree.PartTwo.Sec4.Census CFSG.SectionRank.Native CFSG.KC.OpsK CFSG.KC.OpsV4
  CFSG.Blueprint CertificateChecks.KernelCensus.LiftF2

private theorem dec {d M : Nat} {cs : List Char} {s : String} (e : s = String.ofList cs)
    (h : CFSG.KC.M1F2.m1Bind cs d M = true) :
    (ops2 d).decode s = CFSG.KC.Co1F2.unpackR d M := by
  rw [e]
  exact CFSG.KC.Co1F2.bind_sound h

private theorem co3 : LiftData.check (ops2 22) co3Lift = true :=
  liftCheck_of_N (hom2 22 (by norm_num)) (A := KernelAM.C3A.M) (B := KernelAM.C3B.M)
    (D := co3Lift)
    (dec ((rfl : co3Lift.base.seedA = NativeSporadic.Co3Seed1).trans KernelAM.C3A.eq)
      KernelAM.C3A.bind)
    (dec ((rfl : co3Lift.base.seedB = NativeSporadic.Co3Seed2).trans KernelAM.C3B.eq)
      KernelAM.C3B.bind)
    trivial trivial co3_K

private theorem co2 : LiftData.check (ops2 22) co2Lift = true :=
  liftCheck_of_N (hom2 22 (by norm_num)) (A := KernelAM.C2A.M) (B := KernelAM.C2B.M)
    (D := co2Lift)
    (dec ((rfl : co2Lift.base.seedA = NativeSporadic.Co2Seed1).trans KernelAM.C2A.eq)
      KernelAM.C2A.bind)
    (dec ((rfl : co2Lift.base.seedB = NativeSporadic.Co2Seed2).trans KernelAM.C2B.eq)
      KernelAM.C2B.bind)
    trivial trivial co2_K

private theorem th : LiftData.check (ops2 248) thLift = true :=
  liftCheck_of_N (hom2 248 (by norm_num)) (A := KernelLC.ThA.M) (B := KernelLC.ThB.M)
    (D := thLift)
    (dec ((rfl : thLift.base.seedA = KernelLC.thSeedA).trans KernelLC.ThA.eq) KernelLC.ThA.bind)
    (dec ((rfl : thLift.base.seedB = KernelLC.thSeedB).trans KernelLC.ThB.eq) KernelLC.ThB.bind)
    trivial trivial th_K

end CertificateChecks.Batch8097

namespace Certificates

open CertificateChecks

open CFSG.RankThree.PartTwo.Sec4.Census CFSG.SectionRank.Native in
theorem certificate8097 : LiftData.check (ops2 22) co3Lift = true ∧ LiftData.check (ops2 22) co2Lift = true ∧
    LiftData.check (ops2 248) thLift = true :=
  ⟨CertificateChecks.Batch8097.co3, CertificateChecks.Batch8097.co2, CertificateChecks.Batch8097.th⟩

end Certificates

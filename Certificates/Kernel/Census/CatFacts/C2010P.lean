module

public import Certificates.Kernel.Sporadic.RawGen
public import Certificates.Kernel.SporSch.GenPerms
public import Certificates.Kernel.LocalQT.He4148.Glue
public import Certificates.Data.Kernel.SporSch.MathieuOC
public import Certificates.Data.Kernel.Spor.Prim
public import CFSG.Sporadic.HeldB.InnerData
public import CFSG.Sporadic.HeldB.OuterCentAux
public meta import Certificates.Kernel.SporSch.Mathieu.Gen
public meta import CFSG.Sporadic.HeldB.InnerData
public meta import CFSG.Sporadic.HeldB.OuterCentAux
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Certificates.Kernel.BfsPinSound
public import CFSG.Certificates.Kernel.BfsPinUnpack
public import CFSG.Sporadic.HeldB.OuterCentData
public meta import CFSG.Sporadic.HeldB.OuterCentData
public import Certificates.Kernel.SporSch.Mathieu.Gen
public meta import Mathlib
public import Mathlib

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelCatFacts.C2010P

open CFSG.KS.SporSch.MOCG CFSG.Sporadic.HeldB

@[expose] def wY0 : List (List Int) :=
  [[2, 2, 1, 1], [1, 2, 2, 1, 1, 2, 1, 2], [2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 2]]

@[expose] def wYu : List (List Int) := [[1, 2, 1, 2], [1, 2, 2, 2]]

meta def sig0M : Array (Array Nat) := heInnerSigma0.toArray

meta def sig0IM : Array (Array Nat) := sig0M.map invA

meta def sigUM : Array (Array Nat) := #[heSigma1, heSigma2]

meta def sigUIM : Array (Array Nat) := sigUM.map invA

meta def SA : Array (Array Nat) :=
  strongOf 240 #[evalW 240 sig0M [4, 9, 5, 2], evalW 240 sig0M [7, 5, 2, 8, 5, 6]]
    [[2, 2, 1, 1], [1, 2, 2, 1, 1, 2, 1, 2], [2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 2]]

meta def baseA : Array Nat := #[0, 1, 2]

meta def SB : Array (Array Nat) :=
  strongOf 98 #[evalW 98 sigUM [2, 1, 2, 1, 1, 2, 1], evalW 98 sigUM [2, 1, 1, 2, 1, 2, 1]]
    [[1, 2, 1, 2], [1, 2, 2, 2]]

meta def baseB : Array Nat := #[0, 8]

end CertificateChecks.KernelCatFacts.C2010P

#ks_rawchain CertificateChecks.KernelCatFacts.C2010P.QA 240 8 16
  CertificateChecks.KernelCatFacts.C2010P.SA CertificateChecks.KernelCatFacts.C2010P.baseA 2
  CertificateChecks.KernelCatFacts.C2010P.wY0

#ks_rawchain CertificateChecks.KernelCatFacts.C2010P.QB 98 7 16
  CertificateChecks.KernelCatFacts.C2010P.SB CertificateChecks.KernelCatFacts.C2010P.baseB 2
  CertificateChecks.KernelCatFacts.C2010P.wYu

#kss_perms CertificateChecks.KernelCatFacts.C2010P.SG 8 CertificateChecks.KernelCatFacts.C2010P.sig0M
#kss_perms CertificateChecks.KernelCatFacts.C2010P.SGI 8
  CertificateChecks.KernelCatFacts.C2010P.sig0IM
#kss_perms CertificateChecks.KernelCatFacts.C2010P.SU 7 CertificateChecks.KernelCatFacts.C2010P.sigUM
#kss_perms CertificateChecks.KernelCatFacts.C2010P.SUI 7
  CertificateChecks.KernelCatFacts.C2010P.sigUIM

namespace CertificateChecks.KernelCatFacts.C2010P

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.M11 CFSG.KS.SporSch.MOC
  CertificateChecks.KernelLQT.He4148 CFSG.Sporadic.HeldB

local notation "pa" => pcomp 240 8 (mask 8)

local notation "pb" => pcomp 98 7 (mask 7)

theorem bSG : bindsK 240 8 SG SGI heInnerSigma0 0 = true := by decide +kernel

theorem bSU : bindsK 98 7 SU SUI [heSigma1, heSigma2] 0 = true := by decide +kernel

theorem szA : szOK 240 8 = true := by decide +kernel

theorem szB : szOK 98 7 = true := by decide +kernel

theorem eA0 : canonK 240 8 (mask 8) (240 * 8) (pa (SG 3) (SG 8)) = true ∧
    canonK 240 8 (mask 8) (240 * 8) (pa (pa (SG 3) (SG 8)) (SG 4)) = true ∧
    Nat.beq (pa (pa (pa (SG 3) (SG 8)) (SG 4)) (SG 1)) (QA.S 0) = true ∧
    canonK 240 8 (mask 8) (240 * 8) (QA.S 0) = true := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide +kernel

theorem eA1 : canonK 240 8 (mask 8) (240 * 8) (pa (SG 6) (SG 4)) = true ∧
    canonK 240 8 (mask 8) (240 * 8) (pa (pa (SG 6) (SG 4)) (SG 1)) = true ∧
    canonK 240 8 (mask 8) (240 * 8) (pa (pa (pa (SG 6) (SG 4)) (SG 1)) (SG 7)) = true ∧
    canonK 240 8 (mask 8) (240 * 8) (pa (pa (pa (pa (SG 6) (SG 4)) (SG 1)) (SG 7)) (SG 4)) =
      true ∧
    Nat.beq (pa (pa (pa (pa (pa (SG 6) (SG 4)) (SG 1)) (SG 7)) (SG 4)) (SG 5)) (QA.S 1) = true ∧
    canonK 240 8 (mask 8) (240 * 8) (QA.S 1) = true := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

theorem eB0 : canonK 98 7 (mask 7) (98 * 7) (pb (SU 1) (SU 0)) = true ∧
    canonK 98 7 (mask 7) (98 * 7) (pb (pb (SU 1) (SU 0)) (SU 1)) = true ∧
    canonK 98 7 (mask 7) (98 * 7) (pb (pb (pb (SU 1) (SU 0)) (SU 1)) (SU 0)) = true ∧
    canonK 98 7 (mask 7) (98 * 7) (pb (pb (pb (pb (SU 1) (SU 0)) (SU 1)) (SU 0)) (SU 0)) = true ∧
    canonK 98 7 (mask 7) (98 * 7)
      (pb (pb (pb (pb (pb (SU 1) (SU 0)) (SU 1)) (SU 0)) (SU 0)) (SU 1)) = true ∧
    Nat.beq (pb (pb (pb (pb (pb (pb (SU 1) (SU 0)) (SU 1)) (SU 0)) (SU 0)) (SU 1)) (SU 0))
      (QB.S 0) = true ∧
    canonK 98 7 (mask 7) (98 * 7) (QB.S 0) = true := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

theorem eB1 : canonK 98 7 (mask 7) (98 * 7) (pb (SU 1) (SU 0)) = true ∧
    canonK 98 7 (mask 7) (98 * 7) (pb (pb (SU 1) (SU 0)) (SU 0)) = true ∧
    canonK 98 7 (mask 7) (98 * 7) (pb (pb (pb (SU 1) (SU 0)) (SU 0)) (SU 1)) = true ∧
    canonK 98 7 (mask 7) (98 * 7) (pb (pb (pb (pb (SU 1) (SU 0)) (SU 0)) (SU 1)) (SU 0)) = true ∧
    canonK 98 7 (mask 7) (98 * 7)
      (pb (pb (pb (pb (pb (SU 1) (SU 0)) (SU 0)) (SU 1)) (SU 0)) (SU 1)) = true ∧
    Nat.beq (pb (pb (pb (pb (pb (pb (SU 1) (SU 0)) (SU 0)) (SU 1)) (SU 0)) (SU 1)) (SU 0))
      (QB.S 1) = true ∧
    canonK 98 7 (mask 7) (98 * 7) (QB.S 1) = true := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

theorem oY : ordIs 240 8 (mask 8) (pidn 240 8) (QA.S 0) 4 = true ∧
    ordIs 240 8 (mask 8) (pidn 240 8) (QA.S 1) 4 = true ∧
    ordIs 98 7 (mask 7) (pidn 98 7) (QB.S 0) 4 = true ∧
    ordIs 98 7 (mask 7) (pidn 98 7) (QB.S 1) 4 = true := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide +kernel

theorem oQ : Nat.beq (ordK QA.LR 3) 40320 = true ∧ Nat.beq (ordK QB.LR 2) 1080 = true := by
  constructor <;> decide +kernel

theorem neg : Nat.beq (ordK QB.LR 2) 2160 = false ∧
    ordIs 98 7 (mask 7) (pidn 98 7) (QB.S 0) 9 = false ∧
    Nat.beq (pa (pa (pa (SG 3) (SG 4)) (SG 8)) (SG 1)) (QA.S 0) = false ∧
    bindsK 98 7 SU SUI [heSigma2, heSigma1] 0 = false := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide +kernel

end CertificateChecks.KernelCatFacts.C2010P

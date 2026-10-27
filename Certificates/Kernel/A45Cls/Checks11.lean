module

public import Certificates.Kernel.A45Cls.Checks5
public import Certificates.Kernel.A45Cls.Grp6
public import Certificates.Kernel.OmegaCY.Grp
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 400000
set_option maxHeartbeats 0

public section

namespace CertificateChecks.KernelA45

open CFSG.KC.Enum CFSG.KS CFSG.KC.OrbFind CFSG.KC.A45Cls CFSG.Certificates.Kernel.PkCV

@[expose] noncomputable def splLn (W b p : ℕ) : ℕ := (W >>> (b * p)) &&& (2 ^ b - 1)

@[expose] noncomputable def splEP (E d : ℕ) : ℕ := B0Z.T (splLn E 4 d)

@[expose] noncomputable def splNormK (G : ℕ → ℕ) : Bool :=
  allN 4 fun k => nrmP 45 6 16 16 B0Z.T B0Z.T (G k)

@[expose] noncomputable def splMeetK (N : ℕ) (T : ℕ → ℕ) : Bool :=
  allN N fun i => !inPts 45 6 16 B0Z.T (T i) || isIdK 45 6 (T i)

@[expose] noncomputable def splClsK (E f : ℕ) : Bool :=
  eqP 45 6 (splEP E 0) zP &&
    (allN 5 fun d => Nat.blt (splLn E 4 d) 16 && Nat.beq (fixK 45 6 (splEP E d)) f) &&
    (allN 16 fun i => !Nat.beq (fixK 45 6 (B0Z.T i)) f || exN 5 fun d => Nat.beq i (splLn E 4 d)) &&
    (allN 5 fun d => allN 5 fun d' => Nat.beq d d' || !eqP 45 6 (splEP E d) (splEP E d'))

@[expose] noncomputable def splDist (p : ℕ) : Bool :=
  !Nat.beq (p / 125) (p / 25 % 5) && !Nat.beq (p / 125) (p / 5 % 5) && !Nat.beq (p / 125) (p % 5) &&
    !Nat.beq (p / 25 % 5) (p / 5 % 5) && !Nat.beq (p / 25 % 5) (p % 5) &&
      !Nat.beq (p / 5 % 5) (p % 5)

@[expose] noncomputable def splActK (x p : ℕ) : Bool :=
  eq22 45 6 (mask 6) x (splEP splE 0) (splEP splE (p / 125)) x &&
    eq22 45 6 (mask 6) x (splEP splE 1) (splEP splE (p / 25 % 5)) x &&
      eq22 45 6 (mask 6) x (splEP splE 2) (splEP splE (p / 5 % 5)) x &&
        eq22 45 6 (mask 6) x (splEP splE 3) (splEP splE (p % 5)) x

@[expose] noncomputable def splCovK (W : ℕ) : Bool :=
  allN 625 fun p => !splDist p || (Nat.blt (splLn W 7 p) 120 && splActK (XZ.T (splLn W 7 p)) p)

@[expose] noncomputable def splCm (h u : ℕ) : Bool := eq22 45 6 (mask 6) h u u h

@[expose] noncomputable def splCentK (c ci E : ℕ) : Bool :=
  strictB (pcomp 45 6 (mask 6) ci (pcomp 45 6 (mask 6) (splEP E 1) c)) fun u1 =>
    strictB (pcomp 45 6 (mask 6) ci (pcomp 45 6 (mask 6) (splEP E 2) c)) fun u2 =>
      strictB (pcomp 45 6 (mask 6) ci (pcomp 45 6 (mask 6) (splEP E 3) c)) fun u3 =>
        allN 1152 fun i => !(splCm (CA.T i) u1 && splCm (CA.T i) u2 && splCm (CA.T i) u3) ||
          inPts 45 6 16 B0Z.T (pcomp 45 6 (mask 6) c (pcomp 45 6 (mask 6) (CA.T i) ci))

theorem splBinds : bindWs 45 6 3 KA.G XZ.G splXW 0 = true ∧ XZ.T 0 = pidn 45 6 := by
  decide +kernel

theorem splNorm : splNormK XZ.G = true := by quickRfl

theorem splMeet : splMeetK 120 XZ.T = true := by quickRfl

theorem splCls : splClsK splE 13 = true := by quickRfl

theorem splCov : splCovK splW = true := by quickRfl

theorem splCent : splCentK czP cziP splE = true := by quickRfl

end CertificateChecks.KernelA45

end

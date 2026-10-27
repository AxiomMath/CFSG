
module

public import Certificates.Kernel.Co1M.O10075
public import Certificates.Kernel.Co1M.D10075
public import Certificates.Kernel.Co1B.C2046
public import CFSG.Sporadic.Co1.Module.InvFam
public import CFSG.Certificates.Kernel.Co1M.HitSound
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelCo1M

open CFSG.KD.Co1M CFSG.KC.Co1F2 CFSG.KC.M1F2 CFSG.KLie.CT CFSG.KC.InvFam CFSG.KC.SortTree
  CFSG.KC.Co1B CFSG.KC.Co1M CFSG.KC.VecK CFSG.Sporadic.Co1.Module CertificateChecks.KernelVec.Co1

@[expose] noncomputable def T3 : STree := ⟨recT t3L75 6 46, 5, 16, 64, 736⟩

@[expose] noncomputable def T4 : STree := ⟨recT t4L75 6 46, 5, 16, 64, 728⟩

@[expose] noncomputable def J3 : Nat → Nat := recT j3L75 6 32

@[expose] noncomputable def J4 : Nat → Nat := recT j4L75 6 32

@[expose] noncomputable def hitTest (w i : Nat) : Bool :=
  orbMemK 98280 (lk S 32) 17 (Nat.xor (lk Pt 32 i) w)

@[expose] noncomputable def hitSl (w : Nat) (J : Nat → Nat) (s : Nat) : Bool :=
  allS (Nat.mul s 256) 256 (hitAt 98280 (hitTest w) 552 J 10)

@[expose] noncomputable def hit3 (s : Nat) : Bool := hitSl w3v75 J3 s

@[expose] noncomputable def hit4 (s : Nat) : Bool := hitSl 1 J4 s

theorem words75 : andB (Nat.beq (wordABFrom CertificateChecks.KernelCo1Cover.R0
    CertificateChecks.KernelCo1Cover.R1 stabWord₁ oneK) RS1v75)
    (andB (Nat.beq (wordABFrom CertificateChecks.KernelCo1Cover.R0
      CertificateChecks.KernelCo1Cover.R1 stabWord₂ oneK) RS2v75)
    (Nat.beq (wordABFrom CertificateChecks.KernelCo1Cover.R0
      CertificateChecks.KernelCo1Cover.R1 gWord75 oneK) RGv75)) = true := by quickRfl

theorem trs75 : andB (Nat.beq (trK 24 RS1v75) (getL 0 RT75 0))
    (andB (Nat.beq (trK 24 RS2v75) (getL 0 RT75 1)) (Nat.beq (trK 24 RGv75) RGt75)) = true := by
  quickRfl

theorem fixes75 : andB (Nat.beq (vmF 24 (getL 0 RT75 0) 2) 2)
    (andB (Nat.beq (vmF 24 (getL 0 RT75 1) 2) 2) (Nat.beq (vmF 24 RGt75 4096) w3v75)) = true := by
  quickRfl

theorem mems75 : andB (orbMemK 98280 (lk S 32) 17 u3v75) (orbMemK 98280 (lk S 32) 17 3) = true := by
  quickRfl

theorem xor75 : Nat.beq (Nat.xor 2 u3v75) w3v75 = true := by quickRfl

theorem u3_lt : u3v75 < 2 ^ 24 := by decide +kernel

end CertificateChecks.KernelCo1M

end

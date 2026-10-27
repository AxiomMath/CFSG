module

public import Certificates.Kernel.Co1B.TriD2045
public import Certificates.Kernel.Co1B.Dag2045
public import Certificates.Kernel.SporSch.Co1.Packed
public import Certificates.Data.Kernel.Co1BTri
public import Certificates.Data.Kernel.Co1F2
public import Certificates.Data.Kernel.Spor.Prim
public import Certificates.Data.Kernel.PackSet
public import CFSG.Sporadic.Co1Block.TwoBData
public meta import Certificates.Kernel.Co1B.GenTri2045
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelCo1B.Tri2045

open CFSG.KC.Co1T CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KC.Pack
  CertificateChecks.KernelCo1B.Cent2045 CertificateChecks.KernelSporSch.Co1Packed

@[expose] noncomputable def matIdx (m : Nat) : Nat :=
  nIf(Nat.blt m (nat_lit 10), m, nIf(Nat.beq m (nat_lit 10), nat_lit 19, nat_lit 21))

@[expose] noncomputable def tchk (m : Nat) : Bool :=
  Nat.beq (CFSG.KC.Co1F2.trK 24 (D2.M (matIdx m))) (TB.T m)

@[expose] noncomputable def pchk (m : Nat) : Bool :=
  permOK 1365 11 (mask 11) (1365 * 11) (TB.P m) (TB.PI m)

@[expose] noncomputable def bsl (s : Nat) : Bool :=
  baseK (TB.T 12) TB.PT TB.SV TB.SG TB.ST (s * 128) 128

end CertificateChecks.KernelCo1B.Tri2045

#kc_slices CertificateChecks.KernelCo1B.Tri2045.TT CertificateChecks.KernelCo1B.Tri2045.tchk 12
#kc_slices CertificateChecks.KernelCo1B.Tri2045.PP CertificateChecks.KernelCo1B.Tri2045.pchk 12
#kc_slices CertificateChecks.KernelCo1B.Tri2045.B CertificateChecks.KernelCo1B.Tri2045.bsl 11

namespace CertificateChecks.KernelCo1B.Tri2045

open CFSG.KC.Co1T CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KC.Pack
  CertificateChecks.KernelCo1B.Cent2045 CertificateChecks.KernelSporSch.Co1Packed

theorem kTA : Nat.beq (CFSG.KC.Co1F2.trK 24 PA) (TB.T 12) = true := by quickRfl
theorem kLen : Nat.beq CFSG.Sporadic.Co1Block.twoBTris.length 1365 = true := by quickRfl
theorem kTris : trisPK TB.PT CFSG.Sporadic.Co1Block.twoBTris 0 = true := by quickRfl
theorem kSort : sortK TB.SV 4094 = true := by quickRfl
theorem k3 : Nat.beq (D2.M 3) PA = true := by quickRfl
theorem kId : idK 1365 11 (mask 11) = true := by quickRfl
theorem kP15 : powEqK 1365 11 (mask 11) (1365 * 11) (pidn 1365 11) (TB.P 2) 15 (pidn 1365 11) =
    true := by quickRfl
theorem kTZ : Nat.beq (CFSG.KC.Co1F2.trK 24 (mpowK (D2.M 2) 14)) TB.TZ = true := by quickRfl
theorem kV0 : ne1K (TB.T 12) (TB.V 0) = true := by quickRfl
theorem kV1 : ne1K TB.TZ (TB.V 1) = true := by quickRfl
theorem kV2 : neK2 TB.TZ (TB.T 12) (TB.V 2) = true := by quickRfl
theorem kV3 : ne1K2 (TB.T 12) TB.TZ (TB.V 3) = true := by quickRfl
theorem kSX : signK 1365 11 (mask 11) (TB.P 10) (TB.SW 0) (TB.SK 0) = true := by quickRfl
theorem kSY : signK 1365 11 (mask 11) (TB.P 11) (TB.SW 1) (TB.SK 1) = true := by quickRfl
theorem kS5 : signK 1365 11 (mask 11) (TB.P 5) (TB.SW 2) (TB.SK 2) = true := by quickRfl
theorem kKX : Nat.beq (Nat.mod (TB.SK 0) 2) 0 = true := by quickRfl
theorem kKY : Nat.beq (Nat.mod (TB.SK 1) 2) 0 = true := by quickRfl
theorem kK5 : Nat.beq (Nat.mod (TB.SK 2) 2) 1 = true := by quickRfl
theorem kOX : powEqK 1365 11 (mask 11) (1365 * 11) (pidn 1365 11) (TB.P 10) 2 (pidn 1365 11) =
    true := by quickRfl
theorem kOY : powEqK 1365 11 (mask 11) (1365 * 11) (pidn 1365 11) (TB.P 11) 5 (pidn 1365 11) =
    true := by quickRfl
theorem kXY : compEqK 1365 11 (mask 11) (1365 * 11) (TB.P 10) (TB.P 11) TB.PXY = true := by
  quickRfl
theorem kOXY : powEqK 1365 11 (mask 11) (1365 * 11) (pidn 1365 11) TB.PXY 13 (pidn 1365 11) =
    true := by quickRfl
theorem kNX : neK 1365 11 (mask 11) (1365 * 11) (TB.P 10) (pidn 1365 11) = true := by quickRfl
theorem kNY : neK 1365 11 (mask 11) (1365 * 11) (TB.P 11) (pidn 1365 11) = true := by quickRfl
theorem kNXY : neK 1365 11 (mask 11) (1365 * 11) TB.PXY (pidn 1365 11) = true := by quickRfl

end CertificateChecks.KernelCo1B.Tri2045

end

module

public import Certificates.Kernel.A45Cls.Checks5
public import Certificates.Kernel.A45Cls.Data7
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 400000
set_option maxHeartbeats 0

public section

namespace CertificateChecks.KernelA45

open CFSG.KC.Enum CFSG.KS CFSG.KC.OrbFind CFSG.KC.A45Cls CFSG.KC.ConjOrb
  CFSG.Certificates.Kernel.PkCV

@[expose] noncomputable def f1051ctz (z q u : ℕ) : Bool :=
  eq22 45 6 (mask 6) q u u q || eq22 45 6 (mask 6) q u z (pcomp 45 6 (mask 6) u q)

@[expose] noncomputable def f1051cnt (z u : ℕ) : ℕ :=
  cntN 32 fun i => f1051ctz z (QZ.T i) u

@[expose] noncomputable def f1051cnt2 (z u v : ℕ) : ℕ :=
  cntN 32 fun i => f1051ctz z (QZ.T i) u && f1051ctz z (QZ.T i) v

@[expose] noncomputable def f1051sylK (z f t : ℕ) : Bool :=
  strictB z fun z => strictB f fun f =>
    nrmP 45 6 3 64 TZ.G TZ.T f && inPts 45 6 64 TZ.T (pcomp 45 6 (mask 6) f f) &&
      !inPts 45 6 64 TZ.T f && eq22 45 6 (mask 6) f z z f && !inPts 45 6 32 QZ.T t

@[expose] noncomputable def f1051bndK (z t f : ℕ) : Bool :=
  strictB z fun z => strictB t fun t => strictB f fun f =>
    strictB (pcomp 45 6 (mask 6) t f) fun tf =>
      Nat.blt (f1051cnt z t) 16 && Nat.blt (f1051cnt z f) 16 && Nat.blt (f1051cnt z tf) 16 &&
        Nat.blt (f1051cnt2 z t f) 8

@[expose] noncomputable def f1051qcommK (z : ℕ) : Bool :=
  strictB z fun z =>
    inPts 45 6 32 QZ.T z && allN 4 fun i => allN 4 fun j => f1051ctz z (QZ.G i) (QZ.G j)

@[expose] noncomputable def f1051qdepK (b : ℕ) : Bool :=
  allN 32 fun i => Nat.ble (tDep (QZ.D i)) b

@[expose] noncomputable def f1051qnormK (c ci : ℕ) : Bool :=
  strictB c fun c => strictB ci fun ci =>
    allN 3 fun k => strictB (pcomp 45 6 (mask 6) c (pcomp 45 6 (mask 6) (CA.G k) ci)) fun g =>
      nrmP 45 6 4 32 QZ.G QZ.T g

@[expose] noncomputable def f1051o3 (z P : ℕ) : Bool :=
  isIdK 45 6 (pcomp 45 6 (mask 6) P (pcomp 45 6 (mask 6) P P)) && eq22 45 6 (mask 6) P z z P

@[expose] noncomputable def f1051otwoK (z : ℕ) (bw cw : List (List ℕ)) : Bool :=
  strictB z fun z => allN 4 fun k =>
    lettersK 3 (bw.getD k []) && lettersK 3 (cw.getD k []) &&
      strictB (wordK 45 6 KA.G (bw.getD k [])) fun b =>
        strictB (wordK 45 6 KA.G (cw.getD k [])) fun c =>
          f1051o3 z b && f1051o3 z c && eqP 45 6 (pcomp 45 6 (mask 6) b c) (QZ.G k)

theorem f1051syl : f1051sylK zP (uP 0) (TZ.T f1051tI) = true := by quickRfl

theorem f1051bounds : f1051bndK zP (TZ.T f1051tI) (uP 0) = true := by quickRfl

theorem f1051qcomm : f1051qcommK zP = true := by quickRfl

theorem f1051qdep : f1051qdepK 4 = true := by quickRfl

theorem f1051qnorm : f1051qnormK czP cziP = true := by quickRfl

theorem f1051otwo : f1051otwoK zP f1051bW f1051cW = true := by quickRfl

end CertificateChecks.KernelA45

end

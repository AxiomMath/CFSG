module

public import Certificates.Kernel.A45Cls.Checks
public import Certificates.Kernel.A45Cls.Grp3
public import Certificates.Data.Kernel.A45Cls.Over
public import Certificates.Data.OmegaT0

set_option maxRecDepth 400000
set_option maxHeartbeats 0

public section

namespace CertificateChecks.KernelA45

open CFSG.KC.Enum CFSG.KS CFSG.KC.OrbFind CFSG.KC.A45Cls CFSG.Certificates.Kernel.PkCV

@[expose] noncomputable def czP : ℕ := wordK 45 6 KA.G czW

@[expose] noncomputable def cziP : ℕ := wordK 45 6 KA.G cziW

@[expose] noncomputable def uP (j : ℕ) : ℕ := wordK 45 6 KA.G (uW.getD j [])

@[expose] noncomputable def uiP (j : ℕ) : ℕ := wordK 45 6 KA.G (uiW.getD j [])

@[expose] noncomputable def zP : ℕ := (cOf (Certificates.OmegaT0.z0 ())).1

@[expose] def t0If (p : ℕ) : ℕ := t0I.getD p 0

@[expose] noncomputable def y2P (j : ℕ) : ℕ := pcomp 45 6 (mask 6) (TZ.T (y2p j)) (uP j)

theorem binds3 :
    (cOf ((Certificates.OmegaS107.gensT0 ()).getD 0 1)).1 = TZ.G 0 ∧
    (cOf ((Certificates.OmegaS107.gensT0 ()).getD 1 1)).1 = TZ.G 1 ∧
    (cOf ((Certificates.OmegaS107.gensT0 ()).getD 2 1)).1 = TZ.G 2 ∧
    (cOf (Certificates.OmegaF1051.gq1 ())).1 = QZ.G 0 ∧
    (cOf (Certificates.OmegaF1051.gq2 ())).1 = QZ.G 1 ∧
    (cOf (Certificates.OmegaF1051.gq3 ())).1 = QZ.G 2 ∧
    (cOf (Certificates.OmegaF1051.gq4 ())).1 = QZ.G 3 ∧
    bindWs 45 6 3 KA.G BZ0.G (bW 0) 0 = true ∧ bindWs 45 6 3 KA.G BZ1.G (bW 1) 0 = true ∧
    bindWs 45 6 3 KA.G BZ2.G (bW 2) 0 = true ∧
    (lettersK 3 czW && lettersK 3 cziW &&
      allN 3 fun j => lettersK 3 (uW.getD j []) && lettersK 3 (uiW.getD j [])) = true := by
  decide +kernel

theorem ids3 : TZ.T 0 = pidn 45 6 ∧ QZ.T 0 = pidn 45 6 ∧ BZ0.T 0 = pidn 45 6 ∧
    BZ1.T 0 = pidn 45 6 ∧ BZ2.T 0 = pidn 45 6 := by
  decide +kernel

theorem zFacts : eqP 45 6 zP (pcomp 45 6 (mask 6) czP (pcomp 45 6 (mask 6) (KA.T KA.r0) cziP)) =
      true ∧ isIdK 45 6 (pcomp 45 6 (mask 6) czP cziP) = true ∧
    allN 3 (fun j => isIdK 45 6 (pcomp 45 6 (mask 6) (uP j) (uiP j))) = true ∧
    zcK 45 6 3 64 TZ.G TZ.T zP = true ∧
    allN 3 (fun k => eq22 45 6 (mask 6) zP (TZ.G k) (TZ.G k) zP) = true ∧
    allN 64 (fun p => isIdK 45 6 (pcomp 45 6 (mask 6) (TZ.T p) (TZ.T (t0If p)))) = true ∧
    allN 4 (fun k => inPts 45 6 64 TZ.T (QZ.G k)) = true ∧ inPts 45 6 64 TZ.T zP = true := by
  decide +kernel

theorem cosets : allN 1152 (fun i => cosK 45 6 3 64 3 TZ.G TZ.T uP
    (pcomp 45 6 (mask 6) czP (pcomp 45 6 (mask 6) (CA.T i) cziP))) = true := by
  decide +kernel

theorem tj0 : (isInvK 45 6 (y2P 0) && Nat.beq (fixK 45 6 (y2P 0)) 15 &&
      !inPts 45 6 64 TZ.T (y2P 0)) = true ∧
    b2K 45 6 3 32 TZ.G QZ.T BZ0.T (uP 0) (y2P 0) = true ∧
    outK 45 6 64 TZ.T t0If BZ0.T BZ0.G (uP 0) (uiP 0) (aWit 0) (bWit 0) = true := by
  decide +kernel

theorem tj1 : (isInvK 45 6 (y2P 1) && Nat.beq (fixK 45 6 (y2P 1)) 15 &&
      !inPts 45 6 64 TZ.T (y2P 1)) = true ∧
    b2K 45 6 3 32 TZ.G QZ.T BZ1.T (uP 1) (y2P 1) = true ∧
    outK 45 6 64 TZ.T t0If BZ1.T BZ1.G (uP 1) (uiP 1) (aWit 1) (bWit 1) = true := by
  decide +kernel

theorem tj2 : (isInvK 45 6 (y2P 2) && Nat.beq (fixK 45 6 (y2P 2)) 15 &&
      !inPts 45 6 64 TZ.T (y2P 2)) = true ∧
    b2K 45 6 3 32 TZ.G QZ.T BZ2.T (uP 2) (y2P 2) = true ∧
    outK 45 6 64 TZ.T t0If BZ2.T BZ2.G (uP 2) (uiP 2) (aWit 2) (bWit 2) = true := by
  decide +kernel

end CertificateChecks.KernelA45

end

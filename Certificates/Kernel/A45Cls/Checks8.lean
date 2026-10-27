module

public import Certificates.Kernel.A45Cls.Checks7
public import Certificates.Kernel.A45Cls.Grp5
public import Certificates.Data.OmegaT11

set_option maxRecDepth 400000
set_option maxHeartbeats 0

public section

namespace CertificateChecks.KernelA45

open CFSG.KC.Enum CFSG.KS CFSG.KC.OrbFind CFSG.KC.A45Cls CFSG.Certificates.Kernel.PkCV

@[expose] noncomputable def t11zP : ℕ := (cOf (Certificates.OmegaT11.zeta0 ())).1

@[expose] noncomputable def t11g1P : ℕ := (cOf (Certificates.OmegaT11.g1 ())).1

@[expose] noncomputable def t11g2P : ℕ := (cOf (Certificates.OmegaT11.g2 ())).1

@[expose] noncomputable def cubeK (P : ℕ) : Bool :=
  isIdK 45 6 (pcomp 45 6 (mask 6) P (pcomp 45 6 (mask 6) P P)) && !isIdK 45 6 P

@[expose] noncomputable def t11c3K (Z : ℕ) : Bool :=
  allN 96 fun i => !cubeK (T11Z.T i) || eq22 45 6 (mask 6) (T11Z.T i) Z Z (T11Z.T i)

@[expose] noncomputable def t11k3K (G : ℕ) : Bool :=
  allN 96 fun i => !isInvK 45 6 (T11Z.T i) || !Nat.beq (fixK 45 6 (T11Z.T i)) 13 ||
    !eq22 45 6 (mask 6) G (T11Z.T i) (T11Z.T i) G || eqP 45 6 (T11Z.T i) t11zP

@[expose] noncomputable def t11k4K (m : ℕ) : Bool :=
  allN 96 fun i => !cubeK (T11Z.T i) || allN 96 fun j => !cubeK (T11Z.T j) ||
    !isInvK 45 6 (pcomp 45 6 (mask 6) (T11Z.T i) (T11Z.T j)) ||
      (isInvK 45 6 (pcomp 45 6 (mask 6) (pcomp 45 6 (mask 6) (T11Z.T i) (T11Z.T j)) t11zP) &&
        Nat.beq (fixK 45 6
          (pcomp 45 6 (mask 6) (pcomp 45 6 (mask 6) (T11Z.T i) (T11Z.T j)) t11zP)) m)

theorem t11binds : bindWs 45 6 3 KA.G T11Z.G t11W 0 = true ∧ T11Z.N = 96 ∧ T11Z.ng = 5 ∧
    T11Z.T 0 = pidn 45 6 ∧
    allN 5 (fun k => eq22 45 6 (mask 6) (T11Z.G k) (i7rP 2) (i7rP 2) (T11Z.G k)) = true := by
  decide +kernel

theorem t11elts : allN 3 (fun k => lettersK 2 (t11mW.getD k [])) = true ∧
    eqP 45 6 (i7P (t11mW.getD 0 [])) t11zP = true ∧
    eqP 45 6 (i7P (t11mW.getD 1 [])) t11g1P = true ∧
    eqP 45 6 (i7P (t11mW.getD 2 [])) t11g2P = true ∧
    isInvK 45 6 t11zP = true ∧ fixK 45 6 t11zP = 13 ∧
    eq22 45 6 (mask 6) t11zP (i7rP 2) (i7rP 2) t11zP = true ∧
    cubeK t11g1P = true ∧ cubeK t11g2P = true ∧
    eq22 45 6 (mask 6) t11g1P (i7rP 2) (i7rP 2) t11g1P = true ∧
    eq22 45 6 (mask 6) t11g2P (i7rP 2) (i7rP 2) t11g2P = true ∧
    isInvK 45 6 (pcomp 45 6 (mask 6) t11g1P t11g2P) = true ∧
    eqP 45 6 (pcomp 45 6 (mask 6) (pcomp 45 6 (mask 6) (pcomp 45 6 (mask 6) (i7rP 2) (i7rP 1))
      (i7rP 2)) (i7rP 1)) (pcomp 45 6 (mask 6) (pcomp 45 6 (mask 6) t11g1P t11g2P) t11zP) =
      true := by
  decide +kernel

theorem t11c3 : t11c3K t11zP = true := by decide +kernel

theorem t11k3 : t11k3K t11g1P = true := by decide +kernel

theorem t11k4 : t11k4K 5 = true := by decide +kernel

end CertificateChecks.KernelA45

end

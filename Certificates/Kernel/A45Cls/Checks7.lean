module

public import Certificates.Kernel.A45Cls.Checks
public import Certificates.Kernel.A45Cls.Grp3
public import Certificates.Kernel.A45Cls.Grp4
public import Certificates.Data.Kernel.A45Cls.Over
public import Certificates.Data.OmegaT0

set_option maxRecDepth 400000
set_option maxHeartbeats 0

public section

namespace CertificateChecks.KernelA45

open CFSG.KC.Enum CFSG.KS CFSG.KC.OrbFind CFSG.KC.A45Cls CFSG.Certificates.Kernel.PkCV

@[expose] noncomputable def i7P (l : List ℕ) : ℕ := wordK 45 6 KA.G l

@[expose] noncomputable def i7rP (k : ℕ) : ℕ := (cOf ((Certificates.OmegaInv.reps ()).getD k 1)).1

@[expose] noncomputable def i7tP (k : ℕ) : ℕ :=
  [KA.T KA.r0, KB.T KB.r0, K540.T K540.r0, K36.T K36.r0].getD k 0

@[expose] noncomputable def i7oP (k : ℕ) : ℕ := i7P (i7oW.getD k [] ++ [2])

@[expose] noncomputable def i7gP (j : ℕ) : ℕ := i7P (i7gW.getD j [])

@[expose] noncomputable def i7giP (j : ℕ) : ℕ := i7P (i7giW.getD j [])

@[expose] noncomputable def i7coreK (m : ℕ) : Bool :=
  allN 120 fun i => isIdK 45 6 (K0Z.T i) || exN m fun j =>
    !inPts 45 6 120 K0Z.T (pcomp 45 6 (mask 6) (i7gP j) (pcomp 45 6 (mask 6) (K0Z.T i) (i7giP j)))

@[expose] noncomputable def i7qK (m : ℕ) : Bool :=
  allN 32 fun i => !isInvK 45 6 (QZ.T i) || eqP 45 6 (QZ.T i) (i7rP 0) ||
    Nat.beq (fixK 45 6 (QZ.T i)) m

theorem i7words : ((allN 4 fun k => lettersK 2 (i7cW.getD k []) && lettersK 2 (i7oW.getD k [])) &&
    (allN 6 fun k => lettersK 2 (i7mW.getD k [])) &&
    (allN 4 fun j => lettersK 2 (i7gW.getD j []) && lettersK 2 (i7giW.getD j []))) = true := by
  decide +kernel

theorem i7binds : (cOf (Certificates.OmegaInv.k1 ())).1 = K0Z.G 0 ∧
    (cOf (Certificates.OmegaInv.k2 ())).1 = K0Z.G 1 ∧ K0Z.N = 120 ∧ K0Z.ng = 2 ∧
    K0Z.T 0 = pidn 45 6 ∧ allN 120 (fun i => Nat.ble (CFSG.KC.ConjOrb.tDep (K0Z.D i)) 16) = true := by
  decide +kernel

theorem i7reps : allN 4 (fun k => eq22 45 6 (mask 6) (i7P (i7cW.getD k [])) (i7tP k) (i7rP k)
      (i7P (i7cW.getD k []))) = true ∧
    allN 4 (fun k => eq22 45 6 (mask 6) (i7oP k) (i7rP k) (i7rP k) (i7oP k)) = true ∧
    eqP 45 6 (i7P (i7mW.getD 0 [])) (i7rP 0) = true ∧
    eqP 45 6 (i7P (i7mW.getD 1 [])) (i7rP 1) = true ∧
    eqP 45 6 (i7P (i7mW.getD 2 [] ++ [2])) (i7rP 2) = true ∧
    eqP 45 6 (i7P (i7mW.getD 3 [] ++ [2])) (i7rP 3) = true ∧
    eqP 45 6 (i7P (i7mW.getD 4 [])) (K0Z.G 0) = true ∧
    eqP 45 6 (i7P (i7mW.getD 5 [])) (K0Z.G 1) = true ∧
    allN 4 (fun k => isInvK 45 6 (i7rP k)) = true ∧
    fixK 45 6 (i7rP 0) = 13 ∧ fixK 45 6 (i7rP 1) = 5 ∧ fixK 45 6 (i7rP 2) = 7 ∧
    fixK 45 6 (i7rP 3) = 15 := by
  decide +kernel

theorem i7core : allN 2 (fun k => eq22 45 6 (mask 6) (K0Z.G k) (i7rP 3) (i7rP 3) (K0Z.G k)) = true ∧
    allN 4 (fun j => eq22 45 6 (mask 6) (i7gP j) (i7rP 3) (i7rP 3) (i7gP j) &&
      isIdK 45 6 (pcomp 45 6 (mask 6) (i7gP j) (i7giP j))) = true ∧
    i7coreK 4 = true := by
  decide +kernel

theorem i7q : i7qK 5 = true := by decide +kernel

end CertificateChecks.KernelA45

end

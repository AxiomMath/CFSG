module

public import Certificates.Kernel.Co2Three.UqBind
public import Certificates.Kernel.Co2Three.QK

public section

namespace CertificateChecks.KernelCo2Three

open CFSG.KC.Enum CertificateChecks.KernelMisc.Co2K

@[expose] noncomputable def uqF (W c i : ℕ) : ℕ := f12 W (Nat.add (Nat.mul 20 c) i)

@[expose] noncomputable def clsK (P : ℕ → ℕ) (W c : ℕ) : Bool :=
  allN 9 (fun s => Nat.blt (uqF W c s) 729 && Nat.blt (uqF W c (Nat.add 9 s)) 729 &&
    Nat.beq (mmK (P (uqF W c s)) (P (uqF W c 9)))
      (mmK (P (uqF W c (Nat.add 9 s))) (P (uqF W c s)))) &&
  allN 9 (fun a => allN 9 fun b => Nat.beq a b ||
    !(Nat.beq (P (uqF W c (Nat.add 9 a))) (P (uqF W c (Nat.add 9 b))))) &&
  Nat.blt (uqF W c 18) 729 && Nat.blt (uqF W c 19) 729 &&
  comm (P (uqF W c 9)) (P (uqF W c 18)) && comm (P (uqF W c 9)) (P (uqF W c 19)) &&
  !(comm (P (uqF W c 18)) (P (uqF W c 19)))

@[expose] noncomputable def ptK (W : ℕ) (K CL SL : ℕ → ℕ) (j : ℕ) : Bool :=
  Nat.blt (K j) 2 ||
    (Nat.blt (CL j) 24 && Nat.blt (SL j) 9 && Nat.beq (uqF W (CL j) (Nat.add 9 (SL j))) j)

@[expose] noncomputable def UC (j : ℕ) : ℕ := f12 (Uq 1) j

@[expose] noncomputable def US (j : ℕ) : ℕ := f12 (Uq 2) j

@[expose] noncomputable def ch101704C (c : ℕ) : Bool := clsK QP (Uq 0) c

@[expose] noncomputable def ch101704P (c : ℕ) : Bool :=
  allN 81 fun t => ptK (Uq 0) FKd UC US (Nat.add (Nat.mul 81 c) t)

end CertificateChecks.KernelCo2Three

end

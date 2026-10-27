module

public import Certificates.Data.Kernel.AE6CertE.Keys
public import Certificates.Data.AE6CertE
public import Certificates.Kernel.OmegaEight.AutChainAP
public import Certificates.Kernel.AE6CertE.PathData

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelAE6CertE

open Certificates.AE6CertEK Certificates.AE6CertE

@[expose] noncomputable def eT : List Nat :=
  [CertificateChecks.KernelO8.AP.S 0, CertificateChecks.KernelO8.AP.S 1,
    CertificateChecks.KernelO8.AP.S 2, CertificateChecks.KernelO8.AP.S 3,
    CertificateChecks.KernelO8.AP.S 4, CertificateChecks.KernelO8.AP.S 5,
    CertificateChecks.KernelO8.AP.S 6, CertificateChecks.KernelO8.AP.S 7]

theorem ch517611_invo : ∀ l < 8, invoK (getK eT l) 360 = true := by decide +kernel

theorem ch517611_inv0 : ∀ l < 4, invarK (getK eT (l + l)) eO0 360 = true := by decide +kernel
theorem ch517611_inv1 : ∀ l < 4, invarK (getK eT (l + l)) eO1 360 = true := by decide +kernel
theorem ch517611_inv2 : ∀ l < 4, invarK (getK eT (l + l)) eO2 360 = true := by decide +kernel

theorem ch517611_w0 :
    ((List.range 315).all fun j => (eWordOf 0 j).all fun a => memK a [0, 2, 3, 4, 5, 6, 7]) =
      true := by decide +kernel
theorem ch517611_w1 :
    ((List.range 315).all fun j => (eWordOf 1 j).all fun a => memK a [0, 1, 2, 3, 4, 5, 6]) =
      true := by decide +kernel
theorem ch517611_w2 :
    ((List.range 315).all fun j => (eWordOf 2 j).all fun a => memK a [0, 1, 2, 3, 4, 6, 7]) =
      true := by decide +kernel

theorem ch517611_k0 : keysK eT eO0 (eWordOf 0) 315 = true := by decide +kernel
theorem ch517611_k1 : keysK eT eO2 (eWordOf 1) 315 = true := by decide +kernel
theorem ch517611_k2 : keysK eT eO1 (eWordOf 2) 315 = true := by decide +kernel

theorem ch517611_p0a : pathsK eT eO0 (eWordOf 0) PD 0 63 = true := by decide +kernel
theorem ch517611_p0b : pathsK eT eO0 (eWordOf 0) PD 63 63 = true := by decide +kernel
theorem ch517611_p0c : pathsK eT eO0 (eWordOf 0) PD 126 63 = true := by decide +kernel
theorem ch517611_p0d : pathsK eT eO0 (eWordOf 0) PD 189 63 = true := by decide +kernel
theorem ch517611_p0e : pathsK eT eO0 (eWordOf 0) PD 252 63 = true := by decide +kernel

@[expose] noncomputable def PD1 (j : Nat) : Nat := PD (Nat.add (nat_lit 315) j)

@[expose] noncomputable def PD2 (j : Nat) : Nat := PD (Nat.add (nat_lit 630) j)

theorem ch517611_p1a : pathsK eT eO2 (eWordOf 1) PD1 0 63 = true := by decide +kernel
theorem ch517611_p1b : pathsK eT eO2 (eWordOf 1) PD1 63 63 = true := by decide +kernel
theorem ch517611_p1c : pathsK eT eO2 (eWordOf 1) PD1 126 63 = true := by decide +kernel
theorem ch517611_p1d : pathsK eT eO2 (eWordOf 1) PD1 189 63 = true := by decide +kernel
theorem ch517611_p1e : pathsK eT eO2 (eWordOf 1) PD1 252 63 = true := by decide +kernel

theorem ch517611_p2a : pathsK eT eO1 (eWordOf 2) PD2 0 63 = true := by decide +kernel
theorem ch517611_p2b : pathsK eT eO1 (eWordOf 2) PD2 63 63 = true := by decide +kernel
theorem ch517611_p2c : pathsK eT eO1 (eWordOf 2) PD2 126 63 = true := by decide +kernel
theorem ch517611_p2d : pathsK eT eO1 (eWordOf 2) PD2 189 63 = true := by decide +kernel
theorem ch517611_p2e : pathsK eT eO1 (eWordOf 2) PD2 252 63 = true := by decide +kernel

end CertificateChecks.KernelAE6CertE

end

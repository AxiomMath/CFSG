module

public import Certificates.Data.Kernel.AEOrbitK

public section

namespace CertificateChecks.KernelAEOrbit

open Certificates.AEOrbit CFSG.KC.AEOrbitK

theorem c397301sign5 : (cands 5).all (fun σ => decide (Equiv.Perm.sign σ = 1)) = true := by
  decide +kernel

theorem c397301sign6 : (cands 6).all (fun σ => decide (Equiv.Perm.sign σ = 1)) = true := by
  decide +kernel

theorem c397301ct5 : ((cands 5).map tab == ct5) = true := by decide +kernel

theorem c397301ct6 : ((cands 6).map tab == ct6) = true := by decide +kernel

theorem c397301k5 : kchkM 5 ct5 4 = true := by decide +kernel

theorem c397301k6 : kchkM 6 ct6 4 = true := by decide +kernel

theorem c397301lt5 : (masks4 5).all (fun a => decide (a < 2 ^ 5)) = true := by decide +kernel

theorem c397301lt6 : (masks4 6).all (fun a => decide (a < 2 ^ 6)) = true := by decide +kernel

theorem c397301cov5 : ∀ α ∈ fours 5, ∃ a ∈ masks4 5, dec 5 a = α := by decide +kernel

theorem c397301cov6 : ∀ α ∈ fours 6, ∃ a ∈ masks4 6, dec 6 a = α := by decide +kernel

end CertificateChecks.KernelAEOrbit

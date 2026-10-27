module

public import CFSG.Quasithin.Background.SimsF5LatInputs
import Certificates.Kernel.SimsF5.Glue

public section

namespace Certificates

open CertificateChecks

open CFSG.Quasithin.SimsF5Lat in
theorem certificate7600 :
    Nat.card (Subgroup.closure {g | g ∈ f5TGens}) = 128 ∧
    Nat.card (Subgroup.closure {g | g ∈ f5GensA}) = 384 ∧
    Nat.card (Subgroup.closure {g | g ∈ f5GensB}) = 384 ∧
    Nat.card (Subgroup.closure {g | g ∈ f5GensM1}) = 1152 ∧
    Nat.card (Subgroup.closure {g | g ∈ f5GensM2}) = 1920 ∧
    Nat.card (Subgroup.closure {g | g ∈ f5GensM0}) = 51840 ∧
    (∀ Y : Subgroup GL6F3, Subgroup.closure {g | g ∈ f5TGens} ≤ Y →
      Y ≤ Subgroup.closure {g | g ∈ f5GensM0} →
      Y = Subgroup.closure {g | g ∈ f5TGens} ∨ Y = Subgroup.closure {g | g ∈ f5GensA} ∨
      Y = Subgroup.closure {g | g ∈ f5GensB} ∨ Y = Subgroup.closure {g | g ∈ f5GensM1} ∨
      Y = Subgroup.closure {g | g ∈ f5GensM2} ∨ Y = Subgroup.closure {g | g ∈ f5GensM0}) ∧
    f5XA ∈ Subgroup.closure {g | g ∈ f5GensM1} ∧ f5XB ∈ Subgroup.closure {g | g ∈ f5GensM1} ∧
    f5XB ∈ Subgroup.closure {g | g ∈ f5GensM2} ∧ f5XM1 ∈ Subgroup.closure {g | g ∈ f5GensM0} ∧
    f5XM2 ∈ Subgroup.closure {g | g ∈ f5GensM0} ∧ f5XA ∉ Subgroup.closure {g | g ∈ f5GensB} := KernelSimsF5.facts

end Certificates

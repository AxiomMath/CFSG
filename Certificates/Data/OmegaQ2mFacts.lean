module

public import Certificates.Data.OmegaQ2m

public section

namespace Certificates.OmegaQ2m

open CFSG.ComponentClassification.CatFactsSmall.PSp43

local notation "P45" => Equiv.Perm (Fin 45)

structure Facts : Prop where
  conj : ∃ c ∈ QP45.originalSubgroup,
    c * Certificates.P43Twin.tA () * c⁻¹ = Certificates.OmegaT0.z0 ()
  q : ∀ x ∈ Certificates.OmegaF1051.q0l (), x * x = 1 → x ≠ 1 → x ≠ Certificates.OmegaT0.z0 () →
    Nat.card ↥(QA45.originalSubgroup ⊓ Subgroup.centralizer ({x} : Set P45)) = 192

end Certificates.OmegaQ2m

end

module

public import CFSG.Quasithin.Vol2.Ch6Sec1Lem5Even7In
import Certificates.Kernel.A7Lat.Glue

public section

namespace Certificates

open CertificateChecks

open Equiv CFSG.Quasithin.H13.Even7 in
theorem certificate7250 :
    Nat.card (Subgroup.closure {g | g ∈ mGens}) = 2520 ∧
    (∀ j < 12, Nat.card (Subgroup.closure {g | g ∈ (tGens :: lat).getD j []}) = sizes.getD j 0) ∧
    (∀ Y : Subgroup (Perm (Fin 7)), Subgroup.closure {g | g ∈ tGens} ≤ Y →
      Y ≤ Subgroup.closure {g | g ∈ mGens} →
      ∃ j < 12, Y = Subgroup.closure {g | g ∈ (tGens :: lat).getD j []}) :=
  ⟨KernelA7Lat.Glue.card_mGens, KernelA7Lat.Glue.card_Lm, KernelA7Lat.Glue.overgroups⟩

end Certificates

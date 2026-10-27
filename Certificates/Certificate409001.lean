module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15K21dU42Inputs
import Certificates.Kernel.U42Lat.Glue

public section

namespace Certificates

open CertificateChecks

open Equiv CFSG.LocalAnalysis.RankThreeUC.S15.K21dU42Cert in
theorem certificate409001 :
    (Subgroup.closure {g | g ∈ tGens} ≤ Subgroup.closure {g | g ∈ mGens} ∧
      Nat.card (Subgroup.closure {g | g ∈ tGens}) = 64 ∧
      Nat.card (Subgroup.closure {g | g ∈ mGens}) = 25920) ∧
    ((∀ j < 6, Subgroup.closure {g | g ∈ (tGens :: lat).getD j []} ≤
        Subgroup.closure {g | g ∈ mGens} ∧
        Nat.card (Subgroup.closure {g | g ∈ (tGens :: lat).getD j []}) = sizes.getD j 0) ∧
      ∀ Y : Subgroup (Perm (Fin 45)), Subgroup.closure {g | g ∈ tGens} ≤ Y →
        Y ≤ Subgroup.closure {g | g ∈ mGens} →
        ∃ j < 6, Y = Subgroup.closure {g | g ∈ (tGens :: lat).getD j []}) ∧
    (ea ∈ Subgroup.closure {g | g ∈ L3} ∧ eb ∈ Subgroup.closure {g | g ∈ L3} ∧
      Nat.card (Subgroup.closure {g | g ∈ [ea, eb]}) = 9 ∧ ea * ea * ea = 1 ∧
      eb * eb * eb = 1 ∧
      ∀ v ∈ Subgroup.closure {g | g ∈ L3}, ¬ (v * ea * v⁻¹ = ea⁻¹ ∧ v * eb * v⁻¹ = eb⁻¹)) := KernelU42Lat.Glue.facts

end Certificates

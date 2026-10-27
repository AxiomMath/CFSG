module

public import Certificates.Kernel.AE6E8.Facts

public section

namespace Certificates

open CertificateChecks.KernelAE6E8

open Certificates.AE6CertB Certificates.AE6Model
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3.A6S in
theorem certificate517531 :
    Nat.card (Subgroup.closure {g | g ∈ ae8Gens16 ()}) = 2580480 ∧
    Nat.card (Subgroup.closure {g | g ∈ v0Gens ()}) = 1290240 ∧
    Nat.card (Subgroup.closure {g | g ∈ grGens ()}) = 2580480 ∧
    CFSG.ClassicalInvolution.Q3.PhilipHall.Thm3Step.S5.Q8Rel ((k0Gens ()).getD 0 1)
      ((k0Gens ()).getD 1 1) ∧
    (∀ c : Fin 2, ∀ r ∈ A6.curtisRels,
      A6.curtisEval (List.ofFn fun i => A6.curtisGen (ae6Diag c i)) r = 1) ∧
    ∀ (c : Fin 2) (s : Fin 3), ae6Word ((ae6KWord s).map (ae6Diag c)) ∈ ae6Twin (ae6DiagTwin c) :=
  ⟨card16, cardV0, cardGr, kq8, diagRels, diagTwins⟩

end Certificates

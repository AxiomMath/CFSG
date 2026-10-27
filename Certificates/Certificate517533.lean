
module


public import Certificates.Kernel.AE6Tri.FactsTAT

public section

public section

namespace Certificates

open CertificateChecks.KernelAE6Tri
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3.A6S

open CFSG.ClassicalInvolution.Generic CFSG.EvenSmallLie.OmegaEight
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3.A6S in
theorem certificate517533 :
    ((∀ i, ae6Word (ae6TriGen₀ i) ∈ ae6TriQuat0) ∧
      ∀ y : Fin 6 → AE6Om, (∀ i, y i ∈ ae6TriQuat0) →
        (∀ u ∈ ae6TriProf,
          orderOf (u.map y).prod = orderOf (u.map fun i => ae6Word (ae6TriGen₀ i)).prod ∧
          ((u.map y).prod ∈ ae6TriStab 2 ↔
            (u.map fun i => ae6Word (ae6TriGen₀ i)).prod ∈ ae6TriStab 2) ∧
          ((u.map y).prod ∈ ae6TriQuat0 ↔
            (u.map fun i => ae6Word (ae6TriGen₀ i)).prod ∈ ae6TriQuat0)) →
        ∃ m ∈ ae6LetterSub ↑ae6MLetters, ∃ j : Fin 6,
          ∀ i, y i = m * ae6Word (ae6TriRep 0 j (ae6TriGen₀ i)) * m⁻¹) ∧
    (∀ e : Fin 3, e ≠ 0 → ∀ j : Fin 6, ∀ c ∈ ae6EdgeLetters 0 1,
      ae6Word ((ae6TriRep 0 j [c]).map (ae6EdgeMap e)) =
        ae6Word (ae6TriRep e (ae6RepSwap j) [ae6EdgeMap e c])) ∧
    ∀ e : Fin 3, e ≠ 0 → ∀ s : Fin 2,
      ae6Word ((ae6KWord s.castSucc).map (ae6EdgeMap e)) ∈
        conjSub (ae6Word (ae6TriEdgeC e)) ae6ModelK := by
  refine ⟨ta0, fun e he j c hc => ?_, fun e he s => ?_⟩
  · obtain ⟨j, hj⟩ := j
    obtain ⟨e', rfl⟩ := Fin.exists_succ_eq.2 he
    exact rep_tr e' j hj c hc
  · obtain ⟨e', rfl⟩ := Fin.exists_succ_eq.2 he
    exact k0_tr e' s

end Certificates

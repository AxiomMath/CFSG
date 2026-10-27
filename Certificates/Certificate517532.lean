
module


public import Certificates.Kernel.AE6Tri.FactsT
public import Certificates.Kernel.AE6Tri.FactsQ
public import Certificates.Kernel.AE6Tri.FactsGr

public section

public section

namespace Certificates

open CertificateChecks.KernelAE6Tri

open CFSG.ClassicalInvolution.Generic CFSG.EvenSmallLie.OmegaEight
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3.A6S in
open scoped Pointwise in
theorem certificate517532 :
    (∀ c : Fin 2, ∃ x : Equiv.Perm (Fin 360), ∀ i : Fin 8,
      x * (A6.curtisGen i : Equiv.Perm (Fin 360)) * x⁻¹ = A6.curtisGen (ae6Diag c i)) ∧
    Nat.card (ae6LetterSub ↑ae6MLetters) = 12288 ∧
    1290240 ≤ Nat.card (ae6ModelV 0) ∧
    86016 ≤ Nat.card (ae6LetterSub ↑(ae6EdgeLetters 0 1)) ∧
    (∀ l : Fin 3, ae6ModelV l ≤ ae6TriStab l) ∧
    (∀ e : Fin 3, 15 * Nat.card ↥(ae6ModelV (ae6EdgeK e) ⊓ ae6TriStab (ae6EdgeL e)) ≤
      Nat.card (ae6ModelV (ae6EdgeK e))) ∧
    (∀ e : Fin 3, 7 * Nat.card ↥(ae6LetterSub ↑(ae6EdgeLetters (ae6EdgeK e) (ae6EdgeL e)) ⊓
      ae6TriStab (AE6CertB.triEM e)) ≤ Nat.card (ae6LetterSub ↑(ae6EdgeLetters (ae6EdgeK e) (ae6EdgeL e)))) ∧
    (∀ m ∈ ae6LetterSub ↑ae6MLetters,
      (∀ i ∈ ae6MLetters, m * A6.curtisGen i = A6.curtisGen i * m) → m = 1) ∧
    Nat.card (Subgroup.closure (Set.range fun i : ↥(ae6VertexLetters 0) =>
      (A6.curtisGen (i : Fin 8), ae6Word (ae6Delta 0 i)))) = 1290240 ∧
    Subgroup.closure (Set.range fun i : ↥(ae6VertexLetters 0) => ae6Word (ae6Delta 0 i)) =
      ae6ModelV 0 ∧
    (∀ (k s : Fin 3),
      ae6Word (ae6DeltaW k (ae6KWord s)) ∈ conjSub (ae6Word (ae6TriMemC k)) ae6ModelK) ∧
    (∀ x : Fin 4, ∀ w ∈ ae6TriQWords x,
      ∀ i ∈ ae6MLetters, A6.curtisGen i * ae6Word w * A6.curtisGen i ∈ ae6TriQ x) ∧
    (∀ x y : Fin 4, x ≠ y → ae6TriQ x ≠ ae6TriQ y) ∧
    (∀ (k : Fin 3) (x : Fin 4), ∀ w ∈ ae6TriQWords x,
      ae6Word (ae6DeltaW k w) ∈ ae6TriQ (ae6DeltaQ k x)) ∧
    Subgroup.closure (Set.range fun i => ae6Word (ae6TriGen 0 i)) =
      ae6LetterSub ↑(ae6EdgeLetters 0 1) := by
  refine ⟨fun c => ?_, card_ae6M, card_v0_ge, card_e0_ge, v_le_stab, dist_v, dist_e, tz,
    card_graph, v0_images, td_k0, q_norm, q_dist, q_delta, tgen0⟩
  obtain ⟨x, hx⟩ := gam_perm c
  exact ⟨x, fun i => by rw [coe_curtisGen, coe_curtisGen]; exact hx i⟩

end Certificates

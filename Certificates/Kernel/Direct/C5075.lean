module

public import CFSG.GH74.GLS.C3.Prop121.A6ClassInputs
import CFSG.GH74.GLS.C3.Prop121.CentKFin
import Mathlib.Tactic.Group

public section

namespace CertificateChecks.KernelDirect.C5075

open CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.C3 CFSG.GH74.GLS.C3.Prop121
open Equiv Perm

theorem conj_all_of_rep {G : Type*} [Group G] [DecidableEq G] (I E W : List G) (a0 : G)
    (s : G →* ℤˣ) (hE : ∀ π, π ∈ E ↔ s π = 1)
    (h : I.all (fun a => W.any fun π => decide (π * a0 * π⁻¹ = a) && decide (s π = 1)) = true) :
    I.all (fun a => I.all fun b => E.any fun π => decide (π * a * π⁻¹ = b)) = true := by
  rw [List.all_eq_true]
  intro a ha
  rw [List.all_eq_true]
  intro b hb
  obtain ⟨πa, -, ea⟩ := List.any_eq_true.1 (List.all_eq_true.1 h a ha)
  obtain ⟨πb, -, eb⟩ := List.any_eq_true.1 (List.all_eq_true.1 h b hb)
  rw [Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq] at ea eb
  refine List.any_eq_true.2 ⟨πb * πa⁻¹, (hE _).2 ?_, ?_⟩
  · rw [map_mul, map_inv, ea.2, eb.2, inv_one, mul_one]
  · rw [decide_eq_true_eq, ← ea.1, ← eb.1]
    group

@[expose] def w6 : List (Perm (Fin 6)) :=
  [1,
    Equiv.swap 4 5 * Equiv.swap 3 5,
    Equiv.swap 4 5 * Equiv.swap 3 4,
    Equiv.swap 3 4 * Equiv.swap 2 4,
    Equiv.swap 3 5 * Equiv.swap 2 5,
    Equiv.swap 3 5 * Equiv.swap 2 4,
    Equiv.swap 4 5 * Equiv.swap 1 2,
    Equiv.swap 3 4 * Equiv.swap 1 2,
    Equiv.swap 3 5 * Equiv.swap 1 2,
    Equiv.swap 4 5 * Equiv.swap 3 5 * Equiv.swap 2 5 * Equiv.swap 1 5,
    Equiv.swap 4 5 * Equiv.swap 3 4 * Equiv.swap 2 4 * Equiv.swap 1 4,
    Equiv.swap 4 5 * Equiv.swap 3 4 * Equiv.swap 2 5 * Equiv.swap 1 5,
    Equiv.swap 2 3 * Equiv.swap 1 2,
    Equiv.swap 4 5 * Equiv.swap 3 5 * Equiv.swap 2 5 * Equiv.swap 1 2,
    Equiv.swap 4 5 * Equiv.swap 3 4 * Equiv.swap 2 4 * Equiv.swap 1 2,
    Equiv.swap 3 4 * Equiv.swap 1 4,
    Equiv.swap 3 5 * Equiv.swap 1 5,
    Equiv.swap 4 5 * Equiv.swap 3 4 * Equiv.swap 2 5 * Equiv.swap 1 4,
    Equiv.swap 4 5 * Equiv.swap 3 5 * Equiv.swap 2 3 * Equiv.swap 1 2,
    Equiv.swap 2 4 * Equiv.swap 1 2,
    Equiv.swap 4 5 * Equiv.swap 3 4 * Equiv.swap 2 5 * Equiv.swap 1 2,
    Equiv.swap 4 5 * Equiv.swap 1 5,
    Equiv.swap 3 5 * Equiv.swap 1 4,
    Equiv.swap 4 5 * Equiv.swap 3 4 * Equiv.swap 2 4 * Equiv.swap 1 5,
    Equiv.swap 4 5 * Equiv.swap 3 4 * Equiv.swap 2 3 * Equiv.swap 1 2,
    Equiv.swap 2 5 * Equiv.swap 1 2,
    Equiv.swap 4 5 * Equiv.swap 3 5 * Equiv.swap 2 4 * Equiv.swap 1 2,
    Equiv.swap 4 5 * Equiv.swap 1 4,
    Equiv.swap 3 4 * Equiv.swap 1 5,
    Equiv.swap 4 5 * Equiv.swap 3 5 * Equiv.swap 2 5 * Equiv.swap 1 4,
    Equiv.swap 3 4 * Equiv.swap 2 4 * Equiv.swap 1 4 * Equiv.swap 0 4,
    Equiv.swap 3 5 * Equiv.swap 2 5 * Equiv.swap 1 5 * Equiv.swap 0 5,
    Equiv.swap 3 5 * Equiv.swap 2 4 * Equiv.swap 1 4 * Equiv.swap 0 4,
    Equiv.swap 4 5 * Equiv.swap 3 5 * Equiv.swap 1 5 * Equiv.swap 0 5,
    Equiv.swap 4 5 * Equiv.swap 3 4 * Equiv.swap 1 4 * Equiv.swap 0 4,
    Equiv.swap 3 5 * Equiv.swap 2 4 * Equiv.swap 1 5 * Equiv.swap 0 5,
    Equiv.swap 1 4 * Equiv.swap 0 4,
    Equiv.swap 4 5 * Equiv.swap 3 4 * Equiv.swap 1 5 * Equiv.swap 0 5,
    Equiv.swap 3 5 * Equiv.swap 2 5 * Equiv.swap 1 4 * Equiv.swap 0 4,
    Equiv.swap 1 5 * Equiv.swap 0 5,
    Equiv.swap 4 5 * Equiv.swap 3 5 * Equiv.swap 1 4 * Equiv.swap 0 4,
    Equiv.swap 3 4 * Equiv.swap 2 4 * Equiv.swap 1 5 * Equiv.swap 0 5,
    Equiv.swap 3 5 * Equiv.swap 2 4 * Equiv.swap 1 5 * Equiv.swap 0 4,
    Equiv.swap 3 5 * Equiv.swap 2 5 * Equiv.swap 1 4 * Equiv.swap 0 5,
    Equiv.swap 3 4 * Equiv.swap 2 4 * Equiv.swap 1 5 * Equiv.swap 0 4]

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem okInvConj_true_0 : okInvConj = true := by
  unfold okInvConj
  exact conj_all_of_rep inv6 even6 w6 (Equiv.swap 0 1 * Equiv.swap 2 3) sign (fun _ => mem_even6)
    (by decide +kernel)

end CertificateChecks.KernelDirect.C5075

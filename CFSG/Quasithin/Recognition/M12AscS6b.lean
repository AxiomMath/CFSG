module

public import CFSG.Quasithin.Recognition.M12AscCoxInputs

public section

namespace CFSG.Quasithin

open Equiv

@[expose] def pz : Perm (Fin 6) := swap 0 1
@[expose] def pa : Perm (Fin 6) := swap 2 3 * swap 4 5
@[expose] def pcp : Perm (Fin 6) := swap 2 4 * swap 3 5
@[expose] def pb : Perm (Fin 6) := swap 4 5 * swap 0 1
@[expose] def ps : Perm (Fin 6) := swap 0 1 * (swap 2 3 * swap 4 5)

theorem C1_norm : ∀ γ : Perm (Fin 6), γ * pz = pz * γ →
    ∀ w ∈ [1, pa, pcp, pa * pcp], ∃ w' ∈ [1, pa, pcp, pa * pcp], γ * w = w' * γ := by
  decide +kernel

theorem C2_norm : ∀ γ : Perm (Fin 6), γ * ps = ps * γ →
    ∀ w ∈ [1, pa, pa * pb, pb], ∃ w' ∈ [1, pa, pa * pb, pb], γ * w = w' * γ := by
  decide +kernel

theorem card_C1 : Nat.card (Subgroup.centralizer ({pz} : Set (Perm (Fin 6)))) = 48 := by
  have : Nat.card (Subgroup.centralizer ({pz} : Set (Perm (Fin 6)))) =
      Nat.card {γ : Perm (Fin 6) // γ * pz = pz * γ} :=
    Nat.card_congr (Equiv.subtypeEquivRight (fun γ => by
      rw [Subgroup.mem_centralizer_singleton_iff]))
  rw [this, Nat.card_eq_fintype_card]
  decide +kernel

theorem card_C2 : Nat.card (Subgroup.centralizer ({ps} : Set (Perm (Fin 6)))) = 48 := by
  have : Nat.card (Subgroup.centralizer ({ps} : Set (Perm (Fin 6)))) =
      Nat.card {γ : Perm (Fin 6) // γ * ps = ps * γ} :=
    Nat.card_congr (Equiv.subtypeEquivRight (fun γ => by
      rw [Subgroup.mem_centralizer_singleton_iff]))
  rw [this, Nat.card_eq_fintype_card]
  decide +kernel

theorem pa_comm_pz : pa * pz = pz * pa := by decide +kernel

theorem z2_conj : swap 1 2 = ((pcp * (swap 0 2 * swap 1 3)) * swap 3 4 *
    (pcp * (swap 0 2 * swap 1 3))⁻¹ : Perm (Fin 6)) := by decide +kernel

theorem z2_conj_mem : (pcp * (swap 0 2 * swap 1 3) : Perm (Fin 6)) * ps =
    ps * (pcp * (swap 0 2 * swap 1 3)) := by decide +kernel

end CFSG.Quasithin

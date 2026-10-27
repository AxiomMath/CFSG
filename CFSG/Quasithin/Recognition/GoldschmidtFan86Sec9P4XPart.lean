module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec9P4Lab
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec9Defs

public section

namespace CFSG.Quasithin.Fan86

open SimpleGraph CFSG.Quasithin.F6.GoldAmL3T

variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V}

namespace P4X

variable {L : ZLab Γ G}

@[expose] def FixedPair {A : V} (D' : D10Set L A) : Prop :=
  ∀ g : G, g • D'.alpha 0 = D'.alpha 0 → g • D'.alpha 2 = D'.alpha 2 → orderOf g = 4 →
    (g * g = L.z (D'.alpha 0) * L.z (D'.alpha 2) ∨ g * g = L.z (D'.alpha 0)) →
      ∃ m : Fin 5, (m = 1 ∨ m = 3) ∧ g • D'.alpha m = D'.alpha m

theorem orderOf_w_eq_four (F : FanTree Γ G) {α : V} (h71c : Fan71c F L) {D : D10Set L α} {w : G}
    (hw : IsW1 D w) : orderOf w = 4 := by
  have hz2 : L.z (D.delta 2) * L.z (D.delta 2) = 1 := L.z_mul_self (D.valence_delta F 2)
  have hzα : L.z α * L.z α = 1 := L.z_mul_self D.val
  have hcomm : L.z (D.delta 2) * L.z α = L.z α * L.z (D.delta 2) :=
    D.zd_comm_start F h71c 2
  have hne : L.z (D.delta 2) * L.z α ≠ 1 := fun h => by
    have h1 : L.z (D.delta 2) = L.z α := by
      rw [eq_inv_of_mul_eq_one_left h, L.z_inv D.val]
    have h2 := h71c.z_injective (D.valence_delta F 2) D.val h1
    have h3 := D.dist_delta F 2
    rw [h2, SimpleGraph.dist_self] at h3
    omega
  have hsq1 : (L.z (D.delta 2) * L.z α) * (L.z (D.delta 2) * L.z α) = 1 := by
    calc (L.z (D.delta 2) * L.z α) * (L.z (D.delta 2) * L.z α)
        = L.z (D.delta 2) * (L.z α * L.z (D.delta 2)) * L.z α := by group
      _ = L.z (D.delta 2) * (L.z (D.delta 2) * L.z α) * L.z α := by rw [← hcomm]
      _ = (L.z (D.delta 2) * L.z (D.delta 2)) * (L.z α * L.z α) := by group
      _ = 1 := by rw [hz2, hzα, mul_one]
  have hne2 : w ^ 2 ≠ 1 := by
    rw [pow_two]
    rcases hw.sq with h | h
    · rw [h]; exact hne
    · rw [h]; exact L.z_ne_one (D.valence_delta F 2)
  have h4 : w ^ 4 = 1 := by
    have e : w ^ 4 = (w * w) * (w * w) := by rw [show 4 = 2 + 2 from rfl, pow_add, pow_two]
    rcases hw.sq with h | h
    · rw [e, h]; exact hsq1
    · rw [e, h]; exact hz2
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := orderOf_eq_prime_pow (p := 2) (n := 1) (x := w) (by simpa using hne2) (by simpa using h4)
  simpa using this

end P4X

end CFSG.Quasithin.Fan86

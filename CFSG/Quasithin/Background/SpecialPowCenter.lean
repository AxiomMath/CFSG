module

public import CFSG.Quasithin.Background.F1Lemma10
public import CFSG.Quasithin.Background.A1cA133

public section

namespace CFSG.Quasithin.H13

variable {G : Type} [Group G]

theorem commutator_eq_centerOf_of_isSpecialPow [Finite G] {Q : Subgroup G} {p q w : ℕ}
    (hw : 1 ≤ w) (hq : 2 ≤ q) (h : IsSpecialPow p q w ↥Q) :
    ⁅Q, Q⁆ = centerOf Q ∧ Nat.card (centerOf Q) = q := by
  obtain ⟨⟨-, hs⟩, hcard, hcen⟩ := h
  have hZ : Nat.card (centerOf Q) = q := by
    rw [A1c.centerOf_eq_map_center, Subgroup.card_map_of_injective Q.subtype_injective, hcen]
  refine ⟨?_, hZ⟩
  rcases hs with ⟨hcomm, -⟩ | ⟨hc, -, -⟩
  ·
    exfalso
    have htop : Subgroup.center ↥Q = ⊤ := by
      rw [eq_top_iff]
      intro z _
      exact Subgroup.mem_center_iff.mpr fun g => hcomm.is_comm.comm g z
    rw [htop, Subgroup.card_top, hcard] at hcen
    have : q ^ 1 < q ^ (1 + 2 * w) := Nat.pow_lt_pow_right (by omega) (by omega)
    rw [pow_one] at this
    omega
  · rw [A1c.centerOf_eq_map_center, ← hc, commutator_def, Subgroup.map_commutator,
      ← MonoidHom.range_eq_map, Subgroup.range_subtype]

end CFSG.Quasithin.H13

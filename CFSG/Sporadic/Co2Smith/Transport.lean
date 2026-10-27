module

public import CFSG.Sporadic.Co2Smith.Defs

public section

namespace CFSG.Sporadic.Co2Smith

open Subgroup

variable {H H' : Type*} [Group H] [Group H']

instance fact_prime_five : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩

theorem map_pCore_two (e : H ≃* H') : (CFSG.pCore 2 H).map e.toMonoidHom = CFSG.pCore 2 H' :=
  CFSG.pCore_map_iso 2 e

theorem apply_mem_pCore_two (e : H ≃* H') {x : H} (hx : x ∈ CFSG.pCore 2 H) :
    e x ∈ CFSG.pCore 2 H' := by
  rw [← map_pCore_two e]
  exact ⟨x, hx, rfl⟩

theorem symm_apply_mem_pCore_two (e : H ≃* H') {x : H'} (hx : x ∈ CFSG.pCore 2 H') :
    e.symm x ∈ CFSG.pCore 2 H := by
  have := apply_mem_pCore_two e.symm hx
  exact this

theorem oddCore_eq_bot_of_simple {G : Type*} [Group G] [Finite G] [IsSimpleGroup G] {z : G}
    (hz : orderOf z = 2) : CFSG.oddCore G = ⊥ := by
  refine le_antisymm (sSup_le fun N hN => ?_) bot_le
  rcases hN.1.eq_bot_or_eq_top with h | h
  · exact h.le
  · exfalso
    have hodd := hN.2
    rw [h, Subgroup.card_top] at hodd
    have h2 : 2 ∣ Nat.card G := hz ▸ orderOf_dvd_natCard z
    exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr h2)

theorem center_eq_bot_of_simple {G : Type*} [Group G] [IsSimpleGroup G]
    (h : ∃ a b : G, a * b ≠ b * a) : center G = ⊥ := by
  rcases (inferInstance : (center G).Normal).eq_bot_or_eq_top with hc | hc
  · exact hc
  · exfalso
    obtain ⟨a, b, hab⟩ := h
    have ha : a ∈ center G := hc ▸ mem_top a
    exact hab ((mem_center_iff.mp ha b).symm)

theorem smithHyp_of_simple {G : Type*} [Group G] [Finite G] [IsSimpleGroup G] {z : G}
    (hz : orderOf z = 2) (hnc : ∃ a b : G, a * b ≠ b * a)
    (h : SmithLocal (centralizer ({z} : Set G))) : SmithHyp G z :=
  ⟨oddCore_eq_bot_of_simple hz, center_eq_bot_of_simple hnc, hz, h⟩

end CFSG.Sporadic.Co2Smith

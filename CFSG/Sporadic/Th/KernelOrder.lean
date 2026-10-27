
module


public import CFSG.Sporadic.Th.KernelInputs

public section

namespace CFSG.Sporadic.Th.Kernel

open CFSG.Sporadic.Bridge CFSG.Sporadic.ThSchreier TauCeti Pointwise

variable (h : KernelFacts)
include h

variable (h : KernelFacts)

theorem thOrder_dvd_card_J : thOrder ∣ Nat.card J := by
  have e : thOrder = 2 ^ 15 * 3 ^ 10 * 5 ^ 3 * 7 ^ 2 * 13 * 19 * 31 := by norm_num [thOrder]
  rw [e]
  refine Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) ?_ h.dvd31
  refine Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) ?_ h.dvd19
  refine Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) ?_ h.dvd13
  refine Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) ?_ h.dvd7
  refine Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) ?_ h.dvd5
  exact Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) h.dvd2 h.dvd3

omit h in
theorem range_eq_top {ψ : P →* J} (ha : a ∈ ψ.range) (hb : b ∈ ψ.range) : ψ.range = ⊤ := by
  rw [eq_top_iff, ← closure_ab, Subgroup.closure_le]
  rintro _ (rfl | rfl)
  · exact ha
  · exact hb

theorem card_J_eq : Nat.card J = thOrder := by
  have := h.finite
  obtain ⟨ψ, -, -, ha, hb⟩ := h.fwd
  have hs : Function.Surjective ψ := MonoidHom.range_eq_top.1 (range_eq_top ha hb)
  refine le_antisymm ((Nat.card_le_card_of_surjective _ hs).trans h.card_le) ?_
  exact Nat.le_of_dvd Nat.card_pos (thOrder_dvd_card_J h)

theorem card_P_eq : Nat.card P = thOrder := by
  have := h.finite
  obtain ⟨ψ, -, -, ha, hb⟩ := h.fwd
  have hs : Function.Surjective ψ := MonoidHom.range_eq_top.1 (range_eq_top ha hb)
  refine le_antisymm h.card_le ?_
  rw [← card_J_eq h]
  exact Nat.card_le_card_of_surjective _ hs

theorem exists_psi : ∃ ψ : P →* J, Function.Bijective ψ ∧
    (∀ i < 7, ψ (gen i) ∈ H ∧ ψ (gen i) • Wset = Wset) ∧ ψ (gen 0) ^ 2 = 1 := by
  have := h.finite
  obtain ⟨ψ, hK, h2, ha, hb⟩ := h.fwd
  have hs : Function.Surjective ψ := MonoidHom.range_eq_top.1 (range_eq_top ha hb)
  refine ⟨ψ, hs.bijective_of_nat_card_le ?_, hK, h2⟩
  rw [card_P_eq h, card_J_eq h]

end CFSG.Sporadic.Th.Kernel

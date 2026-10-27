module

public import CFSG.Walter.W67.JR.R123
public import CFSG.Walter.W67.JR.R4

public section

namespace CFSG.Walter.W67

namespace JRGroup

variable {L : Type} [Group L] [Finite L] (h : JRGroup L)

theorem q_eq_three_of_le (hq3 : ¬ 3 < h.q) : h.q = 3 := by
  have hp3 : 3 ≤ h.p := by
    have := (Fact.out : h.p.Prime).two_le
    have := h.p_ne_two
    omega
  have : h.p ≤ h.p ^ h.f := by
    calc h.p = h.p ^ 1 := (pow_one _).symm
      _ ≤ h.p ^ h.f := Nat.pow_le_pow_right (by omega) h.f_pos
  change h.p ^ h.f = 3
  change ¬ 3 < h.p ^ h.f at hq3
  omega

theorem r1_to_r6
    (hJT : JTThreeHyp) (hq5 : h.q ≠ 5) :
    h.R1 ∧ h.R2 ∧ h.R3 ∧ h.R4 ∧ h.R5 ∧ h.R6 := by
  by_cases hq3 : 3 < h.q
  · have hq := h.five_lt_q hq5 hq3
    exact ⟨h.r1_of_five_lt hJT hq, h.r2_of_five_lt hq, h.r3 hJT hq5, h.r4 hJT hq5,
      h.r5 hJT hq5, h.r6 hJT hq5⟩
  · obtain ⟨h1, h2⟩ := h.r12_of_three (h.q_eq_three_of_le hq3)
    exact ⟨h1, h2, fun h => absurd h hq3, fun h => absurd h hq3, fun h => absurd h hq3,
      fun h => absurd h hq3⟩

end JRGroup

theorem rFacts_of_outCyclic
    (hOut : S_outCyclic_of_R) : S_rFacts_of := by
  intro hJT L _ _ hL hq5
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hL.r1_to_r6 hJT hq5
  exact ⟨h1, h2, h3, h4, h5, h6, fun hq3 => hOut hL (hL.five_lt_q hq5 hq3) hJT⟩

end CFSG.Walter.W67

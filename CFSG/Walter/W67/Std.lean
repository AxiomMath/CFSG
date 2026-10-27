module

public import CFSG.Walter.W67.Statements
import CFSG.Walter.W67.Prop24
import CFSG.Walter.W67.Lemma21
import CFSG.Walter.W67.Prop25
import CFSG.Walter.W67.Lemma26ii
import CFSG.Walter.W67.Cor32

public section

namespace CFSG.Walter.W67

variable {G : Type} [Group G] [Finite G]

theorem MinCE.three_lt_q
    (m : MinCE G) : 3 < m.q := by
  have hq3 : m.q ≠ 3 := fun h3 => by
    rcases case_of_q_eq_three G m.toHyp h3 with h | h
    · exact m.not_case1 h
    · exact m.not_case2 h
  have h2 := (Fact.out : m.p.Prime).two_le
  have hpq : m.p ≤ m.q := Nat.le_self_pow m.f_pos.ne' _
  have := m.p_ne_two
  omega

theorem Std.nonempty_of
    :
    S_Std_nonempty := by
  have h25 := prop_2_5
  have h26 := lemma_2_6_ii
  have h32 := cor_3_2
  intro G _ _ m hJ hR hM
  obtain ⟨fr⟩ := Frame.nonempty G m.toHyp
  have hq := m.three_lt_q
  have hperf := h25 G m hq hJ hR
  have hE : fr.E ≠ ⊥ := fun hE => m.not_case2 (case2_of_E_eq_bot G m.toHyp fr hperf hE)
  have hF := h32 G m fr hq hperf hJ hR hM
  classical
  let L : Subgroup G → Subgroup G := fun X => if hX : X ≤ fr.E ∧ X ≠ ⊥ then
    Classical.choose (h26 G m fr hq hperf hJ hR hM hX.1 hX.2) else ⊥
  refine ⟨⟨m, fr, hq, hperf, hE, hF, L, fun X hXE hX => ?_⟩, rfl⟩
  simp only [L, dite_eq_left (And.intro hXE hX)]
  exact Classical.choose_spec (h26 G m fr hq hperf hJ hR hM hXE hX)

theorem Std.nonempty :
    S_Std_nonempty := Std.nonempty_of

end CFSG.Walter.W67

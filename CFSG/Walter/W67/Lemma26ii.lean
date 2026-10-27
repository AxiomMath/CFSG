module

import CFSG.Walter.W67.W2Lemma26B
import CFSG.Walter.W67.W2Lemma26C
public import CFSG.Walter.W67.Interface

public section

namespace CFSG.Walter.W67

theorem lemma_2_6_ii :
    ∀ (G : Type) [Group G] [Finite G] (m : MinCE G) (fr : Frame m.toHyp), 3 < m.q → commutator G = ⊤ →
      JFacts → RFacts → RMult → ∀ {X : Subgroup G}, X ≤ fr.E → X ≠ ⊥ →
      ∃ L : Subgroup G, LSpec m.toHyp fr X L := by
  intro G _ _ m fr hq hperf hJ hR hM X hXE hX
  have hidx := index_ne_two_of_perfect hperf
  have hr3 : 3 ≤ m.p ^ (m.f / m.eX X) := by
    have h2 := (Fact.out : m.p.Prime).two_le
    have := m.p_ne_two
    have hle : m.p ≤ m.p ^ (m.f / m.eX X) := Nat.le_self_pow (fr.div_eX_pos hXE).ne' _
    omega
  rcases (show m.p ^ (m.f / m.eX X) = 3 ∨ 3 < m.p ^ (m.f / m.eX X) by omega) with h3 | h3
  · exact fr.lspec_of_three hidx hXE hX h3
  · by_cases htop : Subgroup.centralizer (X : Set G) = ⊤
    · exact (m.false_of_centralizer_eq_top fr hq hperf hJ hM hXE hX htop).elim
    · exact m.lspec_of_lt fr hJ hR hidx hXE hX h3 htop

end CFSG.Walter.W67

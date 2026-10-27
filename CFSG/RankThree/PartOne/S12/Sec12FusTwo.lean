module

public import CFSG.RankThree.PartOne.S12.Sec12Fus

public section

namespace CFSG.RankThree.PartOne

open CFSG CFSG.Assembly CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.GroupTheory

theorem node1213Two_of_inputs (h124 : Node124) : Node1213Two := by
  classical
  intro G _ _ p A c L E ctx b K I X P Q hL hC hne hcomm hmax
  have h := ctx.hyp
  have hp := h.prime
  have : Fact p.Prime := ⟨hp⟩
  have hAel := h.A_elem
  obtain ⟨hbA, hbL, hb1⟩ := hL.b_mem
  refine ⟨hmax.1.1.1, fun hI1 => ?_⟩
  have hb' : Sec12Hyp G p A b I E :=
    ⟨h.setup, hbA, hb1, ⟨⟨hmax.1, hI1⟩, hmax.2⟩, h.E_elem, h.E_le, h.E_max⟩
  obtain ⟨h124a, h124b⟩ := h124 G p A b I E hb'
  have hfix : pCoreFixed p E = E ⊓ L := ctx.ten.1
  have hcard : Nat.card E = p * Nat.card ↥(E ⊓ L) := ctx.ten.2.1
  have hbE : b ∈ E := h.A_le_E hbA
  have hbB : b ∈ pCoreFixed p E := hfix ▸ ⟨hbE, hbL⟩
  have hinvI : torusInvariant E I (pCoreFixed p E) := fun w hw =>
    torusInvariant_pCoreFixed p E w ⟨Subgroup.mem_top w, hw.2⟩
  have hne0 : pCoreFixed p E ≠ ⊥ := fun h0 => hb1 (by
    have := h0 ▸ hbB
    simpa using this)
  rcases h124a (pCoreFixed p E) (pCoreFixed_le p E) hinvI hne0 (pCoreFixed_ne_top ctx.core) with
    hB | hB
  ·
    have hbord : orderOf b = p := orderOf_eq_prime
      (CFSG.elemPow_eq_one_of_isElementaryAbelian (p := p) (A := A) b hbA) hb1
    have hBcard : Nat.card ↥(E ⊓ L) = p := by
      rw [← hfix, hB, Nat.card_zpowers, hbord]
    rw [hBcard] at hcard
    have h3 := Nat.le_of_dvd Nat.card_pos h.pow_three_dvd_card_E
    rw [hcard] at h3
    have h2 := hp.two_le
    nlinarith [Nat.mul_pos hp.pos hp.pos]
  · rcases h124b with ⟨-, hdisj⟩ | ⟨-, hEE⟩
    · have hmem : b ∈ Subgroup.zpowers b ⊓ ⁅E, I ⊓ torusNormalizer E⁆ :=
        ⟨Subgroup.mem_zpowers b, hB ▸ hbB⟩
      rw [hdisj, Subgroup.mem_bot] at hmem
      exact hb1 hmem
    · exact pCoreFixed_ne_top ctx.core (hB.trans hEE)

end CFSG.RankThree.PartOne

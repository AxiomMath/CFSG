module

public import CFSG.Quasithin.Vol2.GoldschmidtF431U42AutP1Lat

public section

namespace CFSG.Quasithin.H13.F431.U42Aut

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Open

theorem sup_P1h_P2h :
    P1h ⊔ P2h = ⊤ := by
  have hB : Bh ≤ P1h ⊔ P2h := Bh_le_P1h.trans le_sup_left
  rcases lattice_Bh hB with h | h | h | h
  · exact absurd (le_sup_left.trans (h.le.trans Bh_le_P2h)) P1h_not_le_P2h
  · exact absurd (le_sup_right.trans h.le) P2h_not_le_P1h
  · exact absurd (le_sup_left.trans h.le) P1h_not_le_P2h
  · exact h

theorem eq_bot_of_normal
    (N : Subgroup Ah) [N.Normal] (h1 : N ⊓ P1h = ⊥) (h2 : N ⊓ P2h = ⊥) : N = ⊥ := by
  have hle1 : N ≤ P1h → N = ⊥ := fun h =>
    eq_bot_iff.2 fun x hx => by
      have : x ∈ N ⊓ P1h := ⟨hx, h hx⟩
      rwa [h1] at this
  have hle2 : N ≤ P2h → N = ⊥ := fun h =>
    eq_bot_iff.2 fun x hx => by
      have : x ∈ N ⊓ P2h := ⟨hx, h hx⟩
      rwa [h2] at this
  rcases lattice_Bh (le_sup_right : Bh ≤ N ⊔ Bh) with h | h | h | h
  · exact hle1 ((le_sup_left.trans h.le).trans Bh_le_P1h)
  · exact hle1 (le_sup_left.trans h.le)
  · exact hle2 (le_sup_left.trans h.le)
  ·
    exfalso
    have hNP : Function.Injective fun n : N => (QuotientGroup.mk (n : Ah) : Ah ⧸ P1h) := by
      intro n n' hnn
      have hmem : (n : Ah)⁻¹ * n' ∈ P1h := QuotientGroup.eq.1 hnn
      have hN : (n : Ah)⁻¹ * n' ∈ N := N.mul_mem (N.inv_mem n.2) n'.2
      have : (n : Ah)⁻¹ * n' ∈ N ⊓ P1h := ⟨hN, hmem⟩
      rw [h1, Subgroup.mem_bot] at this
      exact Subtype.ext (inv_mul_eq_one.1 this)
    have hN45 : Nat.card N ≤ 45 := by
      have h45 : Nat.card (Ah ⧸ P1h) = 45 := by
        have := Subgroup.card_mul_index P1h
        rw [card_P1h, card_A] at this
        change Nat.card (Ah ⧸ P1h) = 45 at *
        simp only [Subgroup.index] at this
        omega
      exact (Nat.card_le_card_of_injective _ hNP).trans h45.le
    have hsurj : Function.Surjective fun p : N × Bh => (p.1 : Ah) * (p.2 : Ah) := by
      intro a
      have ha : a ∈ (↑(N ⊔ Bh) : Set Ah) := by rw [h]; exact Subgroup.mem_top a
      rw [Subgroup.normal_mul] at ha
      obtain ⟨n, hn, b, hb, rfl⟩ := ha
      exact ⟨(⟨n, hn⟩, ⟨b, hb⟩), rfl⟩
    have := Nat.card_le_card_of_surjective _ hsurj
    rw [Nat.card_prod, card_Bh, card_A] at this
    omega

end CFSG.Quasithin.H13.F431.U42Aut

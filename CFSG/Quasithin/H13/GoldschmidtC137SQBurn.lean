module

public import Mathlib.GroupTheory.Transfer

public section

namespace CFSG.Quasithin.H13.U3.GC137.SQ

theorem false_of_normalizer_le_centralizer {S : Type} [Group S] [Finite S] [IsSimpleGroup S]
    {p : ℕ} [Fact p.Prime] (P : Sylow p S) (hP1 : 1 < Nat.card P) (hPS : Nat.card P < Nat.card S)
    (h : Subgroup.normalizer (P : Set S) ≤ Subgroup.centralizer (P : Set S)) : False := by
  have hc := MonoidHom.ker_transferSylow_isComplement' P h
  have hmul := hc.card_mul_card
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (MonoidHom.transferSylow P h).ker with hb | ht
  · rw [hb, Subgroup.card_bot] at hmul
    omega
  · rw [ht, Subgroup.card_top] at hmul
    have : 0 < Nat.card S := Nat.card_pos
    nlinarith

end CFSG.Quasithin.H13.U3.GC137.SQ

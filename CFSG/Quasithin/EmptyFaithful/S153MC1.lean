module

public import CFSG.Quasithin.EmptyFaithful.S153MElt

public section

namespace CFSG.Quasithin

namespace S153M

private theorem card_le_card_inf_mul_index {V : Type} [CommGroup V] [Finite V] (F U : Subgroup V) :
    Nat.card ↥F ≤ Nat.card ↥(F ⊓ U) * U.index := by
  have h1 := Subgroup.card_mul_index F
  have h2 := Subgroup.card_mul_index (F ⊓ U)
  have h3 : (F ⊓ U).index ≤ F.index * U.index := Subgroup.index_inf_le
  have hpos : 0 < F.index := Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
  have h4 : Nat.card ↥F * F.index ≤ Nat.card ↥(F ⊓ U) * U.index * F.index := by
    calc Nat.card ↥F * F.index = Nat.card ↥(F ⊓ U) * (F ⊓ U).index := h1.trans h2.symm
      _ ≤ Nat.card ↥(F ⊓ U) * (F.index * U.index) := Nat.mul_le_mul_left _ h3
      _ = Nat.card ↥(F ⊓ U) * U.index * F.index := by ring
  exact Nat.le_of_mul_le_mul_right h4 hpos

theorem false_of_strong_natural_sl2 {V : Type} [CommGroup V] [Finite V] (hV : ∀ v : V, v ^ 2 = 1)
    {X L : Subgroup (MulAut V)} (hJ : ffJ X = L) {m : ℕ}
    (hnat : BinaryNaturalSL L (commV L) (fixV L ⊓ commV L) 2 m) (hstrong : IsStrongFFModule X) :
    False := by
  obtain ⟨A, hAX, hA1, hA2, hlt⟩ := hstrong
  have hAA : IsA2 X A := ⟨hAX, hA1, hA2⟩
  obtain ⟨B, -, hB, hBr⟩ := B1_4_4_lt hV hAA ((rAV_lt_one_iff hV hAA).2 hlt)
  have hlt' : Nat.card V < Nat.card B * Nat.card (fixV B) := (rAV_lt_one_iff hV hB.isA2).1 hBr
  have hBL : B ≤ L := hJ ▸ B6.le_ffJ hB
  have h1 := not_strong_of_natural_sl2 hV hnat hBL hB.2.1 hB.2.2.1
  have h2 := card_le_card_inf_mul_index (fixV B) (commV L)
  have h3 : Nat.card ↥(commV L) * (commV L).index = Nat.card V := Subgroup.card_mul_index (commV L)
  have h4 : Nat.card ↥B * Nat.card ↥(fixV B) ≤ Nat.card V := by
    calc Nat.card ↥B * Nat.card ↥(fixV B)
        ≤ Nat.card ↥B * (Nat.card ↥(fixV B ⊓ commV L) * (commV L).index) :=
          Nat.mul_le_mul_left _ h2
      _ = (Nat.card ↥B * Nat.card ↥(fixV B ⊓ commV L)) * (commV L).index := by ring
      _ ≤ Nat.card ↥(commV L) * (commV L).index := Nat.mul_le_mul_right _ h1
      _ = Nat.card V := h3
  omega

end S153M

end CFSG.Quasithin

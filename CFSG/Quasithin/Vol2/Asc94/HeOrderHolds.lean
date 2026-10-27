module

public import CFSG.Quasithin.Vol2.Asc94.HeNoE16
public import CFSG.Quasithin.H13.LocDblOddHe
public import CFSG.Quasithin.H13.LocDblHe

public section

namespace CFSG.Quasithin.A94

open CFSG.Quasithin.H13.LocDbl

theorem he_order_holds :
    He_order := by
  intro X hX
  by_contra hne
  have hHe : Nat.card CFSG.Blueprint.NativeSporadic.He = 322560 * 12495 := by
    rw [CFSG.Sporadic.He.fam_he_order.1]
  obtain ⟨c, hc0⟩ := hX
  have hc : Nat.card ↥X = 322560 * c := by rw [hc0]; ring
  have h1 := X.card_mul_index
  rw [hc, hHe] at h1
  have h2 : c * X.index = 12495 := by
    have h3 : 322560 * (c * X.index) = 322560 * 12495 := by rw [← h1]; ring
    exact Nat.eq_of_mul_eq_mul_left (by norm_num) h3
  have hodd : ¬ 2 ∣ X.index := by
    intro h2dvd
    have : 2 ∣ 12495 := h2 ▸ Dvd.dvd.mul_left h2dvd c
    omega
  obtain ⟨N, hN, hd⟩ := oddIndexBound_He X hodd hne
  have hpos : 0 < Nat.card X := Nat.card_pos
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hN
  have hle : Nat.card X ≤ N := Nat.le_of_dvd (by rcases hN with rfl | rfl | rfl <;> norm_num) hd
  have hbig : 322560 ≤ Nat.card X := by
    rw [hc]
    have : 0 < c := Nat.pos_of_ne_zero fun h0 => by rw [hc, h0] at hpos; omega
    omega
  rcases hN with rfl | rfl | rfl <;> omega

end CFSG.Quasithin.A94

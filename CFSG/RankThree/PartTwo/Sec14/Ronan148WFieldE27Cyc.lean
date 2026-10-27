module

public import Mathlib.Data.Nat.Totient
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.GroupTheory.SpecificGroups.Cyclic.Basic
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific

public section

namespace CFSG.RankThree.PartTwo.Sec14.Ronan148W

theorem exists_cube_iff_pow_eq_one {H : Type*} [Group H] [Finite H] [IsCyclic H] {m : ℕ}
    (hm : Nat.card H = 3 * m) (x : H) : (∃ c : H, c ^ 3 = x) ↔ x ^ m = 1 := by
  constructor
  · rintro ⟨c, rfl⟩
    rw [← pow_mul, ← hm]
    exact pow_card_eq_one'
  · intro hx
    have hpos : 0 < Nat.card H := Nat.card_pos
    have hm0 : 0 < m := by
      rw [hm] at hpos
      omega
    obtain ⟨g, hg⟩ := IsCyclic.exists_monoid_generator (α := H)
    have hord : orderOf g = 3 * m := (orderOf_eq_card_of_forall_mem_powers hg).trans hm
    obtain ⟨k, rfl⟩ := (Submonoid.mem_powers_iff _ _).mp (hg x)
    have hdvd : orderOf g ∣ k * m := by
      rw [orderOf_dvd_iff_pow_eq_one, pow_mul]
      exact hx
    rw [hord] at hdvd
    obtain ⟨t, rfl⟩ := Nat.dvd_of_mul_dvd_mul_right hm0 hdvd
    exact ⟨g ^ t, by rw [← pow_mul, mul_comm t 3]⟩

theorem pow_exists_cube_iff_three_dvd {H : Type*} [Group H] [Finite H] [IsCyclic H] {m : ℕ}
    (hm : Nat.card H = 3 * m) (hm0 : 0 < m) {g : H} (hg : ∀ y : H, y ∈ Submonoid.powers g)
    (k : ℕ) : (∃ c : H, c ^ 3 = g ^ k) ↔ 3 ∣ k := by
  rw [exists_cube_iff_pow_eq_one hm (g ^ k), ← pow_mul, ← orderOf_dvd_iff_pow_eq_one,
    orderOf_eq_card_of_forall_mem_powers hg, hm]
  constructor
  · intro h
    exact Nat.dvd_of_mul_dvd_mul_right hm0 h
  · rintro ⟨c, rfl⟩
    exact ⟨c, by ring⟩

theorem cube_mul_or_cube_mul_sq {H : Type*} [CommGroup H] [Finite H] [IsCyclic H]
    (h3 : 3 ∣ Nat.card H) {a b : H} (ha : ¬ ∃ c : H, c ^ 3 = a) (hb : ¬ ∃ c : H, c ^ 3 = b) :
    (∃ c : H, c ^ 3 = a * b) ∨ (∃ c : H, c ^ 3 = a * b ^ 2) := by
  obtain ⟨m, hm⟩ := h3
  have hpos : 0 < Nat.card H := Nat.card_pos
  have hm0 : 0 < m := by
    rw [hm] at hpos
    omega
  obtain ⟨g, hg⟩ := IsCyclic.exists_monoid_generator (α := H)
  obtain ⟨i, rfl⟩ := (Submonoid.mem_powers_iff _ _).mp (hg a)
  obtain ⟨j, rfl⟩ := (Submonoid.mem_powers_iff _ _).mp (hg b)
  have hi : ¬ 3 ∣ i := fun h => ha ((pow_exists_cube_iff_three_dvd hm hm0 hg i).mpr h)
  have hj : ¬ 3 ∣ j := fun h => hb ((pow_exists_cube_iff_three_dvd hm hm0 hg j).mpr h)
  have hi3 : i % 3 = 1 ∨ i % 3 = 2 := by omega
  have hj3 : j % 3 = 1 ∨ j % 3 = 2 := by omega
  clear hi hj
  rcases hi3 with hi3 | hi3 <;> rcases hj3 with hj3 | hj3
  · right
    rw [← pow_mul, ← pow_add]
    exact (pow_exists_cube_iff_three_dvd hm hm0 hg (i + j * 2)).mpr (by omega)
  · left
    rw [← pow_add]
    exact (pow_exists_cube_iff_three_dvd hm hm0 hg (i + j)).mpr (by omega)
  · left
    rw [← pow_add]
    exact (pow_exists_cube_iff_three_dvd hm hm0 hg (i + j)).mpr (by omega)
  · right
    rw [← pow_mul, ← pow_add]
    exact (pow_exists_cube_iff_three_dvd hm hm0 hg (i + j * 2)).mpr (by omega)

end CFSG.RankThree.PartTwo.Sec14.Ronan148W

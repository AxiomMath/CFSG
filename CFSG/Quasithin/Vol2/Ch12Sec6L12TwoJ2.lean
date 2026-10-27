module

public import CFSG.Quasithin.Vol2.Ch12Sec6L12A6Num
public import CFSG.Quasithin.H13.LocDblOddJ2

public section

namespace CFSG.Quasithin.H13.K1262Two

open CFSG.Open CFSG.Blueprint

theorem a6LocJ2_holds :
    A6LocJ2 := by
  intro X _ _ ⟨e⟩ Y F h
  by_contra hF
  have hF16 : 16 ≤ Nat.card ↥F := Nat.le_of_not_lt hF
  have hX : Nat.card X = 2 ^ 7 * 4725 := by
    rw [Nat.card_congr e.toEquiv, CFSG.Sporadic.J2.card_J2]
    norm_num
  obtain ⟨j, hY, hFj⟩ := a6Config_card h
  have hYdvd : 360 * 2 ^ j ∣ 2 ^ 7 * 4725 := by
    rw [← hY, ← hX]
    exact Subgroup.card_subgroup_dvd_card Y
  have hj : j + 3 ≤ 7 := a6Config_card_le_of_dvd (by decide) hYdvd
  have hFle : Nat.card ↥F ≤ 2 ^ j := Nat.le_of_dvd (by positivity) hFj
  have hj4 : 4 ≤ j := by
    by_contra hlt
    have : 2 ^ j ≤ 2 ^ 3 := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have hj' : j = 4 := by omega
  subst hj'
  have hY5760 : Nat.card ↥Y = 5760 := by rw [hY]; norm_num
  set Y' : Subgroup NativeSporadic.J2 := Y.map e.toMonoidHom with hY'
  have hcard' : Nat.card ↥Y' = 5760 := by
    rw [hY', Subgroup.card_map_of_injective e.injective]
    exact hY5760
  have hJ2 : Nat.card NativeSporadic.J2 = 604800 := CFSG.Sporadic.J2.card_J2
  have hidx : Y'.index = 105 := by
    have h1 := Y'.card_mul_index
    rw [hcard', hJ2] at h1
    omega
  have hne : Y' ≠ ⊤ := by
    intro htop
    have h1 := hcard'
    rw [htop, Subgroup.card_top, hJ2] at h1
    omega
  obtain ⟨N, hN, hd⟩ :=
    CFSG.Quasithin.H13.LocDbl.oddIndexBound_J2 Y' (by rw [hidx]; decide) hne
  rw [hcard'] at hd
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hN
  rcases hN with rfl | rfl <;> exact absurd (Nat.le_of_dvd (by norm_num) hd) (by norm_num)

end CFSG.Quasithin.H13.K1262Two

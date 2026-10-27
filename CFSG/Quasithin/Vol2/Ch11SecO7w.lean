module

public import CFSG.Quasithin.EmptyFaithful.T1515eE
public import CFSG.Quasithin.Vol2.Ch11SecO7h
public import CFSG.Quasithin.Vol2.Ch11SecO7u

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecE.C10KH

open CFSG.Open CFSG.Blueprint

theorem l2two_ne_list3 {N : ℕ} (hN : N ∈ list3Orders) (m : ℕ) : 2 ^ m * ((2 ^ m) ^ 2 - 1) ≠ N := by
  have hA : ∀ N ∈ list3Orders, ¬ 2 ^ 22 ∣ N := by decide
  have hchk : ∀ N ∈ list3Orders, ∀ m ≤ 21, 2 ^ m * ((2 ^ m) ^ 2 - 1) ≠ N := by decide +kernel
  exact fam_ne_of_bound (A := 21) (hA N hN) le_rfl
    (fun m => by rw [one_mul]; exact dvd_mul_right _ _) (hchk N hN) m

theorem psl2_ne_list3 {N p : ℕ} (hN : N ∈ list3Orders) (hp : p.Prime) :
    p * (p ^ 2 - 1) ≠ N * 2 := by
  simp only [list3Orders, Finset.mem_insert, Finset.mem_singleton] at hN
  rcases hN with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact cube_sub_ne (k := 17) (by norm_num) (by norm_num) (by norm_num)
  · exact cube_sub_ne (k := 24) (by norm_num) (by norm_num) (by norm_num)
  · intro h
    have := eq_of_cube_sub hp.one_lt.le (by norm_num : 1 ≤ 25) (h.trans (by norm_num))
    subst this
    norm_num at hp
  · exact cube_sub_ne (k := 90) (by norm_num) (by norm_num) (by norm_num)
  · exact cube_sub_ne (k := 91) (by norm_num) (by norm_num) (by norm_num)
  · exact cube_sub_ne (k := 63) (by norm_num) (by norm_num) (by norm_num)
  · exact cube_sub_ne (k := 96) (by norm_num) (by norm_num) (by norm_num)
  · exact cube_sub_ne (k := 138) (by norm_num) (by norm_num) (by norm_num)
  · exact cube_sub_ne (k := 273) (by norm_num) (by norm_num) (by norm_num)
  · exact cube_sub_ne (k := 70) (by norm_num) (by norm_num) (by norm_num)
  · exact cube_sub_ne (k := 106) (by norm_num) (by norm_num) (by norm_num)
  · exact cube_sub_ne (k := 5577965) (by norm_num) (by norm_num) (by norm_num)
  · exact cube_sub_ne (k := 445) (by norm_num) (by norm_num) (by norm_num)
  · exact cube_sub_ne (k := 6633) (by norm_num) (by norm_num) (by norm_num)


variable {X : Type} [Group X] {n : ℕ}

theorem not_l2two (h : InLists X n) (m : ℕ) (hc : Nat.card X = 2 ^ m * ((2 ^ m) ^ 2 - 1)) :
    False := by
  obtain ⟨hn, h2 | ⟨rfl, h3⟩, hA, hE⟩ := h
  · exact list2_ne_l2two hn h2 m hc
  · rcases list3_cases h3 hA hE with ⟨p, hp, hp11, h8, hL⟩ | hm
    · have hn8 := not_eight_dvd_psl2 h8 (card_mul_two_of_psl2 hp (by omega) hL)
      have hge := list3_ge h3 hA hE
      rw [hc] at hn8 hge
      rcases Nat.lt_or_ge m 3 with hm3 | hm3
      · interval_cases m <;> norm_num at hge
      · exact hn8 ((Nat.pow_dvd_pow 2 hm3).mul_right _)
    · exact l2two_ne_list3 hm m hc.symm

theorem psl2_case (h : InLists X n) {r : ℕ} (hr : r.Prime) (hr5 : 5 ≤ r)
    (hc : Nat.card X * 2 = r * (r ^ 2 - 1)) : n = 2 ∧ 11 ≤ r := by
  obtain ⟨hn, h2 | ⟨rfl, h3⟩, hA, hE⟩ := h
  · exact absurd (by rw [hc, one_mul])
      (list2_ne_artin hn h2 (c := 1) odd_one (hr.odd_of_ne_two (by omega)) (by omega))
  · refine ⟨rfl, ?_⟩
    rcases list3_cases h3 hA hE with ⟨p, hp, hp11, -, hL⟩ | hm
    · have hp2 := card_mul_two_of_psl2 hp (by omega) hL
      have hrp : r = p := eq_of_cube_sub (by omega) (by omega) (hc.symm.trans hp2)
      omega
    · exact absurd hc.symm (psl2_ne_list3 hm hr)

theorem not_l42 (h : InLists X n) (h42 : IsPSL 4 2 1 X) : False := by
  have hc := card_of_isPSL421 h42
  obtain ⟨hn, h2 | ⟨rfl, h3⟩, hA, hE⟩ := h
  · exact CFSG.Quasithin.l34NotL42Fact1515e_of_cert X (list2_20160 hn h2 hc) h42
  · rcases list3_cases h3 hA hE with ⟨p, hp, hp11, -, hL⟩ | hm
    · have := card_mul_two_of_psl2 hp (by omega) hL
      rw [hc] at this
      exact cube_sub_ne (k := 34) (by norm_num) (by norm_num) (by norm_num) this.symm
    · rw [hc] at hm
      simp [list3Orders] at hm

end CFSG.Quasithin.Vol2.Ch11.SecE.C10KH

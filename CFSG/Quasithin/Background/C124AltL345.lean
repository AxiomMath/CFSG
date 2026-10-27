module

public import CFSG.Quasithin.Background.B5NonInputs
public import CFSG.LocalAnalysis.SectionRank.OddCover.DegreeThree

public section

namespace CFSG.Quasithin.C124

open CFSG.Open CFSG.Assembly.LowTwoRank

theorem card_alt_five_six_seven {m : ℕ} (hm : m = 5 ∨ m = 6 ∨ m = 7) :
    Nat.card (alternatingGroup (Fin m)) = 60 ∨ Nat.card (alternatingGroup (Fin m)) = 360 ∨
      Nat.card (alternatingGroup (Fin m)) = 2520 := by
  have : Nontrivial (Fin m) := Fin.nontrivial_iff_two_le.2 (by omega)
  rw [nat_card_alternatingGroup, Nat.card_fin]
  rcases hm with rfl | rfl | rfl
  · left; decide
  · right; left; decide
  · right; right; decide

theorem card_statedSL_four_two {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2) :
    Nat.card (StatedSL 4 K) = 20160 :=
  CFSG.Open.StatedAPI.card_statedSL_four_of_card_eq_two hK

theorem card_statedSL_five_two {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2) :
    Nat.card (StatedSL 5 K) = 9999360 :=
  CFSG.Open.StatedAPI.card_statedSL_five_of_card_eq_two hK

theorem not_isL345Type_of_alt {Γ : Type} [Group Γ] [Finite Γ] {m : ℕ}
    (hm : m = 5 ∨ m = 6 ∨ m = 7) {z : ℕ} (hz : Odd z)
    (hcard : Nat.card Γ = Nat.card (alternatingGroup (Fin m)) * z) : ¬ IsL345Type Γ := by
  obtain ⟨k, hk⟩ := hz
  have hA := card_alt_five_six_seven hm
  rintro (⟨n, K, _, _, hK, ⟨e⟩⟩ | ⟨K, _, _, hK, ⟨e⟩⟩ | ⟨K, _, _, hK, ⟨e⟩⟩)
  · have h3 := Nat.card_congr e.toEquiv
    rw [CFSG.SectionRank.OddCover.card_statedSL_three, hK] at h3
    have hn : 1 ≤ n := by
      by_contra h0
      have hn0 : n = 0 := by omega
      subst hn0
      have := Finite.one_lt_card (α := K)
      rw [hK] at this
      simp at this
    rcases Nat.lt_or_ge n 2 with hn2 | hn2
    · have hn1 : n = 1 := by omega
      subst hn1
      norm_num at h3
      rcases hA with hA | hA | hA <;> rw [hcard, hA] at h3 <;> omega
    · have h64 : 64 ∣ Nat.card Γ := by
        rw [h3]
        have h6 : 64 ∣ (2 ^ n) ^ 3 := by
          rw [← pow_mul]
          calc 64 = 2 ^ 6 := by norm_num
            _ ∣ 2 ^ (n * 3) := pow_dvd_pow 2 (by omega)
        exact Dvd.dvd.mul_right (Dvd.dvd.mul_right h6 _) _
      rcases hA with hA | hA | hA <;> rw [hcard, hA] at h64 <;> omega
  · have h4 := Nat.card_congr e.toEquiv
    rw [card_statedSL_four_two hK] at h4
    rcases hA with hA | hA | hA <;> rw [hcard, hA] at h4 <;> omega
  · have h5 := Nat.card_congr e.toEquiv
    rw [card_statedSL_five_two hK] at h5
    rcases hA with hA | hA | hA <;> rw [hcard, hA] at h5 <;> omega

end CFSG.Quasithin.C124

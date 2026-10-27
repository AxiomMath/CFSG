module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtA312RuAct

public section

namespace CFSG.Quasithin.A312Ru

theorem isSolvable_of_card_seven_mul {K : Type} [Group K] [Finite K] {m : ℕ}
    (hm : m = 6 ∨ m = 12) (hK : Nat.card K = 7 * m) : Group.IsSolvable K := by
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  obtain ⟨P⟩ : Nonempty (Sylow 7 K) := inferInstance
  have hm0 : ¬ 7 ∣ m := by rcases hm with rfl | rfl <;> norm_num
  have hP : Nat.card P = 7 := by
    rw [Sylow.card_eq_multiplicity, hK, Nat.factorization_mul (by norm_num)
      (by rcases hm with rfl | rfl <;> norm_num), Finsupp.add_apply,
      Nat.Prime.factorization_self (by norm_num), Nat.factorization_eq_zero_of_not_dvd hm0]
    norm_num
  have hidx : (P : Subgroup K).index = m := by
    have h := (P : Subgroup K).card_mul_index
    rw [hP, hK] at h
    exact Nat.eq_of_mul_eq_mul_left (by norm_num : 0 < 7) h
  have hmod := card_sylow_modEq_one 7 K
  have hdvd : Nat.card (Sylow 7 K) ∣ m := by
    have h := P.card_dvd_index
    rwa [hidx] at h
  have hn1 : Nat.card (Sylow 7 K) = 1 := by
    have hle := Nat.le_of_dvd (by rcases hm with rfl | rfl <;> norm_num) hdvd
    have hpos : 0 < Nat.card (Sylow 7 K) := Nat.card_pos
    unfold Nat.ModEq at hmod
    rcases hm with rfl | rfl <;>
      (interval_cases h : Nat.card (Sylow 7 K) <;> first | rfl | omega)
  have hsub : Subsingleton (Sylow 7 K) := (Nat.card_eq_one_iff_unique.mp hn1).1
  have hnormal : (P : Subgroup K).Normal := Sylow.normal_of_subsingleton P
  have hPs : Group.IsSolvable (P : Subgroup K) :=
    isSolvable_of_card_pq (p := 7) (q := 2) (a := 1) (b := 0) (by norm_num) Nat.prime_two
      (by norm_num) (by rw [hP]; norm_num)
  have hQcard : Nat.card (K ⧸ (P : Subgroup K)) = m := by
    rw [← hidx]; rfl
  have hQs : Group.IsSolvable (K ⧸ (P : Subgroup K)) := by
    rcases hm with rfl | rfl
    · exact isSolvable_of_card_pq Nat.prime_two Nat.prime_three (by norm_num) (a := 1) (b := 1)
        (by rw [hQcard]; norm_num)
    · exact isSolvable_of_card_pq Nat.prime_two Nat.prime_three (by norm_num) (a := 2) (b := 1)
        (by rw [hQcard]; norm_num)
  exact Group.isSolvable_of_ker_le_range (P : Subgroup K).subtype
    (QuotientGroup.mk' (P : Subgroup K)) (by rw [QuotientGroup.ker_mk', Subgroup.range_subtype])

theorem isSolvable_of_card_dvd_168 {K : Type} [Group K] [Finite K] (hd : Nat.card K ∣ 168)
    (hlt : Nat.card K < 168) : Group.IsSolvable K := by
  have hpos : 0 < Nat.card K := Nat.card_pos
  obtain ⟨n, hn⟩ : ∃ n, Nat.card K = n := ⟨_, rfl⟩
  rw [hn] at hd hlt hpos
  have hmem : n ∈ Nat.divisors 168 := Nat.mem_divisors.mpr ⟨hd, by norm_num⟩
  have hdiv : Nat.divisors 168 =
      {1, 2, 3, 4, 6, 7, 8, 12, 14, 21, 24, 28, 42, 56, 84, 168} := by decide
  rw [hdiv] at hmem
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
  have p2 := Nat.prime_two
  have p3 := Nat.prime_three
  have p7 : Nat.Prime 7 := by norm_num
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl
  · exact isSolvable_of_card_pq p2 p3 (by norm_num) (a := 0) (b := 0) (by rw [hn]; norm_num)
  · exact isSolvable_of_card_pq p2 p3 (by norm_num) (a := 1) (b := 0) (by rw [hn]; norm_num)
  · exact isSolvable_of_card_pq p2 p3 (by norm_num) (a := 0) (b := 1) (by rw [hn]; norm_num)
  · exact isSolvable_of_card_pq p2 p3 (by norm_num) (a := 2) (b := 0) (by rw [hn]; norm_num)
  · exact isSolvable_of_card_pq p2 p3 (by norm_num) (a := 1) (b := 1) (by rw [hn]; norm_num)
  · exact isSolvable_of_card_pq p2 p7 (by norm_num) (a := 0) (b := 1) (by rw [hn]; norm_num)
  · exact isSolvable_of_card_pq p2 p3 (by norm_num) (a := 3) (b := 0) (by rw [hn]; norm_num)
  · exact isSolvable_of_card_pq p2 p3 (by norm_num) (a := 2) (b := 1) (by rw [hn]; norm_num)
  · exact isSolvable_of_card_pq p2 p7 (by norm_num) (a := 1) (b := 1) (by rw [hn]; norm_num)
  · exact isSolvable_of_card_pq p3 p7 (by norm_num) (a := 1) (b := 1) (by rw [hn]; norm_num)
  · exact isSolvable_of_card_pq p2 p3 (by norm_num) (a := 3) (b := 1) (by rw [hn]; norm_num)
  · exact isSolvable_of_card_pq p2 p7 (by norm_num) (a := 2) (b := 1) (by rw [hn]; norm_num)
  · exact isSolvable_of_card_seven_mul (m := 6) (Or.inl rfl) (by rw [hn])
  · exact isSolvable_of_card_pq p2 p7 (by norm_num) (a := 3) (b := 1) (by rw [hn]; norm_num)
  · exact isSolvable_of_card_seven_mul (m := 12) (Or.inr rfl) (by rw [hn])
  · exact absurd hlt (lt_irrefl _)

theorem isSimpleGroup_of_card_168 {G : Type} [Group G] [Finite G] (hcard : Nat.card G = 168)
    (hns : ¬ Group.IsSolvable G) : IsSimpleGroup G := by
  have hnt : Nontrivial G := Finite.one_lt_card_iff_nontrivial.mp (by rw [hcard]; norm_num)
  refine { toNontrivial := hnt, eq_bot_or_eq_top_of_normal := fun N hN => ?_ }
  by_contra hne
  push Not at hne
  obtain ⟨h1, h2⟩ := hne
  have hNdvd : Nat.card N ∣ 168 := hcard ▸ Subgroup.card_subgroup_dvd_card N
  have hNlt : Nat.card N < 168 := by
    by_contra hge
    push Not at hge
    have : Nat.card N = 168 := le_antisymm (Nat.le_of_dvd (by norm_num) hNdvd) hge
    exact h2 (Subgroup.eq_top_of_card_eq N (by rw [this, hcard]))
  have hNs : Group.IsSolvable N := isSolvable_of_card_dvd_168 hNdvd hNlt
  have hQdvd : Nat.card (G ⧸ N) ∣ 168 := hcard ▸ Subgroup.card_quotient_dvd_card N
  have hQlt : Nat.card (G ⧸ N) < 168 := by
    have hmul := Subgroup.card_eq_card_quotient_mul_card_subgroup N
    have hN1 : 1 < Nat.card N := by
      by_contra hle
      push Not at hle
      have hpos : 0 < Nat.card N := Nat.card_pos
      exact h1 (Subgroup.eq_bot_of_card_eq N (by omega))
    have hQpos : 0 < Nat.card (G ⧸ N) := Nat.card_pos
    nlinarith
  have hQs : Group.IsSolvable (G ⧸ N) := isSolvable_of_card_dvd_168 hQdvd hQlt
  exact hns (Group.isSolvable_of_ker_le_range N.subtype (QuotientGroup.mk' N)
    (by rw [QuotientGroup.ker_mk', Subgroup.range_subtype]))

end CFSG.Quasithin.A312Ru

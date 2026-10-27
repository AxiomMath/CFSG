module

public import CFSG.Quasithin.Vol2.Ch10SecE9He
public import CFSG.RankThree.PartTwo.KFacts.KP7Suzuki

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecB

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13 CFSG.Quasithin CFSG.QuasithinUnique

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem card_lbar {L : Subgroup G} (hL : LBarL32 L) :
    Nat.card (↥L ⧸ CFSG.pCore 2 ↥L) = 168 := by
  obtain ⟨e⟩ := hL
  rw [Nat.card_congr e.toEquiv]
  exact card_Γ

theorem card_sl_two_ne {F : Type} [Field F] [Finite F] {n : ℕ} (hn : 1 < n)
    (hF : Nat.card F = 2 ^ n) : Nat.card (Matrix.SpecialLinearGroup (Fin 2) F) ≠ 168 := by
  have : Fintype F := Fintype.ofFinite F
  have hq : Fintype.card F = 2 ^ n := by rw [← Nat.card_eq_fintype_card, hF]
  rw [Matrix.card_SL_field, Fin.prod_univ_two, hq]
  simp only [Fin.val_zero, Fin.val_one, pow_zero, pow_one]
  have hq4 : 4 ≤ 2 ^ n := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  have e : ((2 ^ n) ^ 2 - 1) * ((2 ^ n) ^ 2 - 2 ^ n) =
      ((2 ^ n) ^ 2 - 1) * 2 ^ n * (2 ^ n - 1) := by
    rw [mul_assoc]; congr 1; rw [Nat.mul_sub_one, sq]
  rw [e, Nat.mul_div_cancel _ (by omega)]
  intro h
  obtain rfl | hn3 : n = 2 ∨ 3 ≤ n := by omega
  · norm_num at h
  · have h8 : 8 ≤ 2 ^ n := by
      calc 8 = 2 ^ 3 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn3
    have h64 : 64 ≤ (2 ^ n) ^ 2 := by nlinarith
    have h63 : 63 ≤ (2 ^ n) ^ 2 - 1 := by omega
    have := Nat.mul_le_mul h63 h8
    omega

theorem t1Inner_of
    (h1011 : Stmt10_1_1) (h1027 : Stmt10_2_7) {T L I : Subgroup G}
    (hyp : Hyp10 G T L I) (hL32 : LBarL32 L) (hn5 : ¬ Case10_1_1Five T L I) : T1Inner T L := by
  have hcard := card_lbar hL32
  rcases (h1011 G T L I hyp).2.2.2 with ⟨n, hn, ⟨K, _, _, hK, ⟨e⟩⟩, -⟩ | ⟨⟨e⟩, -⟩ | h3 |
      ⟨n, hn, ⟨K, _, _, hK, ⟨e⟩⟩, -⟩ | h5 | h6 | ⟨n, hsz, -⟩
  · rw [Nat.card_congr e.toEquiv] at hcard
    exact absurd hcard (card_sl_two_ne hn hK)
  · rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup, Nat.card_fin] at hcard
    exact absurd hcard (by decide)
  · intro s hs
    obtain ⟨x₀, hx₀, hx, -⟩ := inner_of_case3 hyp h3 hs
    exact ⟨x₀, hx₀, hx⟩
  · rw [Nat.card_congr e.toEquiv] at hcard
    exact absurd hcard (card_sl_two_ne (by omega) hK)
  · exact absurd h5 hn5
  · exact absurd h6 (h1027 G T L I hyp).1
  · exact absurd (by rw [hcard]; norm_num)
      (CFSG.RankThree.PartTwo.KFacts.KP7.three_not_dvd_card hsz)

theorem case3_of
    (h1011 : Stmt10_1_1) (h1027 : Stmt10_2_7) {T L I : Subgroup G}
    (hyp : Hyp10 G T L I) (hL32 : LBarL32 L) (hn5 : ¬ Case10_1_1Five T L I) :
    Case10_1_1Three T L I := by
  have hcard := card_lbar hL32
  rcases (h1011 G T L I hyp).2.2.2 with ⟨n, hn, ⟨K, _, _, hK, ⟨e⟩⟩, -⟩ | ⟨⟨e⟩, -⟩ | h3 |
      ⟨n, hn, ⟨K, _, _, hK, ⟨e⟩⟩, -⟩ | h5 | h6 | ⟨n, hsz, -⟩
  · rw [Nat.card_congr e.toEquiv] at hcard
    exact absurd hcard (card_sl_two_ne hn hK)
  · rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup, Nat.card_fin] at hcard
    exact absurd hcard (by decide)
  · exact h3
  · rw [Nat.card_congr e.toEquiv] at hcard
    exact absurd hcard (card_sl_two_ne (by omega) hK)
  · exact absurd h5 hn5
  · exact absurd h6 (h1027 G T L I hyp).1
  · exact absurd (by rw [hcard]; norm_num)
      (CFSG.RankThree.PartTwo.KFacts.KP7.three_not_dvd_card hsz)

theorem stmt10_2_4_of
    (h37 : Vol2Native.A37ForSQTKCat) (h38 : Vol2Native.A38ForSQTKCat)
    (h1011 : Stmt10_1_1) (h1027 : Stmt10_2_7) (h134 : EmptyFaithfulMultiple.Prop134E9He)
    (hRed : HeReduce) (h1029 : Stmt10_2_9) (hFa : FactL33M11) (hFc : FactL4L5) :
    Stmt10_2_4 := by
  intro G _ _ T L I hyp hL32 hn5 P hP hTP H hH
  have hinner := t1Inner_of h1011 h1027 hyp hL32 hn5
  have h3 := case3_of h1011 h1027 hyp hL32 hn5
  obtain ⟨t, ht, htn⟩ := Set.not_subset.mp hyp.not_normal
  obtain ⟨Ψ, c, hC⟩ := exists_L0Coord h37 h38 hyp hL32 hinner ht htn
  have h : MaxCtx T L I t Ψ c := ⟨h37, h38, hyp, ht, htn, hC⟩
  rcases maximal_classify h37 h38 hyp ht htn hC hP hTP with rfl | rfl
  · rcases kof_cases_of_red hRed h1029 h134 hFa hFc h3 h parData_a (Or.inl rfl) hH with
      h1 | h2 | ⟨h3', k, hk, -, h4⟩
    · exact Or.inl h1
    · exact Or.inr (Or.inl h2)
    · exact Or.inr (Or.inr ⟨h3', k, hk, h4⟩)
  · rcases kof_cases_of_red hRed h1029 h134 hFa hFc h3 h parData_b (Or.inr rfl) hH with
      h1 | h2 | ⟨h3', k, hk, -, h4⟩
    · exact Or.inl h1
    · exact Or.inr (Or.inl h2)
    · exact Or.inr (Or.inr ⟨h3', k, hk, h4⟩)

end CFSG.Quasithin.Vol2.Ch10.SecB

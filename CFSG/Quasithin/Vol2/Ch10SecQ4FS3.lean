module

public import CFSG.Quasithin.Vol2.Ch10SecAT1Fix
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Quasithin.Vol2.Ch10SecB3A5
public import CFSG.Quasithin.Vol2.Ch10SecB3CBor
public import CFSG.Quasithin.Vol2.Ch10SecQ4H5

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecF.C10P4F

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.H13 CFSG.QuasithinUnique

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G}

omit [Finite G] in
theorem three_dvd_card_LBar
    (h12 : (∃ n, Ch10.Case10_1_1One T L I n) ∨ Ch10.Case10_1_1Two T L I) :
    3 ∣ Nat.card (↥L ⧸ CFSG.pCore 2 ↥L) := by
  rcases h12 with ⟨n, -, ⟨K, _, _, hK, ⟨e⟩⟩, -⟩ | ⟨⟨e⟩, -⟩
  · rw [Nat.card_congr e.toEquiv, SecA.card_SL_two_pow hK]
    have h := Nat.sub_dvd_pow_sub_pow 4 1 n
    rw [one_pow] at h
    exact Dvd.dvd.mul_left h _
  · rw [Nat.card_congr e.toEquiv, SecB.card_alt5]
    norm_num

theorem mem_B0_of_three (h1012 : Ch10.Stmt10_1_2) (h1013 : Ch10.Stmt10_1_3) (h331 : Stmt3_3_1)
    (hyp : Hyp10 G T L I) (h12 : (∃ n, Ch10.Case10_1_1One T L I n) ∨ Ch10.Case10_1_1Two T L I)
    {H : Subgroup G} (hH : IsHStar T (fsuM T L) H) {q : G} (hqH : q ∈ H)
    (hqM : q ∈ fsuM T L) (hq3 : orderOf q = 3) :
    q ∈ fsuL0 T L ∧ q ∈ Subgroup.normalizer (Ch10.T0 T L : Set G) ∧ q ∈ Ch10.B0 T L := by
  have hL0 := h1013 G T L I hyp 3 Nat.prime_three (by norm_num) (three_dvd_card_LBar h12)
  have hqL0 : q ∈ fsuL0 T L :=
    hL0 ▸ Subgroup.subset_closure ⟨hqM, 1, by rw [hq3, pow_one]⟩
  have hmp := ((h1012 G T L I hyp).2.2.2.2.2.2.2.2 h12).1
  set Y := Subgroup.zpowers q ⊔ T with hY
  have hTY : T ≤ Y := le_sup_right
  have hYle : Y ≤ fsuL0 T L ⊔ T :=
    sup_le_sup_right (Subgroup.zpowers_le.mpr hqL0) T
  have hYlt : Y < fsuL0 T L ⊔ T := by
    refine lt_of_le_of_ne hYle fun heq => SecB.not_le_of_isHStar h331 hyp hH ?_
    have hYH : Y ≤ H := sup_le (Subgroup.zpowers_le.mpr hqH) hH.1.1
    exact ((SecA.le_fsuL0 T L).trans le_sup_left).trans (heq ▸ hYH)
  have hqN := (C10E4.le_of_isUniqueMaxOver' hmp.uniqueMax hTY hYlt
    (Subgroup.mem_sup_left (Subgroup.mem_zpowers q))).2
  refine ⟨hqL0, hqN, mem_oTwoUpper_of_odd ⟨hqL0, hqN⟩ ?_⟩
  rw [hq3]
  decide

theorem case2_of_centralizer (h1012 : Ch10.Stmt10_1_2) (h1013 : Ch10.Stmt10_1_3)
    (h331 : Stmt3_3_1) (hyp : Hyp10 G T L I)
    (h12 : (∃ n, Ch10.Case10_1_1One T L I n) ∨ Ch10.Case10_1_1Two T L I)
    {H : Subgroup G} (hH : IsHStar T (fsuM T L) H) {q : G} (hqH : q ∈ H)
    (hqM : q ∈ fsuM T L) (hq3 : orderOf q = 3)
    (hqZ : q ∈ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G)) :
    Ch10.Case10_1_1Two T L I := by
  rcases h12 with h1 | h2
  · exfalso
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    obtain ⟨-, -, hqB⟩ := mem_B0_of_three h1012 h1013 h331 hyp (Or.inl h1) hH hqH hqM hq3
    have hnL : ¬ Ch10.LBarL32 L := by
      obtain ⟨n, hn, ⟨K, _, _, hK, ⟨e⟩⟩, -⟩ := h1
      exact SecB.not_L32_of_SL2 hn hK e
    obtain ⟨D₀, hD₀⟩ := SecA.exists_isHallTwoPrimeOf_B0 hyp
    have hP : IsPGroup 3 (Subgroup.zpowers q) :=
      IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hq3, pow_one])
    obtain ⟨x, hx, hxle⟩ :=
      Ch11.SecB.exists_conj_le_hall (by norm_num) hD₀ (Subgroup.zpowers_le.mpr hqB) hP
    have hD := SecB.isHallTwoPrimeOf_conjSub hx hD₀
    have hbot := ((h1012 G T L I hyp).2.2.2.2.2.2.2.1 hnL _ hD).1 (Or.inl h1)
    have hq : q ∈ conjSub x D₀ ⊓ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) :=
      ⟨hxle (Subgroup.mem_zpowers q), hqZ⟩
    rw [hbot, Subgroup.mem_bot] at hq
    rw [hq, orderOf_one] at hq3
    omega
  · exact h2

end CFSG.Quasithin.Vol2.Ch10.SecF.C10P4F

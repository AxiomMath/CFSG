module

public import CFSG.Timmesfeld.Orders.Distinct
public import CFSG.Quasithin.Vol2.Ch11SecBL2OOrd
public import CFSG.Quasithin.Vol2.Ch11SecBL2UOut

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecB

open CFSG.Open

theorem card_isPSU3 {Y : Type} [Group Y] {k : ℕ} (hY : IsPSU 3 2 k Y) :
    Nat.card Y = ordTwistedA 2 (2 ^ k) :=
  (CFSG.Timmesfeld.card_statedClassicalModel_two hY).2.1 rfl

theorem ordTwistedA_two_eq {q : ℕ} (hq : 1 ≤ q) :
    ordTwistedA 2 q = q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 + 1)) / Nat.gcd 3 (q + 1) := by
  have h1 : ((q : ℤ) ^ 2 - (-1) ^ 2).toNat = q ^ 2 - 1 := by
    rw [show ((q : ℤ) ^ 2 - (-1) ^ 2) = ((q ^ 2 - 1 : ℕ) : ℤ) by
      push_cast [Nat.cast_sub (Nat.one_le_pow _ _ hq)]; ring]
    exact Int.toNat_natCast _
  have h2 : ((q : ℤ) ^ 3 - (-1) ^ 3).toNat = q ^ 3 + 1 := by
    rw [show ((q : ℤ) ^ 3 - (-1) ^ 3) = ((q ^ 3 + 1 : ℕ) : ℤ) by push_cast; ring]
    exact Int.toNat_natCast _
  rw [ordTwistedA, show 2 * (2 + 1) / 2 = 3 from rfl, show (2 : ℕ) + 1 = 3 from rfl,
    show (∏ i ∈ Finset.Icc 2 3, ((q : ℤ) ^ i - (-1) ^ i).toNat) =
      ((q : ℤ) ^ 2 - (-1) ^ 2).toNat * ((q : ℤ) ^ 3 - (-1) ^ 3).toNat from
      prod_Icc_two_three _, h1, h2]

theorem gcd_dvd_U3 (q : ℕ) (hq : 1 ≤ q) : Nat.gcd 3 (q + 1) ∣ (q ^ 2 - 1) * (q ^ 3 + 1) := by
  have h3 : q + 1 ∣ q ^ 2 - 1 := ⟨q - 1, by
    have := sq_eq_succ_mul_pred q hq
    omega⟩
  exact (Nat.gcd_dvd_right 3 (q + 1)).trans (h3.trans (Dvd.intro _ rfl))

theorem exists_odd_ordTwistedA_two {k : ℕ} (hk : 1 ≤ k) :
    ∃ r : ℕ, Odd r ∧ ordTwistedA 2 (2 ^ k) = 2 ^ (3 * k) * r := by
  have hq : 1 ≤ 2 ^ k := Nat.one_le_two_pow
  have hodd : Odd (((2 ^ k) ^ 2 - 1) * ((2 ^ k) ^ 3 + 1)) := by
    refine Odd.mul ?_ ?_
    · exact CFSG.Timmesfeld.Orders.odd_pow_sub_one (by omega) (by norm_num)
    · exact CFSG.Timmesfeld.Orders.odd_pow_add_one (by omega) (by norm_num)
  refine ⟨((2 ^ k) ^ 2 - 1) * ((2 ^ k) ^ 3 + 1) / Nat.gcd 3 (2 ^ k + 1),
    Odd.of_dvd_nat hodd (Nat.div_dvd_of_dvd (gcd_dvd_U3 _ hq)), ?_⟩
  rw [ordTwistedA_two_eq hq, Nat.mul_div_assoc _ (gcd_dvd_U3 _ hq),
    show 2 ^ (3 * k) = (2 ^ k) ^ 3 by rw [← pow_mul, mul_comm]]

theorem lt_ordTwistedA_two {k : ℕ} (hk : 2 ≤ k) : 20160 < ordTwistedA 2 (2 ^ k) := by
  have hq4 : 4 ≤ 2 ^ k := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk
  set q := 2 ^ k with hq
  have hq1 : 1 ≤ q := by omega
  rw [ordTwistedA_two_eq hq1, Nat.mul_div_assoc _ (gcd_dvd_U3 _ hq1)]
  have hd : Nat.gcd 3 (q + 1) ≤ 3 := Nat.le_of_dvd (by norm_num) (Nat.gcd_dvd_left _ _)
  have h16 : 16 ≤ q ^ 2 := by nlinarith
  have h64' : 64 ≤ q ^ 3 := by nlinarith
  have h2 : 15 ≤ q ^ 2 - 1 := by omega
  have h3 : 65 ≤ q ^ 3 + 1 := by omega
  have hX : 975 ≤ (q ^ 2 - 1) * (q ^ 3 + 1) := by nlinarith
  have hdiv : 325 ≤ (q ^ 2 - 1) * (q ^ 3 + 1) / Nat.gcd 3 (q + 1) := by
    calc 325 = 975 / 3 := by norm_num
      _ ≤ (q ^ 2 - 1) * (q ^ 3 + 1) / 3 := Nat.div_le_div_right hX
      _ ≤ (q ^ 2 - 1) * (q ^ 3 + 1) / Nat.gcd 3 (q + 1) :=
        Nat.div_le_div_left hd (Nat.gcd_pos_of_pos_left _ (by norm_num))
  have h64 : 64 ≤ q ^ 3 := by nlinarith
  nlinarith

theorem ordA_mem {n f : ℕ} (hn : 1 ≤ n) (hf : 1 ≤ f) (hnf : (n, f) ≠ (1, 1)) :
    ordA n (2 ^ f) ∈ CFSG.Timmesfeld.evenOrdersExceptUnitarySp4 :=
  Set.mem_union_left _ ⟨f, hf, Or.inl ⟨n, hn, hnf, rfl⟩⟩

theorem ordSuzuki_mem {f : ℕ} (hf : Odd f) (hf3 : 3 ≤ f) :
    ordSuzuki (2 ^ f) ∈ CFSG.Timmesfeld.evenOrdersExceptUnitarySp4 :=
  Set.mem_union_left _ ⟨f, by omega, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
    (Or.inr (Or.inr (Or.inr ⟨hf, hf3, Or.inl rfl⟩)))))))))⟩

theorem card_isSz
    {Y : Type} [Group Y] {f : ℕ} (hY : IsSz f Y) :
    Odd f ∧ 3 ≤ f ∧ Nat.card Y = ordSuzuki (2 ^ f) := by
  obtain ⟨-, a, ha, K, _, _, hfa, hK, ⟨e⟩⟩ := hY
  refine ⟨⟨a, by omega⟩, by omega, ?_⟩
  rw [Nat.card_congr e.toEquiv, CFSG.LieType.Ree.suzuki_order (by rw [hK, hfa]), ordSuzuki,
    hfa]
  ring

theorem not_a312Out_of_isPSU3
    {Y : Type} [Group Y] {k : ℕ} (hk : 2 ≤ k) (hY : IsPSU 3 2 k Y) :
    ¬ A312Out Y := by
  have hc := card_isPSU3 hY
  obtain ⟨r, hr, hr'⟩ := exists_odd_ordTwistedA_two (k := k) (by omega)
  have hne : ∀ m ∈ CFSG.Timmesfeld.evenOrdersExceptUnitarySp4, m ≠ ordTwistedA 2 (2 ^ k) :=
    fun m hm => (CFSG.Timmesfeld.evenOrdersExceptUnitarySp4_ne hm).1 2 k le_rfl (by omega)
  rintro (h | ⟨n, hn, h⟩ | ⟨f, h⟩ | ⟨p, hp, hp2, h⟩ | h | h)
  · have := lt_ordTwistedA_two hk
    omega
  · have hcn := (CFSG.Timmesfeld.card_statedClassicalModel_two h).1 rfl
    rw [show (2 : ℕ) - 1 = 1 from rfl] at hcn
    exact hne _ (ordA_mem le_rfl (by omega) (by intro h; simp at h; omega)) (hcn.symm.trans hc)
  · obtain ⟨hodd, hf3, hcf⟩ := card_isSz h
    exact hne _ (ordSuzuki_mem hodd hf3) (hcf.symm.trans hc)
  · exact false_of_l2BadType_of_card hk (Or.inr (Or.inl hY)) hp hp2 h
  · rw [hc, hr', show (443520 : ℕ) = 2 ^ 7 * 3465 by norm_num] at h
    have := CFSG.Timmesfeld.Orders.eq_of_two_pow_mul_odd hr ⟨1732, by norm_num⟩ h
    omega
  · rw [hc, hr', show (244823040 : ℕ) = 2 ^ 10 * 239085 by norm_num] at h
    have := CFSG.Timmesfeld.Orders.eq_of_two_pow_mul_odd hr ⟨119542, by norm_num⟩ h
    omega

end CFSG.Quasithin.Vol2.Ch11.SecB

module

public import CFSG.Quasithin.EmptyFaithful.Gold14610CmpTwo
public import CFSG.Quasithin.EmptyFaithful.Gold14610Props
public import CFSG.Quasithin.EmptyFaithful.A38c7Rank
public import CFSG.Timmesfeld.Orders.ClassicalLinear
public import CFSG.Quasithin.Vol2.Ch11SecA11Ord

public section

namespace CFSG.Quasithin.Gold14610

open CFSG.Assembly.LowTwoRank

theorem card_isL2_odd {p e : ℕ} {Y : Type} [Group Y] (h : F6.IsL2 p e Y)
    (hq : p ^ e % 2 = 1) : Nat.card Y = p ^ e * ((p ^ e) ^ 2 - 1) / 2 := by
  have h1 := Vol2.Ch11.SecA.card_of_isPSL (X := Y) (k := 2) (p := p) (e := e) (by norm_num) h
  have hg : Nat.gcd 2 (p ^ e - 1) = 2 := by
    have : 0 < p ^ e := by omega
    exact Nat.gcd_eq_left (by omega)
  rw [h1, hg, show Finset.Icc 2 2 = {2} by decide, Finset.prod_singleton]
  norm_num

theorem card_isHatAlt {n : ℕ} (hn : 2 ≤ n) {Y : Type} [Group Y] (h : F6.IsHatAlt n Y) :
    Nat.card Y = n.factorial / 2 * 3 := by
  obtain ⟨-, h3, ⟨e⟩⟩ := h
  have hA : Nat.card ↥(alternatingGroup (Fin n)) = n.factorial / 2 :=
    Vol2.Ch11.SecA.card_of_isAlt hn ⟨MulEquiv.refl _⟩
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center Y),
    Nat.card_congr e.toEquiv, hA, h3]

theorem sq_mod_sixteen {p : ℕ} (hp : p % 8 = 3 ∨ p % 8 = 5) : p ^ 2 % 16 = 9 := by
  have : p % 16 = 3 ∨ p % 16 = 5 ∨ p % 16 = 11 ∨ p % 16 = 13 := by omega
  rcases this with h | h | h | h <;> simp [Nat.pow_mod, h]

theorem card_sl3_of {p : ℕ} {K : Type} [Field K] [Finite K] (hK : Nat.card K = p)
    {Y : Type} [Group Y]
    (h : Nonempty (Y ≃* ↥(StatedSL 3 K)) ∨ Nonempty (Y ≃* StatedProj (StatedSL 3 K))) :
    ∃ e, (e = 1 ∨ e = 3) ∧ Nat.card Y * e = p ^ 3 * ((p ^ 2 - 1) * (p ^ 3 - 1)) := by
  rcases h with ⟨⟨f⟩⟩ | ⟨⟨f⟩⟩
  · refine ⟨1, Or.inl rfl, ?_⟩
    rw [Nat.card_congr f.toEquiv, A38c7.card_statedSL_three, hK]
    ring
  · have h1 := Timmesfeld.ClassicalOrders.card_statedProj_statedSL (K := K) (n := 3) (by norm_num)
    rw [hK] at h1
    have hg : Nat.gcd 3 (p - 1) = 1 ∨ Nat.gcd 3 (p - 1) = 3 :=
      (Nat.dvd_prime Nat.prime_three).mp (Nat.gcd_dvd_left 3 (p - 1))
    refine ⟨Nat.gcd 3 (p - 1), hg, ?_⟩
    have h2 : Nat.card (StatedProj (StatedSL 3 K)) =
        p ^ 3 * ((p ^ 2 - 1) * (p ^ 3 - 1)) / Nat.gcd 3 (p - 1) := by
      rw [h1, show Finset.Icc 2 3 = {2, 3} by decide, Finset.prod_pair (by norm_num)]
    rw [Nat.card_congr f.toEquiv, h2]
    refine Nat.div_mul_cancel (Dvd.dvd.mul_left (Dvd.dvd.mul_right ?_ _) _)
    exact (Nat.gcd_dvd_right 3 (p - 1)).trans (by simpa using Nat.sub_dvd_pow_sub_pow p 1 2)

theorem toNat_aux (p : ℕ) (hp : 1 ≤ p) :
    ((((p : ℕ) : ℤ) ^ 2 - (-1) ^ 2).toNat) * (((p : ℤ) ^ 3 - (-1) ^ 3).toNat) =
      (p ^ 2 - 1) * (p ^ 3 + 1) := by
  have h2 : ((p : ℤ) ^ 2 - (-1) ^ 2).toNat = p ^ 2 - 1 := by
    have : 1 ≤ p ^ 2 := Nat.one_le_pow _ _ hp
    have h : ((p : ℤ) ^ 2 - (-1) ^ 2) = ((p ^ 2 - 1 : ℕ) : ℤ) := by
      push_cast [Nat.cast_sub this]; ring
    rw [h, Int.toNat_natCast]
  have h3 : ((p : ℤ) ^ 3 - (-1) ^ 3).toNat = p ^ 3 + 1 := by
    have h : ((p : ℤ) ^ 3 - (-1) ^ 3) = ((p ^ 3 + 1 : ℕ) : ℤ) := by push_cast; ring
    rw [h, Int.toNat_natCast]
  rw [h2, h3]

theorem card_su3_of {p : ℕ} (hp : p.Prime) {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = p ^ 2) {Y : Type} [Group Y]
    (h : Nonempty (Y ≃* ↥(StatedSU 3 p K)) ∨ Nonempty (Y ≃* StatedProj (StatedSU 3 p K))) :
    ∃ e, (e = 1 ∨ e = 3) ∧ Nat.card Y * e = p ^ 3 * ((p ^ 2 - 1) * (p ^ 3 + 1)) := by
  have hK1 : Nat.card K = (p ^ 1) ^ 2 := by rw [pow_one]; exact hK
  have h1 := Timmesfeld.ClassicalOrders.card_statedProj_statedSU (K := K) (n := 3) hp
    le_rfl hK1 (by norm_num)
  have hsc := (LinearGroups.unitary_scalar_kernel (K := K) hp hK1 (n := 3) (by norm_num)).2.2
  simp only [pow_one] at h1
  rw [pow_one] at hsc
  have hg : Nat.gcd 3 (p + 1) = 1 ∨ Nat.gcd 3 (p + 1) = 3 :=
    (Nat.dvd_prime Nat.prime_three).mp (Nat.gcd_dvd_left 3 (p + 1))
  have hd : Nat.gcd 3 (p + 1) ∣ p ^ 3 * ((p ^ 2 - 1) * (p ^ 3 + 1)) := by
    refine Dvd.dvd.mul_left (Dvd.dvd.mul_right ?_ _) _
    refine (Nat.gcd_dvd_right 3 (p + 1)).trans ⟨p - 1, ?_⟩
    have h1p : 1 ≤ p := hp.one_le
    zify [h1p, Nat.one_le_pow 2 p (by omega)]
    ring
  have hP : Nat.card (StatedProj (StatedSU 3 p K)) =
      p ^ 3 * ((p ^ 2 - 1) * (p ^ 3 + 1)) / Nat.gcd 3 (p + 1) := by
    rw [h1, show Finset.Icc 2 3 = {2, 3} by decide, Finset.prod_pair (by norm_num),
      toNat_aux p hp.one_le]
  rcases h with ⟨⟨f⟩⟩ | ⟨⟨f⟩⟩
  · refine ⟨1, Or.inl rfl, ?_⟩
    rw [Nat.card_congr f.toEquiv, mul_one,
      Subgroup.card_eq_card_quotient_mul_card_subgroup
        ((StatedScalars (Fin 3) K).subgroupOf (StatedSU 3 p K))]
    change Nat.card (StatedProj (StatedSU 3 p K)) * _ = _
    rw [hP, hsc]
    exact Nat.div_mul_cancel hd
  · refine ⟨Nat.gcd 3 (p + 1), hg, ?_⟩
    rw [Nat.card_congr f.toEquiv, hP]
    exact Nat.div_mul_cancel hd

theorem F618OrdA_of_isSLEps3 {p : ℕ} (hp8 : p % 8 = 3 ∨ p % 8 = 5) {Y : Type} [Group Y]
    (h : F6.IsSLEps3 p Y) : F618OrdA (Nat.card Y) := by
  obtain ⟨hp, K, _, _, h⟩ := h
  have h3 : 3 ≤ p := by omega
  rcases h with ⟨h4, hK, hY⟩ | ⟨h4, hK, hY⟩
  · obtain ⟨e, he, hy⟩ := card_sl3_of hK hY
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨p, e, h3, he, Or.inl ⟨by omega, hy⟩⟩))))
  · obtain ⟨e, he, hy⟩ := card_su3_of hp hK hY
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨p, e, h3, he, Or.inr ⟨by omega, hy⟩⟩))))

theorem F618OrdA.of_1080 : F618OrdA 1080 := Or.inr (Or.inr (Or.inl rfl))

theorem F618OrdA.of_2520 : F618OrdA 2520 := Or.inr (Or.inr (Or.inr (Or.inl rfl)))

theorem F618OrdA.of_7560 : F618OrdA 7560 := Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))

theorem m12_noncomm : ∃ a b : ↥CFSG.Blueprint.NativeSporadic.M12, a * b ≠ b * a :=
  ⟨Sporadic.Mathieu.m12a, Sporadic.Mathieu.m12b, fun h => by
    have := congrArg Subtype.val h
    revert this
    decide⟩

theorem F618Core.ord {Y : Type} [Group Y] (h : F618Core Y) :
    F618OrdA (Nat.card Y) ∨ (Nat.card Y = 95040 ∧ IsSimpleGroup Y ∧ Subgroup.center Y = ⊥) := by
  rcases h with ⟨p, -, hp, hY⟩ | ⟨p, e, -, -, -, hq, hY⟩ | hY | ⟨⟨e⟩⟩ | hY | ⟨p, -, hp, hY⟩ |
    ⟨p, hp, hY⟩ | ⟨⟨e⟩⟩
  · refine Or.inl (Or.inl ⟨p, by omega, by omega, ?_⟩)
    simpa using card_isL2_odd hY (by simp; omega)
  · exact Or.inl (Or.inr (Or.inl ⟨p ^ e, by omega, hq, card_isL2_odd hY (by omega)⟩))
  · have : Nat.card Y = 1080 := by rw [card_isHatAlt (by norm_num) hY]; decide
    rw [this]
    exact Or.inl .of_1080
  · have : Nat.card Y = 2520 := by
      rw [Nat.card_congr e.toEquiv, Vol2.Ch11.SecA.card_of_isAlt (by norm_num) ⟨MulEquiv.refl _⟩]
      decide
    rw [this]
    exact Or.inl .of_2520
  · have : Nat.card Y = 7560 := by rw [card_isHatAlt (by norm_num) hY]; decide
    rw [this]
    exact Or.inl .of_7560
  · have hodd : p ^ 2 % 2 = 1 := by
      have : p % 2 = 1 := by omega
      simp [Nat.pow_mod, this]
    have h3 : 3 ≤ p := by omega
    refine Or.inl (Or.inr (Or.inl ⟨p ^ 2, by nlinarith, Or.inr (sq_mod_sixteen hp), ?_⟩))
    exact card_isL2_odd hY hodd
  · exact Or.inl (F618OrdA_of_isSLEps3 hp hY)
  · refine Or.inr ⟨?_, ?_⟩
    · rw [Nat.card_congr e.toEquiv]
      exact Sporadic.Mathieu.card_M12
    · have hs : IsSimpleGroup CFSG.Blueprint.NativeSporadic.M12 :=
        Sporadic.Mathieu.fam_m12_simplicity.2.2
      have hsY : IsSimpleGroup Y := e.isSimpleGroup
      refine ⟨hsY, ?_⟩
      rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center Y) with h0 | h0
      · exact h0
      · exfalso
        obtain ⟨a, b, hab⟩ := m12_noncomm
        apply hab
        have := Subgroup.mem_center_iff.mp (h0 ▸ Subgroup.mem_top (e.symm b)) (e.symm a)
        simpa using congrArg e this

end CFSG.Quasithin.Gold14610

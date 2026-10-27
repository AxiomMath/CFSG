module

public import CFSG.Quasithin.H13.VolIA38Orders

public section

namespace CFSG.Quasithin.H13.VolI

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.Blueprint CFSG.Timmesfeld CFSG.Timmesfeld.Orders

theorem card_SL_three {F : Type} [Field F] [Fintype F] {q : ℕ} (hq : Fintype.card F = q)
    (hq2 : 2 ≤ q) :
    Nat.card (Matrix.SpecialLinearGroup (Fin 3) F) = q ^ 3 * ((q ^ 3 - 1) * (q ^ 2 - 1)) := by
  rw [Matrix.card_SL_field, hq, Fin.prod_univ_three]
  simp only [Fin.val_zero, Fin.val_one, Fin.val_two, pow_zero, pow_one]
  have h1 : 1 ≤ q := by omega
  have h2 : q ≤ q ^ 3 := Nat.le_self_pow (by norm_num) q
  have h3 : q ^ 2 ≤ q ^ 3 := Nat.pow_le_pow_right (by omega) (by norm_num)
  have h4 : 1 ≤ q ^ 3 := Nat.one_le_pow _ _ (by omega)
  have h5 : 1 ≤ q ^ 2 := Nat.one_le_pow _ _ (by omega)
  have e : (q ^ 3 - 1) * (q ^ 3 - q) * (q ^ 3 - q ^ 2) =
      (q - 1) * (q ^ 3 * ((q ^ 3 - 1) * (q ^ 2 - 1))) := by
    zify [h1, h2, h3, h4, h5]
    ring
  rw [e, Nat.mul_div_cancel_left _ (by omega)]

theorem not_three_dvd_ordSuzuki {f : ℕ} (hf : Odd f) : ¬ 3 ∣ ordSuzuki (2 ^ f) := by
  obtain ⟨k, rfl⟩ := hf
  have ht : 4 ^ k % 3 = 1 := by
    rw [Nat.pow_mod]
    norm_num
  have hu : 4 ^ k * 4 ^ k % 3 = 1 := by
    rw [Nat.mul_mod, ht]
  have e1 : 2 ^ (2 * k + 1) = 2 * 4 ^ k := by
    rw [pow_succ, pow_mul]
    norm_num
    ring
  have e2 : (2 * 4 ^ k) ^ 2 = 4 * (4 ^ k * 4 ^ k) := by ring
  unfold ordSuzuki
  rw [e1, e2]
  intro h
  rcases (Nat.Prime.dvd_mul Nat.prime_three).1 h with h | h
  · rcases (Nat.Prime.dvd_mul Nat.prime_three).1 h with h | h
    · omega
    · omega
  · omega

theorem a38TypesSLThree_holds
    : ∀ (X : Type) [Group X] (F : Type) [Field F] [Finite F] (m : ℕ),
    Nat.card F = 2 ^ m → Nonempty (X ≃* ↥(Assembly.LowTwoRank.StatedSL 3 F)) → A38Types X →
      m = 1 := by
  intro X _ F _ _ m hF ⟨φ⟩ hA
  have : Fintype F := Fintype.ofFinite F
  have hm : 1 ≤ m := by
    by_contra h0
    have hm0 : m = 0 := by omega
    rw [hm0, pow_zero] at hF
    have h1 := (Finite.one_lt_card (α := F))
    omega
  set q := 2 ^ m with hqdef
  have hq : Fintype.card F = q := by rw [← Nat.card_eq_fintype_card, hF]
  have hq2 : 2 ≤ q := by
    rw [hqdef]
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
  have hX : Nat.card X = q ^ 3 * ((q ^ 3 - 1) * (q ^ 2 - 1)) := by
    rw [Nat.card_congr φ.toEquiv,
      ← Nat.card_congr (specialLinearGroupEquivStatedSL 3 F).toEquiv, card_SL_three hq hq2]
  have hq3 : q ^ 3 = 2 ^ (m * 3) := by rw [hqdef, ← pow_mul]
  have hodd : Odd ((q ^ 3 - 1) * (q ^ 2 - 1)) := by
    have ha : Odd (q ^ 3 - 1) := by
      rw [hq3]
      exact odd_two_pow_sub_one (by omega)
    have hb : Odd (q ^ 2 - 1) := by
      rw [hqdef, ← pow_mul]
      exact odd_two_pow_sub_one (by omega)
    exact ha.mul hb
  have h2part : ∃ r, Odd r ∧ Nat.card X = 2 ^ (m * 3) * r := ⟨_, hodd, by rw [hX, hq3]⟩
  have h1 : 1 ≤ q := by omega
  have hpos3 : 1 ≤ q ^ 3 := Nat.one_le_pow _ _ (by omega)
  have hpos2 : 1 ≤ q ^ 2 := Nat.one_le_pow _ _ (by omega)
  have h23 : q ^ 2 ≤ q ^ 3 := Nat.pow_le_pow_right (by omega) (by norm_num)
  have hq22 : 2 ≤ q ^ 2 := le_trans hq2 (Nat.le_self_pow (by norm_num) q)
  have hq32 : 2 ≤ q ^ 3 := le_trans hq22 h23
  rcases a38Order_card hA with ⟨n, hn, hcard⟩ | ⟨f, hf, -, hcard⟩ | hcard | ⟨p, hp, hp3, hcard⟩
  ·
    exfalso
    have hn3 : n = m * 3 := by
      by_contra hne
      exact ne_of_two_part (two_part_ordA_one (by omega)) h2part hne hcard.symm
    rw [ordA_one_two_pow (by omega), hn3, ← hq3, hX] at hcard
    have h6 : (q ^ 3 - 1) * (q ^ 2 - 1) = (q ^ 3) ^ 2 - 1 :=
      Nat.eq_of_mul_eq_mul_left (by omega) hcard
    have h7 : 1 ≤ (q ^ 3) ^ 2 := Nat.one_le_pow _ _ (by omega)
    zify [hpos3, hpos2, h7] at h6
    nlinarith
  ·
    exfalso
    have h3 : 3 ∣ q ^ 2 - 1 := by
      have e : q ^ 2 = 4 ^ m := by
        rw [hqdef, ← pow_mul, mul_comm, pow_mul]
        norm_num
      rw [e]
      exact Nat.sub_one_dvd_pow_sub_one 4 m
    have h3X : 3 ∣ Nat.card X := by
      rw [hX]
      exact Dvd.dvd.mul_left (Dvd.dvd.mul_left h3 _) _
    rw [hcard] at h3X
    exact not_three_dvd_ordSuzuki hf h3X
  ·
    by_contra hne
    exact ne_of_two_part (N := 3) ⟨21945, ⟨10972, by norm_num⟩, by norm_num⟩ h2part (by omega)
      hcard.symm
  ·
    have hpodd : Odd p := hp.odd_of_ne_two (by omega)
    have hdvd2 : 2 ^ (m * 3) ∣ ordA 1 p := by
      obtain ⟨r, -, hr⟩ := h2part
      rw [← hcard, hr]
      exact Dvd.intro r rfl
    have hle : q ^ 3 ≤ p + 1 := by
      rw [hq3]
      exact two_pow_le_of_dvd_ordA_one hpodd (by omega) hdvd2
    have h2ord := two_mul_ordA_one_of_odd hpodd
    have hpX : p ∣ Nat.card X := by
      rw [hcard]
      have h1' : p ∣ 2 * ordA 1 p := by
        rw [h2ord]
        exact Dvd.intro _ rfl
      exact (Nat.Coprime.dvd_of_dvd_mul_left
        ((Nat.coprime_primes hp Nat.prime_two).2 (by omega)) h1')
    rw [hX] at hpX
    have hp2 : ¬ p ∣ q ^ 3 := by
      rw [hq3]
      intro h
      have := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow h)
      omega
    have hpq : p ≤ q ^ 3 - 1 := by
      rcases (Nat.Prime.dvd_mul hp).1 ((Nat.Prime.dvd_mul hp).1 hpX |>.resolve_left hp2) with
        h | h
      · exact Nat.le_of_dvd (by omega) h
      · have := Nat.le_of_dvd (by omega) h
        omega
    have hpe : p = q ^ 3 - 1 := by omega
    rw [← hcard, hX, hpe] at h2ord
    have hsq : (q ^ 3 - 1) ^ 2 - 1 = q ^ 3 * (q ^ 3 - 2) := by
      have h8 : 1 ≤ (q ^ 3 - 1) ^ 2 := Nat.one_le_pow _ _ (by omega)
      zify [hpos3, h8, hq32]
      ring
    rw [hsq] at h2ord
    have h9 : (q ^ 3 * (q ^ 3 - 1)) * (2 * (q ^ 2 - 1)) = (q ^ 3 * (q ^ 3 - 1)) * (q ^ 3 - 2) := by
      calc (q ^ 3 * (q ^ 3 - 1)) * (2 * (q ^ 2 - 1)) =
            2 * (q ^ 3 * ((q ^ 3 - 1) * (q ^ 2 - 1))) := by ring
        _ = (q ^ 3 - 1) * (q ^ 3 * (q ^ 3 - 2)) := h2ord
        _ = (q ^ 3 * (q ^ 3 - 1)) * (q ^ 3 - 2) := by ring
    have h10 := Nat.eq_of_mul_eq_mul_left (Nat.mul_pos (by omega) (by omega)) h9
    have h11 : q * q ^ 2 = 2 * q ^ 2 := by
      have e : q * q ^ 2 = q ^ 3 := by ring
      omega
    have hq' : q = 2 := Nat.eq_of_mul_eq_mul_right (by omega) h11
    rw [hqdef] at hq'
    have := Nat.pow_right_injective (le_refl 2) (hq'.trans (pow_one 2).symm)
    omega

end CFSG.Quasithin.H13.VolI

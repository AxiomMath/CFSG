module

public import CFSG.Quasithin.Vol2.Ch11SecA02Shape

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecA

open CFSG.Open CFSG.Blueprint

variable {X Y : Type} [Group X] [Group Y]

theorem card_eq_ker_mul {f : X →* Y} (hf : Function.Surjective f) :
    Nat.card X = Nat.card f.ker * Nat.card Y := by
  rw [f.ker.card_eq_card_quotient_mul_card_subgroup, mul_comm,
    Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective f hf).toEquiv]

theorem odd_of_dvd_two_pow_sub_one {c n : ℕ} (hn : 1 ≤ n) (h : c ∣ 2 ^ n - 1) : Odd c :=
  Odd.of_dvd_nat (odd_two_pow_sub_one hn) h

theorem two_pow_eq_of {c z e o e' o' : ℕ} (hc : Odd c) (hz : Odd z) (ho : Odd o) (ho' : Odd o')
    (h : c * (z * (2 ^ e' * o')) = 2 ^ e * o) : e' = e ∧ c * z * o' = o := by
  have h1 : 2 ^ e' * (c * z * o') = 2 ^ e * o := by rw [← h]; ring
  have he := eq_of_two_pow_mul_odd ((hc.mul hz).mul ho') ho h1
  refine ⟨he, ?_⟩
  rw [he] at h1
  exact Nat.eq_of_mul_eq_mul_left (by positivity) h1

theorem odd_oSL2 {m : ℕ} (hm : 1 ≤ m) : Odd (oSL2 m) := odd_two_pow_sub_one (by omega)

theorem odd_oSL3 {m : ℕ} (hm : 1 ≤ m) : Odd (oSL3 m) :=
  (odd_two_pow_sub_one (by omega)).mul (odd_two_pow_sub_one (by omega))

theorem odd_oSp4 {m : ℕ} (hm : 1 ≤ m) : Odd (oSp4 m) :=
  (odd_two_pow_sub_one (by omega)).mul (odd_two_pow_sub_one (by omega))

theorem odd_oG2 {m : ℕ} (hm : 1 ≤ m) : Odd (oG2 m) :=
  (odd_two_pow_sub_one (by omega)).mul (odd_two_pow_sub_one (by omega))

variable {n : ℕ} {f : X →* Y}

theorem shape_eq (hX : ShapeData X n) (hn : 2 ≤ n) (hf : Function.Surjective f)
    (hodd : Odd (Nat.card f.ker)) {e' o' : ℕ} (ho' : Odd o') (hY : Nat.card Y = 2 ^ e' * o') :
    (∃ (K : Type) (_ : Field K) (_ : Finite K) (c : ℕ), Nat.card K = 2 ^ n ∧ c ∣ 2 ^ n - 1 ∧
        e' = 3 * n ∧ c * Nat.card f.ker * o' = oSL3 n ∧
        (c = 1 → Nat.card (Subgroup.center X) ≤ 3) ∧
        ∃ g : Matrix.SpecialLinearGroup (Fin 3) K →* X, Function.Surjective g) ∨
      (∃ c : ℕ, c ∣ 2 ^ n - 1 ∧ e' = 4 * n ∧ c * Nat.card f.ker * o' = oSp4 n) ∨
      (e' = 6 * n ∧ Nat.card f.ker * o' = oG2 n) := by
  have hcard := card_eq_ker_mul hf
  rcases hX with ⟨K, _, _, c, hK, hc, hcX, hcZ, g, hg⟩ | ⟨c, hc, hcX⟩ | hcX
  · rw [hcard, hY] at hcX
    obtain ⟨h1, h2⟩ := two_pow_eq_of (odd_of_dvd_two_pow_sub_one (by omega) hc) hodd
      (odd_oSL3 (by omega)) ho' hcX
    exact Or.inl ⟨K, inferInstance, inferInstance, c, hK, hc, h1, h2, hcZ, g, hg⟩
  · rw [hcard, hY] at hcX
    obtain ⟨h1, h2⟩ := two_pow_eq_of (odd_of_dvd_two_pow_sub_one (by omega) hc) hodd
      (odd_oSp4 (by omega)) ho' hcX
    exact Or.inr (Or.inl ⟨c, hc, h1, h2⟩)
  · rw [hcard, hY, ← one_mul (Nat.card f.ker * _)] at hcX
    obtain ⟨h1, h2⟩ := two_pow_eq_of odd_one hodd (odd_oG2 (by omega)) ho' hcX
    rw [one_mul] at h2
    exact Or.inr (Or.inr ⟨h1, h2⟩)

theorem injective_of_card_ker [Finite X] (h : Nat.card f.ker = 1) : Function.Injective f :=
  (MonoidHom.ker_eq_bot_iff f).mp (Subgroup.card_eq_one.mp h)

theorem recog_SL2 (hX : ShapeData X n) (hn : 2 ≤ n) (hf : Function.Surjective f)
    (hodd : Odd (Nat.card f.ker)) {m : ℕ} (hm : 1 ≤ m) (hY : Nat.card Y = 2 ^ m * oSL2 m) :
    False := by
  rcases shape_eq hX hn hf hodd (odd_oSL2 hm) hY with
    ⟨-, -, -, c, -, -, h1, h2, -⟩ | ⟨c, -, h1, h2⟩ | ⟨h1, h2⟩
  · subst h1
    exact not_dvd_oSL2_oSL3 (n := n) (by omega) ⟨c * Nat.card f.ker, by rw [← h2]; ring⟩
  · subst h1
    exact not_dvd_oSL2_oSp4 (n := n) (by omega) ⟨c * Nat.card f.ker, by rw [← h2]; ring⟩
  · subst h1
    exact not_dvd_oSL2_oG2 (n := n) (by omega) ⟨Nat.card f.ker, by rw [← h2]; ring⟩

theorem recog_SL3 [Finite X] (hX : ShapeData X n) (hn : 2 ≤ n) (hf : Function.Surjective f)
    (hodd : Odd (Nat.card f.ker)) {m : ℕ} (hm : 1 ≤ m) (hY : Nat.card Y = 2 ^ (3 * m) * oSL3 m) :
    m = n ∧ Function.Injective f := by
  rcases shape_eq hX hn hf hodd (odd_oSL3 hm) hY with
    ⟨-, -, -, c, -, -, h1, h2, -⟩ | ⟨c, -, h1, h2⟩ | ⟨h1, h2⟩
  · have hmn : m = n := by omega
    subst hmn
    have hpos : 0 < oSL3 m := (odd_oSL3 hm).pos
    have h3 : c * Nat.card f.ker = 1 := by
      have : c * Nat.card f.ker * oSL3 m = 1 * oSL3 m := by rw [h2, one_mul]
      exact Nat.eq_of_mul_eq_mul_right hpos this
    exact ⟨rfl, injective_of_card_ker (Nat.eq_one_of_mul_eq_one_left h3)⟩
  · obtain ⟨k, rfl, rfl⟩ : ∃ k, m = 4 * k ∧ n = 3 * k := ⟨m - n, by omega, by omega⟩
    exact (not_dvd_oSL3_oSp4 (k := k) (by omega) ⟨c * Nat.card f.ker, by rw [← h2]; ring⟩).elim
  · obtain rfl : m = 2 * n := by omega
    exact (not_dvd_oSL3_oG2 (n := n) (by omega) ⟨Nat.card f.ker, by rw [← h2]; ring⟩).elim

theorem recog_Sp4 [Finite X] (hX : ShapeData X n) (hn : 2 ≤ n) (hf : Function.Surjective f)
    (hodd : Odd (Nat.card f.ker)) {m : ℕ} (hm : 1 ≤ m) (hY : Nat.card Y = 2 ^ (4 * m) * oSp4 m) :
    m = n ∧ Function.Injective f := by
  rcases shape_eq hX hn hf hodd (odd_oSp4 hm) hY with
    ⟨-, -, -, c, -, -, h1, h2, -⟩ | ⟨c, -, h1, h2⟩ | ⟨h1, h2⟩
  · obtain ⟨k, rfl, rfl⟩ : ∃ k, m = 3 * k ∧ n = 4 * k := ⟨n - m, by omega, by omega⟩
    exact (not_dvd_oSp4_oSL3 (k := k) (by omega) ⟨c * Nat.card f.ker, by rw [← h2]; ring⟩).elim
  · have hmn : m = n := by omega
    subst hmn
    have hpos : 0 < oSp4 m := (odd_oSp4 hm).pos
    have h3 : c * Nat.card f.ker = 1 := by
      have : c * Nat.card f.ker * oSp4 m = 1 * oSp4 m := by rw [h2, one_mul]
      exact Nat.eq_of_mul_eq_mul_right hpos this
    exact ⟨rfl, injective_of_card_ker (Nat.eq_one_of_mul_eq_one_left h3)⟩
  · obtain ⟨k, rfl, rfl⟩ : ∃ k, m = 3 * k ∧ n = 2 * k := ⟨m - n, by omega, by omega⟩
    exact (not_dvd_oSp4_oG2 (k := k) (by omega) ⟨Nat.card f.ker, by rw [← h2]; ring⟩).elim

end CFSG.Quasithin.Vol2.Ch11.SecA

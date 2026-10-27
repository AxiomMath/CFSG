module

public import CFSG.Quasithin.H13.L1332Inputs
public import CFSG.Timmesfeld.Orders.Classical
public import CFSG.LieType.Simplicity.Classical

public section

namespace CFSG.Quasithin.H13.U3

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Quasithin

theorem card_of_qt13Five {Q : Type} [Group Q] [Finite Q] (h : QT13Five Q) :
    Nat.card Q = 60 ∨ Nat.card Q = 168 ∨ Nat.card Q = 360 ∨ Nat.card Q = 1080 ∨
      Nat.card Q = 6048 := by
  rcases h with h | h | h | ⟨-, hz, h⟩ | h
  · left
    obtain ⟨e⟩ := h
    rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup, Nat.card_fin]
    rfl
  · right; left
    obtain ⟨e⟩ := nonempty_mulEquiv_sl_two_of_lieModel h
    rw [Nat.card_congr e.toEquiv, card_sl_three_zmod_two]
  · right; right; left
    obtain ⟨e⟩ := h
    rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup, Nat.card_fin]
    rfl
  · right; right; right; left
    obtain ⟨e⟩ := h
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (center Q)
    rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup, Nat.card_fin, hz] at h1
    rw [h1]
    rfl
  · right; right; right; right
    exact card_of_statedClassicalModel_psu_three_three
      (LieType.Steinberg.statedClassicalModel_of_lieModel (by decide) h)

theorem center_eq_bot_of_simple_noncomm {Q : Type} [Group Q] [IsSimpleGroup Q]
    (hnab : ¬ ∀ a b : Q, a * b = b * a) : center Q = ⊥ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (center Q) with h | h
  · exact h
  · exfalso
    apply hnab
    intro a b
    have : a ∈ center Q := h ▸ mem_top a
    exact (mem_center_iff.mp this b).symm

theorem card_center_le_three_of_qt13Five {Q : Type} [Group Q] [Finite Q] (h : QT13Five Q) :
    Nat.card (center Q) ≤ 3 := by
  have hsimp : IsSimpleGroup Q → ¬ (Nat.card Q).Prime → Nat.card (center Q) ≤ 3 := by
    intro hs hnp
    have hnab : ¬ ∀ a b : Q, a * b = b * a := by
      intro hc
      let _ : CommGroup Q := { (inferInstance : Group Q) with mul_comm := hc }
      exact hnp (IsSimpleGroup.prime_card (α := Q))
    rw [center_eq_bot_of_simple_noncomm hnab, card_bot]
    norm_num
  have halt : ∀ n : ℕ, 5 ≤ n → Nonempty (Q ≃* alternatingGroup (Fin n)) →
      Nat.card (center Q) ≤ 3 := by
    intro n hn ⟨e⟩
    have hb : center Q = ⊥ := by
      rw [eq_bot_iff]
      intro z hz
      have h1 : e z ∈ center (alternatingGroup (Fin n)) := by
        rw [mem_center_iff] at hz ⊢
        intro g
        obtain ⟨g', rfl⟩ := e.surjective g
        rw [← map_mul, ← map_mul, hz g']
      rw [alternatingGroup.center_eq_bot (by simp; omega), mem_bot] at h1
      rw [mem_bot]
      exact e.injective (h1.trans (map_one e).symm)
    rw [hb, card_bot]
    norm_num
  rcases h with h | h | h | ⟨-, hz, -⟩ | h
  · exact halt 5 le_rfl h
  · have hc := card_of_qt13Five (Or.inr (Or.inl h))
    rcases hc with hc | hc | hc | hc | hc
    · exact hsimp (LieType.Simplicity.fam_PSL_simplicity Q 3 2 1
        (LieType.Steinberg.statedClassicalModel_of_lieModel (by decide) h)).2 (by rw [hc]; norm_num)
    · exact hsimp (LieType.Simplicity.fam_PSL_simplicity Q 3 2 1
        (LieType.Steinberg.statedClassicalModel_of_lieModel (by decide) h)).2 (by rw [hc]; norm_num)
    · exact hsimp (LieType.Simplicity.fam_PSL_simplicity Q 3 2 1
        (LieType.Steinberg.statedClassicalModel_of_lieModel (by decide) h)).2 (by rw [hc]; norm_num)
    · exact hsimp (LieType.Simplicity.fam_PSL_simplicity Q 3 2 1
        (LieType.Steinberg.statedClassicalModel_of_lieModel (by decide) h)).2 (by rw [hc]; norm_num)
    · exact hsimp (LieType.Simplicity.fam_PSL_simplicity Q 3 2 1
        (LieType.Steinberg.statedClassicalModel_of_lieModel (by decide) h)).2 (by rw [hc]; norm_num)
  · exact halt 6 (by norm_num) h
  · exact hz.le
  · have hc : Nat.card Q = 6048 := card_of_statedClassicalModel_psu_three_three
      (LieType.Steinberg.statedClassicalModel_of_lieModel (by decide) h)
    exact hsimp (ClassicalGroups.Unitary.fam_PSU_simplicity Q 3 3 1
      (LieType.Steinberg.statedClassicalModel_of_lieModel (by decide) h)).2 (by rw [hc]; norm_num)

theorem card_le_of_qt13Five {Q : Type} [Group Q] [Finite Q] (h : QT13Five Q) :
    Nat.card Q ≤ 6048 := by
  rcases card_of_qt13Five h with h | h | h | h | h <;> omega

theorem not_qt13Five_of_psl3 {Q : Type} [Group Q] [Finite Q] {p : ℕ} (hp2 : p ≠ 2)
    (h : CFSG.Assembly.LowTwoRank.StatedClassicalModel Q .PSL 3 p 1) : ¬ QT13Five Q := by
  intro hq
  obtain ⟨⟨hp, -, -, -, -⟩, K, _, _, hK, ⟨e⟩⟩ := h
  rw [pow_one] at hK
  have hp3 : 3 ≤ p := by have := hp.two_le; omega
  have hdvd : Nat.gcd 3 (p - 1) ∣ p ^ 3 * ((p ^ 2 - 1) * (p ^ 3 - 1)) := by
    have h1 : p - 1 ∣ p ^ 3 - 1 := Nat.sub_one_dvd_pow_sub_one p 3
    exact ((Nat.gcd_dvd_right 3 (p - 1)).trans h1).trans
      ((Dvd.intro_left _ rfl).trans (Dvd.intro_left _ rfl))
  have hcard : Nat.card Q * Nat.gcd 3 (p - 1) = p ^ 3 * ((p ^ 2 - 1) * (p ^ 3 - 1)) := by
    rw [Nat.card_congr e.toEquiv,
      CFSG.Timmesfeld.ClassicalOrders.card_statedProj_statedSL (by norm_num), hK]
    have : ∏ j ∈ Finset.Icc 2 3, (p ^ j - 1) = (p ^ 2 - 1) * (p ^ 3 - 1) := by
      rw [show Finset.Icc 2 3 = {2, 3} by decide, Finset.prod_pair (by norm_num)]
    rw [this, show 3 * (3 - 1) / 2 = 3 by norm_num]
    exact Nat.div_mul_cancel hdvd
  have hle := card_le_of_qt13Five hq
  have hg : Nat.gcd 3 (p - 1) ≤ 3 := Nat.le_of_dvd (by norm_num) (Nat.gcd_dvd_left 3 (p - 1))
  rcases Nat.lt_or_ge p 5 with h5 | h5
  · have hp3' : p = 3 := by
      rcases Nat.lt_or_ge p 4 with h4 | h4
      · omega
      · exfalso
        have : p = 4 := by omega
        rw [this] at hp
        norm_num at hp
    subst hp3'
    norm_num at hcard
    rcases card_of_qt13Five hq with h | h | h | h | h <;> omega
  · have h1 : 125 ≤ p ^ 3 := by
      calc 125 = 5 ^ 3 := by norm_num
        _ ≤ p ^ 3 := Nat.pow_le_pow_left h5 3
    have h2 : 24 ≤ p ^ 2 - 1 := by
      have : 25 ≤ p ^ 2 := by
        calc 25 = 5 ^ 2 := by norm_num
          _ ≤ p ^ 2 := Nat.pow_le_pow_left h5 2
      omega
    have h3 : 124 ≤ p ^ 3 - 1 := by omega
    have h4 : 125 * (24 * 124) ≤ p ^ 3 * ((p ^ 2 - 1) * (p ^ 3 - 1)) :=
      Nat.mul_le_mul h1 (Nat.mul_le_mul h2 h3)
    have h5' : Nat.card Q * Nat.gcd 3 (p - 1) ≤ 6048 * 3 := Nat.mul_le_mul hle hg
    omega

theorem not_qt13Five_of_sl3 {Q : Type} [Group Q] [Finite Q] {p : ℕ} [hpf : Fact p.Prime]
    (hp2 : p ≠ 2)
    (h : Nonempty (Q ≃* ↥(CFSG.Assembly.LowTwoRank.StatedSL 3 (ZMod p)))) : ¬ QT13Five Q := by
  intro hq
  obtain ⟨e⟩ := h
  have hp : p.Prime := hpf.out
  have hcard : Nat.card Q = p ^ 3 * ((p - 1) * (p + 1)) * ((p - 1) * (p ^ 2 + p + 1)) := by
    rw [Nat.card_congr e.toEquiv]
    exact CFSG.SectionRank.OddCover.card_statedSL_three_eq_mul (by rw [Nat.card_zmod])
  have hle := card_le_of_qt13Five hq
  have hp3 : 3 ≤ p := by have := hp.two_le; omega
  have h1 : 27 ≤ p ^ 3 := by
    calc 27 = 3 ^ 3 := by norm_num
      _ ≤ p ^ 3 := Nat.pow_le_pow_left hp3 3
  have h2 : 2 * 4 ≤ (p - 1) * (p + 1) := Nat.mul_le_mul (by omega) (by omega)
  have h3 : 2 * 13 ≤ (p - 1) * (p ^ 2 + p + 1) := by
    have : 9 ≤ p ^ 2 := by
      calc 9 = 3 ^ 2 := by norm_num
        _ ≤ p ^ 2 := Nat.pow_le_pow_left hp3 2
    exact Nat.mul_le_mul (by omega) (by omega)
  have h4 : 27 * (2 * 4) * (2 * 13) ≤ Nat.card Q := by
    rw [hcard]
    exact Nat.mul_le_mul (Nat.mul_le_mul h1 h2) h3
  have h5 : p = 3 := by
    by_contra hne
    have hp5 : 5 ≤ p := by
      rcases Nat.lt_or_ge p 5 with h | h
      · have : p = 4 := by omega
        rw [this] at hp
        norm_num at hp
      · exact h
    have h6 : 125 ≤ p ^ 3 := by
      calc 125 = 5 ^ 3 := by norm_num
        _ ≤ p ^ 3 := Nat.pow_le_pow_left hp5 3
    have h7 : 4 * 6 ≤ (p - 1) * (p + 1) := Nat.mul_le_mul (by omega) (by omega)
    have h7' : 4 * 31 ≤ (p - 1) * (p ^ 2 + p + 1) := by
      have : 25 ≤ p ^ 2 := by
        calc 25 = 5 ^ 2 := by norm_num
          _ ≤ p ^ 2 := Nat.pow_le_pow_left hp5 2
      exact Nat.mul_le_mul (by omega) (by omega)
    have h8 : 125 * (4 * 6) * (4 * 31) ≤ Nat.card Q := by
      rw [hcard]
      exact Nat.mul_le_mul (Nat.mul_le_mul h6 h7) h7'
    omega
  subst h5
  norm_num at hcard
  rcases card_of_qt13Five hq with h | h | h | h | h <;> omega

theorem not_qt13Five_of_psp {Q : Type} [Group Q] [Finite Q] {n : ℕ} (hn : Even n)
    (h : CFSG.Assembly.LowTwoRank.StatedClassicalModel Q .PSp 2 2 n) : ¬ QT13Five Q := by
  intro hq
  have hn1 : 1 ≤ n := h.1.2.1
  have hcard := (CFSG.Timmesfeld.card_statedClassicalModel_two h).2.2.1 rfl
  rw [ordBC] at hcard
  have hg : Nat.gcd 2 (2 ^ n - 1) = 1 := by
    refine Nat.coprime_two_left.mpr ?_
    have h2 : 2 ≤ 2 ^ n := by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn1
    obtain ⟨k, hk⟩ : Even (2 ^ n) := (Nat.even_pow' (by omega)).2 even_two
    exact ⟨k - 1, by omega⟩
  rw [hg, Nat.div_one] at hcard
  have hn2 : 2 ≤ n := by
    obtain ⟨k, rfl⟩ := hn
    omega
  have hdvd : 2 ^ 8 ∣ Nat.card Q := by
    rw [hcard]
    have : 2 ^ 8 ∣ (2 ^ n) ^ (2 * 2) := by
      rw [← pow_mul]
      exact Nat.pow_dvd_pow 2 (by omega)
    exact this.trans (Dvd.intro _ rfl)
  rcases card_of_qt13Five hq with h | h | h | h | h <;> rw [h] at hdvd <;> norm_num at hdvd

theorem not_qt13Five_of_m11 {Q : Type} [Group Q] [Finite Q]
    (h : Nonempty (Q ≃* NativeSporadic.Carrier TauCeti.SporadicName.M11)) : ¬ QT13Five Q := by
  intro hq
  obtain ⟨e⟩ := h
  have hcard : Nat.card Q = 7920 := by
    rw [Nat.card_congr e.toEquiv]
    exact CFSG.Sporadic.Mathieu.card_M11
  rcases card_of_qt13Five hq with h | h | h | h | h <;> omega

theorem not_qt13Five_of_he {Q : Type} [Group Q] [Finite Q]
    (h : Nonempty (Q ≃* NativeSporadic.Carrier TauCeti.SporadicName.He)) : ¬ QT13Five Q := by
  intro hq
  obtain ⟨e⟩ := h
  have hcard : Nat.card Q = 4030387200 := by
    rw [Nat.card_congr e.toEquiv]
    exact CFSG.Sporadic.He.card_He
  rcases card_of_qt13Five hq with h | h | h | h | h <;> omega

theorem not_qt13Five_of_psl_two {Q : Type} [Group Q] [Finite Q] {n : ℕ} (hn : n = 4 ∨ n = 5)
    (h : CFSG.Assembly.LowTwoRank.StatedClassicalModel Q .PSL n 2 1) : ¬ QT13Five Q := by
  intro hq
  have hcard := (CFSG.Timmesfeld.card_statedClassicalModel_two h).1 rfl
  rcases hn with rfl | rfl
  · have : ordA (4 - 1) (2 ^ 1) = 20160 := by decide
    rw [this] at hcard
    rcases card_of_qt13Five hq with h | h | h | h | h <;> omega
  · have : ordA (5 - 1) (2 ^ 1) = 9999360 := by decide
    rw [this] at hcard
    rcases card_of_qt13Five hq with h | h | h | h | h <;> omega

end CFSG.Quasithin.H13.U3

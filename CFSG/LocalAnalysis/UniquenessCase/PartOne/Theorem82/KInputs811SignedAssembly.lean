module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.KInputs811SignedModel
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.KInputs811Transport

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.SignedModel

open CFSG.Open Subgroup
open CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82
  (IsSignedCoords IsLie811 LieFam811 qMinusPi qPlusPi prime_and_one_le_of_isLie811
    not_three_dvd_card_center_of_isLie811 not_dvd_card_center_of_isLie811_char
    not_dvd_card_center_of_isLie811_of_dvd_qMinusPi not_dvd_card_center_or_eq_of_isLie811
    card_center_eq_one_of_isLie811_of_ne_l7)

theorem k6c_of_signedModel
    {Y : Type} [Group Y] [Finite Y] {fam : LieFam811} {r f : ℕ} (h : IsLie811 Y fam r f)
    (hM : SignedModelK6c Y) {A : Subgroup Y} (hA : IsElemAbelian 3 A) (h27 : Nat.card A = 27) :
    ∃ c : Multiplicative (Fin 3 → ZMod 3) →* Y, IsSignedCoords A c := by
  obtain ⟨H, _, _, N, _, c₀, e, h₀, hN, hU⟩ := hM
  exact IsSignedCoords.exists_of_model h₀ N hN hU (center Y)
    (not_three_dvd_card_center_of_isLie811 h) e hA h27

theorem k6r_of_signedModel
    {Y : Type} [Group Y] [Finite Y] {fam : LieFam811} {r f : ℕ} (h : IsLie811 Y fam r f)
    (hM : SignedModelK6r Y r) (hr5 : 5 ≤ r) {A : Subgroup Y} (hA : IsElemAbelian 3 A)
    (h27 : Nat.card A = 27) :
    (∀ X : Subgroup Y, X ≤ A → Nat.card X = 3 → 2 ≤ CFSG.pRank r (centralizer (X : Set Y))) ∧
    (∀ c : Multiplicative (Fin 3 → ZMod 3) →* Y, IsSignedCoords A c →
      1 ≤ CFSG.pRank r (centralizer ({c (Multiplicative.ofAdd ![1, 0, 0]),
        c (Multiplicative.ofAdd ![0, 1, 0])} : Set Y)) ∧
      1 ≤ CFSG.pRank r (centralizer ({c (Multiplicative.ofAdd ![1, 1, 1]),
        c (Multiplicative.ofAdd ![0, 0, 1])} : Set Y))) := by
  obtain ⟨H, _, _, N, _, c₀, e, h₀, hN, hU, hr⟩ := hM
  obtain ⟨hNr, hrank⟩ := hr hr5
  haveI : Fact r.Prime := ⟨(prime_and_one_le_of_isLie811 h).1⟩
  exact ModelTransport.k6r_of_model h₀ hN hU (not_three_dvd_card_center_of_isLie811 h) hNr
    (not_dvd_card_center_of_isLie811_char h hr5) e hrank hA h27

theorem k7a_of_signedModel
    {Y : Type} [Group Y] [Finite Y] {fam : LieFam811} {r f : ℕ} (h : IsLie811 Y fam r f)
    (hM : SignedModelK7 Y fam r f) {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hpq : p ∣ qMinusPi r f)
    {A : Subgroup Y} (hA : IsElemAbelian 3 A) (h27 : Nat.card A = 27) :
    2 ≤ CFSG.pRank p (centralizer (A : Set Y)) := by
  obtain ⟨H, _, _, N, _, c₀, e, h₀, hN, hU, ha, -⟩ := hM
  obtain ⟨hNp, h2⟩ := ha p hp hp5 hpq
  haveI : Fact p.Prime := ⟨hp⟩
  exact ModelTransport.two_le_pRank_centralizer_of_model_of_coprime hU hN
    (not_three_dvd_card_center_of_isLie811 h) hNp
    (not_dvd_card_center_of_isLie811_of_dvd_qMinusPi h hp (by omega) hpq) e h₀.isElemAbelian
    h₀.card_eq h2 hA h27

theorem k7b_lin_of_signedModel
    {Y : Type} [Group Y] [Finite Y] {fam : LieFam811} {r f : ℕ} (h : IsLie811 Y fam r f)
    (hM : SignedModelK7 Y fam r f) (hfam : fam = .l6 ∨ fam = .l7) {p : ℕ} (hp : p.Prime)
    (hp5 : 5 ≤ p) (hpq : p ∣ qPlusPi r f) {A : Subgroup Y} (hA : IsElemAbelian 3 A)
    (h27 : Nat.card A = 27) :
    2 ≤ CFSG.pRank p (centralizer (A : Set Y)) := by
  obtain ⟨H, _, _, N, _, c₀, e, h₀, hN, hU, -, hb, -⟩ := hM
  haveI : Fact p.Prime := ⟨hp⟩
  refine ModelTransport.two_le_pRank_centralizer_of_model hU hN
    (not_three_dvd_card_center_of_isLie811 h) ?_ e h₀.isElemAbelian h₀.card_eq
    (hb hfam p hp hp5 hpq) hA h27
  rcases not_dvd_card_center_or_eq_of_isLie811 h hp with h1 | h1
  · exact Or.inl h1
  · exact Or.inr ⟨by omega, le_rfl, h1⟩

theorem k7b_dvd_of_signedModel
    {Y : Type} [Group Y] [Finite Y] {fam : LieFam811} {r f : ℕ} (h : IsLie811 Y fam r f)
    (hM : SignedModelK7 Y fam r f) (hfam : fam = .psp6 ∨ fam = .omega7) {p : ℕ} (hp : p.Prime)
    (hp5 : 5 ≤ p) (hpq : p ∣ qPlusPi r f) {A : Subgroup Y} (hA : IsElemAbelian 3 A)
    (h27 : Nat.card A = 27) :
    ¬ p ∣ Nat.card (centralizer (A : Set Y)) ∧
      ∀ X : Subgroup Y, X ≤ A → Nat.card X = 3 → p ∣ Nat.card (centralizer (X : Set Y)) := by
  obtain ⟨H, _, _, N, _, c₀, e, h₀, hN, hU, -, -, hd⟩ := hM
  obtain ⟨hNp, h1, h2, h3, h4⟩ := hd hfam p hp hp5 hpq
  haveI : Fact p.Prime := ⟨hp⟩
  have hZ1 : Nat.card (center Y) = 1 :=
    card_center_eq_one_of_isLie811_of_ne_l7 h (by rcases hfam with rfl | rfl <;> decide)
  have hZp : ¬ p ∣ Nat.card (center Y) := fun hd =>
    hp.one_lt.ne' (Nat.dvd_one.1 (hZ1 ▸ hd))
  exact ⟨ModelTransport.not_dvd_card_centralizer_of_model hU hN
      (not_three_dvd_card_center_of_isLie811 h) hNp hZp e h₀.isElemAbelian h₀.card_eq h1 hA h27,
    ModelTransport.dvd_card_centralizer_points_of_model h₀ hN hU
      (not_three_dvd_card_center_of_isLie811 h) hNp hZp e h2 h3 h4 hA h27⟩

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.SignedModel

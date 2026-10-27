module

public import CFSG.Quasithin.EmptyFaithful.S146zYCfg
public import CFSG.Quasithin.Vol2.F134L2
import CFSG.Adapters.StatedClassicalSmallOrders

public section

namespace CFSG.Quasithin.S146zY

open CFSG.Assembly.LowTwoRank CFSG.Quasithin.F134
open scoped MatrixGroups

theorem false_of_card_twentyFive_of_center {X Y : Type*} [Group X] [Group Y] {Q : Subgroup X}
    (hQ : Nat.card Q = 25) (e : Q ≃* Y) (hY : Subgroup.center Y = ⊥) : False := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have : IsMulCommutative Q :=
    IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := 5) (by simpa using hQ)
  have hc : Subgroup.center Q = ⊥ := CFSG.Quasithin.F420.center_eq_bot_of_mulEquiv' e hY
  have htop : (⊤ : Subgroup Q) = ⊥ := Subgroup.center_eq_top.symm.trans hc
  have h1 : Nat.card Q = 1 := by
    rw [← Subgroup.card_top (G := Q), htop, Subgroup.card_bot]
  omega

theorem noElemTwentyFive_psl2
    {p f : ℕ} [hp : Fact p.Prime] (hp5 : p ≠ 5) (hf : 1 ≤ f) :
    NoElemTwentyFive PSL(2, GaloisField p f) := by
  intro H hH hexp
  have hp25 : ∀ m : ℕ, p ^ m ∣ 25 → m = 0 := by
    intro m hm
    by_contra hm0
    have h1 : p ∣ 5 ^ 2 := (dvd_pow_self p hm0).trans (by simpa using hm)
    exact hp5 ((Nat.prime_dvd_prime_iff_eq hp.out (by norm_num)).1
      (hp.out.dvd_of_dvd_pow h1))
  rcases F6.dicksonPSL2_holds p f hf H with
      ⟨-, m, -, hm⟩ | ⟨hc, -⟩ | ⟨z, -, ⟨e⟩⟩ | ⟨-, ⟨e⟩⟩ | ⟨-, ⟨e⟩⟩ | ⟨-, ⟨e⟩⟩ |
      ⟨m, t, P, hPn, -, hPc, hQc, hQt, -, -⟩ | ⟨m, -, ⟨e⟩⟩ | ⟨m, -, ⟨e⟩⟩
  · have := hp25 m (by rw [← hm, hH])
    subst this
    rw [hH] at hm
    norm_num at hm
  · exact not_isCyclic_of_card_twentyFive hH hexp hc
  · have := Nat.card_congr e.toEquiv
    rw [DihedralGroup.nat_card, hH] at this
    omega
  · have := Nat.card_congr e.toEquiv
    rw [card_alternating_four, hH] at this
    omega
  · have := Nat.card_congr e.toEquiv
    rw [card_perm_four, hH] at this
    omega
  · have := Nat.card_congr e.toEquiv
    rw [card_alternating_five, hH] at this
    omega
  · have hHt : Nat.card H = t * p ^ m := by
      rw [Subgroup.card_eq_card_quotient_mul_card_subgroup P, hQt, hPc]
    have hm0 := hp25 m (by rw [← hH, hHt]; exact Dvd.intro_left _ rfl)
    subst hm0
    have hPbot : P = ⊥ := Subgroup.card_eq_one.mp (by rw [hPc, pow_zero])
    subst hPbot
    have := hQc
    exact not_isCyclic_of_card_twentyFive hH hexp
      (isCyclic_of_surjective (QuotientGroup.quotientBot.toMonoidHom)
        QuotientGroup.quotientBot.surjective)
  · exact false_of_card_twentyFive_of_center hH e
      (CFSG.GorensteinWalter.psl2_center_eq_bot (GaloisField p m))
  · exact false_of_card_twentyFive_of_center hH e
      (CFSG.GorensteinWalter.pgl2_center_eq_bot (GaloisField p m))

theorem noElemTwentyFive_of_statedPSL_two
    {X : Type} [Group X] {p f : ℕ} (hp5 : p ≠ 5)
    (h : StatedClassicalModel X .PSL 2 p f) : NoElemTwentyFive X := by
  have : Fact p.Prime := ⟨h.1.1⟩
  obtain ⟨e⟩ := nonempty_mulEquiv_psl2 h
  exact NoElemTwentyFive.of_mulEquiv e (noElemTwentyFive_psl2 hp5 h.1.2.1)

theorem card_psl2_galoisField_odd {p m : ℕ} [hp : Fact p.Prime] (hp2 : p ≠ 2) (hm : m ≠ 0) :
    Nat.card PSL(2, GaloisField p m) = p ^ m * (p ^ (2 * m) - 1) / 2 := by
  have hK : Nat.card (GaloisField p m) = p ^ m := GaloisField.card p m hm
  have hodd : CFSG.GorensteinWalter.IsOddPrimePower (Nat.card (GaloisField p m)) :=
    ⟨p, m, hp.out, hp.out.odd_of_ne_two hp2, Nat.one_le_iff_ne_zero.mpr hm, hK⟩
  have := CFSG.GorensteinWalter.psl2_card_formula (GaloisField p m) hodd
  rw [hK, ← pow_mul, mul_comm m 2] at this
  exact this

theorem card_of_statedPSL_five_one {X : Type} [Group X]
    (h : StatedClassicalModel X .PSL 2 5 1) : Nat.card X = 60 :=
  CFSG.Open.StatedAPI.card_of_statedClassicalModel_psl_two_five h

theorem card_ne_twoHundred_psl2
    {p : ℕ} [Fact p.Prime] (hp5 : p = 5) (H : Subgroup PSL(2, GaloisField p 2)) :
    Nat.card H ≠ 200 := by
  subst hp5
  intro h200
  rcases F6.dicksonPSL2_holds 5 2 (by norm_num) H with
      ⟨-, m, hm2, hm⟩ | ⟨-, hz⟩ | ⟨z, hz, ⟨e⟩⟩ | ⟨-, ⟨e⟩⟩ | ⟨-, ⟨e⟩⟩ | ⟨-, ⟨e⟩⟩ |
      ⟨m, t, P, -, -, hPc, -, hQt, -, htq⟩ | ⟨m, hm, ⟨e⟩⟩ | ⟨m, hm, ⟨e⟩⟩
  · interval_cases m <;> omega
  · rw [h200] at hz
    norm_num at hz
  · have hc := Nat.card_congr e.toEquiv
    rw [DihedralGroup.nat_card, h200] at hc
    have hz100 : z = 100 := by omega
    subst hz100
    norm_num at hz
  · have := Nat.card_congr e.toEquiv
    rw [card_alternating_four, h200] at this
    omega
  · have := Nat.card_congr e.toEquiv
    rw [card_perm_four, h200] at this
    omega
  · have := Nat.card_congr e.toEquiv
    rw [card_alternating_five, h200] at this
    omega
  · have hHt : Nat.card H = t * 5 ^ m := by
      rw [Subgroup.card_eq_card_quotient_mul_card_subgroup P, hQt, hPc]
    rw [h200] at hHt
    have ht12 : t ∣ 12 := by simpa using htq
    have ht : t ≤ 12 := Nat.le_of_dvd (by norm_num) ht12
    have hdvd : 5 ^ m ∣ 200 := Dvd.intro_left t hHt.symm
    have hm3 : m ≤ 3 := by
      by_contra hcon
      have h1 : (625 : ℕ) ≤ 5 ^ m :=
        calc (625 : ℕ) = 5 ^ 4 := by norm_num
          _ ≤ 5 ^ m := Nat.pow_le_pow_right (by norm_num) (by omega)
      have h2 := Nat.le_of_dvd (by norm_num) hdvd
      omega
    interval_cases m
    · omega
    · omega
    · obtain rfl : t = 8 := by omega
      norm_num at ht12
    · omega
  · have hc := Nat.card_congr e.toEquiv
    rw [card_psl2_galoisField_odd (by norm_num) (Nat.pos_of_dvd_of_pos hm (by norm_num)).ne',
      h200] at hc
    rcases (Nat.dvd_prime Nat.prime_two).1 hm with rfl | rfl <;> norm_num at hc
  · have hm1 : m = 1 := by
      have h1 : m ∣ 1 := by
        have : 2 * m ∣ 2 * 1 := by simpa using hm
        exact Nat.dvd_of_mul_dvd_mul_left (by norm_num) this
      exact Nat.dvd_one.mp h1
    subst hm1
    have hc := Nat.card_congr e.toEquiv
    have hK : Nat.card (GaloisField 5 1) = 5 ^ 1 := GaloisField.card 5 1 one_ne_zero
    rw [CFSG.GorensteinWalter.pgl2_card_formula, hK, h200] at hc
    norm_num at hc

theorem facts134Five_psl2Even :
    ∀ n : ℕ,
    NoE25Config fun (X : Type) [Group X] => StatedClassicalModel X .PSL 2 2 n :=
  fun _ => noE25Config_of_noElem fun _ _ h =>
    noElemTwentyFive_of_statedPSL_two (by norm_num) h

theorem facts134Five_psl2Odd :
    ∀ p f : ℕ, p.Prime → p ≠ 2 → (f = 1 ∨ f = 2) →
    NoE25Config fun (X : Type) [Group X] => StatedClassicalModel X .PSL 2 p f := by
  intro p f hp hp2 hf
  by_cases hp5 : p = 5
  · subst hp5
    have : Fact (Nat.Prime 5) := ⟨hp⟩
    rcases hf with rfl | rfl
    · exact noE25Config_of_not_dvd fun X _ h => by
        rw [card_of_statedPSL_five_one h]
        norm_num
    · intro A _ _ L P T hL hcfg
      obtain ⟨e⟩ := nonempty_mulEquiv_psl2 hL
      obtain ⟨H, k, hH, hk, hodd⟩ := E25Config.exists_model hcfg e
      have hcard : Nat.card PSL(2, GaloisField 5 2) = 7800 :=
        (card_psl2_galoisField_odd (p := 5) (by norm_num) two_ne_zero).trans (by norm_num)
      rw [hcard] at hk hodd
      have hk3 : k = 3 := by
        have hk4 : k ≤ 3 := by
          by_contra hcon
          have h16 : 2 ^ 4 ∣ 2 ^ k := pow_dvd_pow 2 (by omega)
          have := h16.trans hk
          norm_num at this
        interval_cases k <;> first | rfl | (norm_num at hodd)
      subst hk3
      exact card_ne_twoHundred_psl2 rfl H (by norm_num [hH])
  · exact noE25Config_of_noElem fun _ _ h => noElemTwentyFive_of_statedPSL_two hp5 h

end CFSG.Quasithin.S146zY

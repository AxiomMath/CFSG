module

public import CFSG.Quasithin.EmptyFaithful.S146zXGOrder
public import CFSG.Quasithin.Background.GoldschmidtS146RFour

public section

namespace CFSG.Quasithin.S146zX

open CFSG.Quasithin CFSG.Assembly.LowTwoRank

theorem not_fourList_of_order {X : Type} [Group X] {c k r : ℕ} (hc : Nat.card X = c)
    (hr : r % 2 = 1) (hck : c = 2 ^ k * r) (hbig : (2 ^ k) ^ 3 ≤ c) (h360 : 360 < c)
    (h2520 : c ≠ 2520) (h20160 : c ≠ 20160) (h9999360 : c ≠ 9999360)
    (hM : ¬ IsSporadic TauCeti.SporadicName.M22 X) : ¬ FourList X := by
  intro hF
  have hfin : Finite X := Nat.finite_of_card_ne_zero (by omega)
  have h7 : ¬ IsAlt 7 X := fun h => h2520 (hc.symm.trans (card_isAlt_seven h))
  have h4 : ¬ IsPSL 4 2 1 X := fun h => h20160 (hc.symm.trans (card_isPSL_four_two h))
  have h5 : ¬ IsPSL 5 2 1 X := fun h => h9999360 (hc.symm.trans (card_isPSL_five_two h))
  have hprof := CFSG.Quasithin.GoldS146R.srcProfile_of_fourList hF h7 hM h4 h5
  rw [hc] at hprof
  refine CFSG.Quasithin.GoldS146R.profile_contra (B := 2 ^ k) hprof (fun N hN => ?_) hbig h360
  rw [hck] at hN
  exact Nat.le_of_dvd (by positivity)
    (CFSG.Quasithin.GoldS146R.two_pow_dvd_of_mul_odd (by omega) hN)

theorem not_fourList_of_he {X : Type} [Group X]
    (h : Nonempty (X ≃* CFSG.Blueprint.NativeSporadic.Carrier TauCeti.SporadicName.He)) :
    ¬ FourList X := by
  have hc : Nat.card X = 4030387200 := by
    rw [Nat.card_congr h.some.toEquiv]
    exact CFSG.Sporadic.He.card_He
  refine not_fourList_of_order (k := 10) (r := 3935925) hc (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  rintro ⟨e⟩
  have h1 : Nat.card X = 443520 := by
    rw [Nat.card_congr e.toEquiv]
    exact CFSG.Sporadic.Mathieu.card_M22
  omega

theorem not_fourList_of_l35 {p : ℕ} [Fact p.Prime] (hp : p = 5) {X : Type} [Group X]
    (h : StatedClassicalModel X StatedLieTag.PSL 3 p 1 ∨
      Nonempty (X ≃* ↥(StatedSL 3 (ZMod p)))) : ¬ FourList X := by
  subst hp
  have hc : Nat.card X = 372000 := by
    rcases h with h | ⟨⟨e⟩⟩
    · exact card_isPSL_three_five h
    · exact card_eq_of_mulEquiv_statedSL_three (K := ZMod 5) (Nat.card_zmod 5) e
  refine not_fourList_of_order (k := 5) (r := 11625) hc (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  intro hM
  have h1 := card_dvd_factorial_of_isSporadic_M22 hM
  rw [hc] at h1
  have h31 : 31 ∣ Nat.factorial 22 := (show 31 ∣ 372000 by norm_num).trans h1
  have := (Nat.Prime.dvd_factorial (by norm_num : Nat.Prime 31)).mp h31
  omega

end CFSG.Quasithin.S146zX

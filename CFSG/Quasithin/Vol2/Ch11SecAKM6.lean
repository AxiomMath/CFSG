module

public import CFSG.Quasithin.Vol2.Ch11SecAKM5
public import CFSG.Quasithin.Vol2.Ch11SecAKE12

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecA

open CFSG.Open CFSG.Blueprint

namespace C10KH

theorem not_dvd_GL6_of {X : Type} [Group X] [Finite X] (hZ : Nat.card (Subgroup.center X) ∣ 3)
    {r : ℕ} (hr3 : Nat.Coprime r 3) (hdvd : r ∣ Nat.card X) (hn : ¬ r ∣ 20158709760) :
    ¬ Nat.card (X ⧸ Subgroup.center X) ∣
      Nat.card (Matrix.GeneralLinearGroup (Fin 6) (ZMod 2)) := by
  rw [card_GL6]
  intro h
  apply hn
  have h1 := (Subgroup.center X).card_eq_card_quotient_mul_card_subgroup
  have hcop : Nat.Coprime r (Nat.card (Subgroup.center X)) := Nat.Coprime.coprime_dvd_right hZ hr3
  rw [h1] at hdvd
  exact (hcop.dvd_of_dvd_mul_right hdvd).trans h

end C10KH


theorem factModulesList3Order_holds : FactModulesList3Order := by
  intro X _ _ h
  have hZ := (C10KH.list3Other_props factList3Table_holds h).2
  have hc11 : Nat.Coprime 11 3 := by norm_num
  have hn11 : ¬ 11 ∣ 20158709760 := by norm_num
  have hc125 : Nat.Coprime 125 3 := by norm_num
  have hn125 : ¬ 125 ∣ 20158709760 := by norm_num
  rcases h with ⟨p, hp, h5, h8, h⟩ | h | ⟨s, h | h⟩ | h | h | h | h | h | h | h | h
  ·
    have hc := H13.NotLie.card_psl2 h
    have hp2 : p ≠ 2 := by rintro rfl; norm_num at h5
    have hg : Nat.gcd 2 (p ^ 1 - 1) = 2 := by
      rw [pow_one]
      exact Nat.gcd_eq_left ((Nat.Prime.even_sub_one hp hp2).two_dvd)
    rw [hg, pow_one] at hc
    have hev : 2 ∣ p * (p ^ 2 - 1) :=
      Dvd.dvd.mul_left (even_iff_two_dvd.mp
        (Nat.Odd.sub_odd ((hp.odd_of_ne_two hp2).pow) odd_one)) p
    have hpX : p ∣ Nat.card X := by
      have h2 : Nat.card X * 2 = p * (p ^ 2 - 1) := by
        rw [hc]
        exact Nat.div_mul_cancel hev
      have h3 : p ∣ Nat.card X * 2 := h2 ▸ dvd_mul_right p _
      exact (Nat.Coprime.dvd_of_dvd_mul_right
        ((Nat.coprime_primes hp Nat.prime_two).mpr hp2) h3)
    refine C10KH.not_dvd_GL6_of hZ ?_ hpX fun hd => ?_
    · exact (Nat.coprime_primes hp Nat.prime_three).mpr (by rintro rfl; norm_num at h5)
    · rcases C10KH.prime_dvd_GL6 hp hd with rfl | rfl | rfl | rfl | rfl <;> revert h5 h8 <;> decide
  ·
    have hc : Nat.card X = 7800 := by
      rw [H13.NotLie.card_psl2 h]
      norm_num
    exact C10KH.not_dvd_GL6_of hZ (r := 13) (by norm_num) (by rw [hc]; norm_num) (by norm_num)
  · cases s
    ·
      have hc : Nat.card X = 378000 := by
        rw [C11P9B.card_of_isSU3 h]
        norm_num
      exact C10KH.not_dvd_GL6_of hZ hc125 (by rw [hc]; norm_num) hn125
    ·
      obtain ⟨K, _, _, hK, ⟨e⟩⟩ := h
      let e₁ : X ≃* Matrix.SpecialLinearGroup (Fin 3) K :=
        e.trans (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 3 K).symm
      have hc : Nat.card X = 372000 := by
        rw [Nat.card_congr e₁.toEquiv,
          CFSG.OrderReductions.LinearOrders.card_specialLinear K 3 (by norm_num), hK]
        decide
      exact C10KH.not_dvd_GL6_of hZ hc125 (by rw [hc]; norm_num) hn125
  · cases s
    ·
      have hc : Nat.card X = 126000 := by
        have h1 := C11P9B.card_mul_gcd_of_isPSU3 (X := X) h
        norm_num at h1
        omega
      exact C10KH.not_dvd_GL6_of hZ hc125 (by rw [hc]; norm_num) hn125
    ·
      have hc := H13.NotLie.card_psl35 h
      exact C10KH.not_dvd_GL6_of hZ hc125 (by rw [hc]; norm_num) hn125
  ·
    obtain ⟨e⟩ := h
    have hc : Nat.card X = 443520 :=
      (Nat.card_congr e.toEquiv).trans CFSG.Sporadic.Mathieu.card_M22
    exact C10KH.not_dvd_GL6_of hZ hc11 (by rw [hc]; norm_num) hn11
  ·
    have hc : Nat.card X = 1330560 := by
      rw [C10KH.card_of_isHat h]
      exact congrArg (· * 3) CFSG.Sporadic.Mathieu.card_M22
    exact C10KH.not_dvd_GL6_of hZ hc11 (by rw [hc]; norm_num) hn11
  ·
    obtain ⟨e⟩ := h
    have hc : Nat.card X = 10200960 := (Nat.card_congr e.toEquiv).trans card_nativeM23_1522
    exact C10KH.not_dvd_GL6_of hZ hc11 (by rw [hc]; norm_num) hn11
  ·
    obtain ⟨e⟩ := h
    let e' : X ≃* ↥CFSG.Sporadic.J1.J := e.trans CFSG.Sporadic.J1.nativeEquiv
    have hc : Nat.card X = 175560 := (Nat.card_congr e'.toEquiv).trans CFSG.Sporadic.J1.card_J
    exact C10KH.not_dvd_GL6_of hZ hc11 (by rw [hc]; norm_num) hn11
  ·
    obtain ⟨e⟩ := h
    have hc : Nat.card X = 604800 := (Nat.card_congr e.toEquiv).trans CFSG.Sporadic.J2.card_J2
    exact C10KH.not_dvd_GL6_of hZ (r := 25) (by norm_num) (by rw [hc]; norm_num) (by norm_num)
  ·
    obtain ⟨e⟩ := h
    have hc : Nat.card X = 86775571046077562880 :=
      (Nat.card_congr e.toEquiv).trans CFSG.Sporadic.J4.card_J4
    exact C10KH.not_dvd_GL6_of hZ hc11 (by rw [hc]; norm_num) hn11
  ·
    obtain ⟨e⟩ := h
    have hc : Nat.card X = 44352000 := (Nat.card_congr e.toEquiv).trans CFSG.Sporadic.HS.card_HS
    exact C10KH.not_dvd_GL6_of hZ hc11 (by rw [hc]; norm_num) hn11
  ·
    obtain ⟨e⟩ := h
    have hc : Nat.card X = 145926144000 :=
      (Nat.card_congr e.toEquiv).trans CFSG.Sporadic.Ru.card_Ru
    exact C10KH.not_dvd_GL6_of hZ (r := 13) (by norm_num) (by rw [hc]; norm_num) (by norm_num)

end CFSG.Quasithin.Vol2.Ch11.SecA

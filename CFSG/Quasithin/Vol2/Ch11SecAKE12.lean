module

public import CFSG.Quasithin.Vol2.Ch11SecAKE11
public import CFSG.Quasithin.EmptyFaithful.T1515eD
public import CFSG.Quasithin.Vol2.Ch11SecA11Ord
public import CFSG.Quasithin.Vol2.Ch11SecAFacts12b

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecA

open CFSG.Open CFSG.Blueprint C10KH

namespace C10KH

theorem pRank_three_congr {X Y : Type} [Group X] [Group Y] [Finite X] [Finite Y] (e : X ≃* Y)
    (h : 2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup Y)) : 2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup X) := by
  rwa [CFSG.SectionRank.pRank_top_eq_of_mulEquiv (by norm_num : 1 < 3) e]

theorem list3Two_of_simple {X : Type} [Group X] [Finite X] [IsSimpleGroup X] {N : ℕ}
    (hN : Nat.card X = N) (hNp : ¬ N.Prime) (h3 : 3 ∣ N) :
    CFSG.IsQuasisimple X ∧ Subgroup.center X = ⊥ ∧ 3 ∣ Nat.card X :=
  ⟨(CFSG.LocalCores.isQuasisimple_of_isSimpleGroup
      (nonabelian_of_simple (X := X) (by rwa [hN]))).1,
    (CFSG.LocalCores.isQuasisimple_of_isSimpleGroup
      (nonabelian_of_simple (X := X) (by rwa [hN]))).2, hN ▸ h3⟩

theorem three_dvd_psl2 {p : ℕ} (hp : p.Prime) (hp11 : 11 ≤ p) :
    3 ∣ p * (p ^ 2 - 1) / 2 ∧ ¬ (p * (p ^ 2 - 1) / 2).Prime := by
  have h3 : p % 3 ≠ 0 := by
    intro h
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).mp (Nat.dvd_of_mod_eq_zero h)
    omega
  have h2 : p % 2 = 1 := (Nat.Prime.eq_one_or_self_of_dvd hp 2 |>.mt (by omega)) |> fun _ =>
    Nat.odd_iff.mp (hp.odd_of_ne_two (by omega))
  have hp2 : p ^ 2 % 3 = 1 := by
    rw [Nat.pow_mod]
    rcases (by omega : p % 3 = 1 ∨ p % 3 = 2) with h | h <;> rw [h]
  have hp2' : p ^ 2 % 2 = 1 := by rw [Nat.pow_mod, h2]
  have h1 : 1 ≤ p ^ 2 := Nat.one_le_pow _ _ hp.pos
  have h6 : 6 ∣ p ^ 2 - 1 := by omega
  obtain ⟨k, hk⟩ := h6
  have hk' : p * (p ^ 2 - 1) / 2 = 3 * (p * k) := by
    rw [hk]
    rw [show p * (6 * k) = 2 * (3 * (p * k)) by ring, Nat.mul_div_cancel_left _ (by norm_num)]
  rw [hk']
  refine ⟨dvd_mul_right 3 _, fun hpr => ?_⟩
  have := (Nat.prime_mul_iff.mp hpr)
  have hk1 : 1 ≤ k := by
    have : 121 ≤ p ^ 2 := by nlinarith
    omega
  have : 2 ≤ p * k := by nlinarith
  rcases Nat.prime_mul_iff.mp hpr with ⟨-, h⟩ | ⟨-, h⟩ <;> omega

end C10KH


theorem factList3Table_holds : FactList3Table := by
  refine ⟨fun X _ _ hX => ?_, fun X _ _ hX => ?_⟩
  · rcases hX with h | h | h | h | h | h | h | h | h | h | h
    ·
      obtain ⟨e⟩ := (h : Nonempty (X ≃* alternatingGroup (Fin 7)))
      have : IsSimpleGroup X := @MulEquiv.isSimpleGroup _ _ _ _ H13.NotLie.isSimpleGroup_alt7 e
      have hN : Nat.card X = 2520 := (Nat.card_congr e.toEquiv).trans H13.NotLie.card_alt7
      exact list3One_of_simple hN (by norm_num)
        (pRank_three_congr e (CFSG.Quasithin.A3Facts.two_le_pRank_alternating (by norm_num)))
        (psleps3_of_card_2520 hN)
    ·
      have hN : Nat.card X = 7560 := by rw [card_of_isHat h, H13.NotLie.card_alt7]
      exact list3One_of_hat h (CFSG.Quasithin.A3Facts.two_le_pRank_alternating (by norm_num))
        (psleps3_of_card_7560 hN)
    ·
      obtain ⟨e⟩ := h
      obtain ⟨hfin, -, hs⟩ := CFSG.Sporadic.Mathieu.fam_m22_simplicity
      have : Finite (CFSG.Blueprint.NativeSporadic.Carrier .M22) := hfin
      have : IsSimpleGroup X := @MulEquiv.isSimpleGroup _ _ _ _ hs e
      have hN : Nat.card X = 443520 :=
        (Nat.card_congr e.toEquiv).trans CFSG.Sporadic.Mathieu.card_M22
      exact list3One_of_simple hN (by norm_num) (pRank_three_congr e two_le_pRank_M22_1515e)
        (psleps3_of_card_443520 hN)
    ·
      obtain ⟨hfin, -, -⟩ := CFSG.Sporadic.Mathieu.fam_m22_simplicity
      have hN : Nat.card X = 1330560 := by
        rw [card_of_isHat h]
        exact congrArg (· * 3) CFSG.Sporadic.Mathieu.card_M22
      exact list3One_of_hat (S := CFSG.Blueprint.NativeSporadic.M22) h
        two_le_pRank_M22_1515e (psleps3_of_card_1330560 hN)
    ·
      obtain ⟨e⟩ := h
      obtain ⟨hfin, -, hs⟩ := CFSG.Sporadic.Mathieu.fam_m23_simplicity
      have : Finite (CFSG.Blueprint.NativeSporadic.Carrier .M23) := hfin
      have : IsSimpleGroup X := @MulEquiv.isSimpleGroup _ _ _ _ hs e
      have hN : Nat.card X = 10200960 :=
        (Nat.card_congr e.toEquiv).trans card_nativeM23_1522
      exact list3One_of_simple hN (by norm_num) (pRank_three_congr e two_le_pRank_M23_1515e)
        (psleps3_of_card_10200960 hN)
    ·
      obtain ⟨e⟩ := h
      obtain ⟨hfin, -, hs⟩ := CFSG.Sporadic.J2.fam_j2_simplicity
      have : IsSimpleGroup X := @MulEquiv.isSimpleGroup _ _ _ _ hs e
      have hN : Nat.card X = 604800 := (Nat.card_congr e.toEquiv).trans CFSG.Sporadic.J2.card_J2
      have hr := CFSG.QuasithinUnique.Vol2Native.two_le_pRank_three_J2 e
      rw [CFSG.SectionRank.pRank_eq_open_pRank_top] at hr
      exact list3One_of_simple hN (by norm_num) hr (psleps3_of_card_604800 hN)
    ·
      obtain ⟨e⟩ := h
      obtain ⟨hfin, -, hs⟩ := CFSG.Sporadic.J4.fam_j4_simplicity
      have : IsSimpleGroup X := @MulEquiv.isSimpleGroup _ _ _ _ hs e
      have hN : Nat.card X = 86775571046077562880 :=
        (Nat.card_congr e.toEquiv).trans CFSG.Sporadic.J4.card_J4
      have hr := CFSG.QuasithinUnique.Vol2Native.two_le_pRank_three_J4 e
      rw [CFSG.SectionRank.pRank_eq_open_pRank_top] at hr
      exact list3One_of_simple hN (by norm_num) hr (psleps3_of_card_J4 hN)
    ·
      obtain ⟨e⟩ := h
      obtain ⟨hfin, -, hs⟩ := CFSG.Sporadic.HS.fam_hs_simplicity
      have : IsSimpleGroup X := @MulEquiv.isSimpleGroup _ _ _ _ hs e
      have hN : Nat.card X = 44352000 := (Nat.card_congr e.toEquiv).trans CFSG.Sporadic.HS.card_HS
      have hr := CFSG.QuasithinUnique.Vol2Native.two_le_pRank_three_HS e
      rw [CFSG.SectionRank.pRank_eq_open_pRank_top] at hr
      exact list3One_of_simple hN (by norm_num) hr (psleps3_of_card_44352000 hN)
    ·
      obtain ⟨e⟩ := h
      obtain ⟨hfin, -, hs⟩ := CFSG.Sporadic.Ru.fam_ru_simplicity
      have : IsSimpleGroup X := @MulEquiv.isSimpleGroup _ _ _ _ hs e
      have hN : Nat.card X = 145926144000 :=
        (Nat.card_congr e.toEquiv).trans CFSG.Sporadic.Ru.card_Ru
      have hr := CFSG.QuasithinUnique.Vol2Native.two_le_pRank_three_Ru e
      rw [CFSG.SectionRank.pRank_eq_open_pRank_top] at hr
      exact list3One_of_simple hN (by norm_num) hr (psleps3_of_card_145926144000 hN)
    ·
      exact list3One_su35 h
    ·
      have : IsSimpleGroup X := (CFSG.ClassicalGroups.Unitary.fam_PSU_simplicity X 3 5 1 h).2
      have hN : Nat.card X = 126000 := by
        have hc := C11P9B.card_mul_gcd_of_isPSU3 (X := X) h
        norm_num at hc
        omega
      exact list3One_of_simple hN (by norm_num) (two_le_pRank_psu35 h)
        (psleps3_of_card_126000 hN)
  · rcases hX with ⟨p, hp, hp11, h⟩ | h | h | h | h
    ·
      have : IsSimpleGroup X := (CFSG.LieType.Simplicity.fam_PSL_simplicity X 2 p 1 h).2
      have hc := H13.NotLie.card_psl2 h
      have hg : Nat.gcd 2 (p ^ 1 - 1) = 2 := by
        rw [pow_one]
        exact Nat.gcd_eq_left ((Nat.Prime.even_sub_one hp (by omega)).two_dvd)
      rw [hg, pow_one] at hc
      obtain ⟨h3, hnp⟩ := three_dvd_psl2 hp hp11
      exact list3Two_of_simple hc hnp h3
    ·
      have : IsSimpleGroup X := (CFSG.LieType.Simplicity.fam_PSL_simplicity X 2 5 2 h).2
      have hc : Nat.card X = 7800 := by
        rw [H13.NotLie.card_psl2 h]
        norm_num
      exact list3Two_of_simple hc (by norm_num) (by norm_num)
    ·
      obtain ⟨K, _, _, hK, ⟨e⟩⟩ := h
      let e₁ : X ≃* Matrix.SpecialLinearGroup (Fin 3) K :=
        e.trans (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 3 K).symm
      have hN : Nat.card X = 372000 := by
        rw [Nat.card_congr e₁.toEquiv,
          CFSG.OrderReductions.LinearOrders.card_specialLinear K 3 (by norm_num), hK]
        decide
      have hq : CFSG.IsQuasisimple X := CFSG.LocalCores.isQuasisimple_of_mulEquiv e₁.symm
        (CFSG.LieType.Universal.SpecialLinear.isQuasisimple 2 K le_rfl)
      have hZ : Nat.card (Subgroup.center X) = 1 := by
        have h1 := (Subgroup.center X).card_eq_card_quotient_mul_card_subgroup
        rw [hN, H13.NotLie.card_sl35_quot ⟨K, inferInstance, inferInstance, hK, ⟨e⟩⟩] at h1
        omega
      exact ⟨hq, Subgroup.eq_bot_of_card_eq _ hZ, by rw [hN]; norm_num⟩
    ·
      have : IsSimpleGroup X := (CFSG.LieType.Simplicity.fam_PSL_simplicity X 3 5 1 h).2
      exact list3Two_of_simple (H13.NotLie.card_psl35 h) (by norm_num) (by norm_num)
    ·
      obtain ⟨e⟩ := h
      let e' : X ≃* ↥CFSG.Sporadic.J1.J := e.trans CFSG.Sporadic.J1.nativeEquiv
      have := CFSG.Sporadic.J1.isSimpleGroup_J
      have : IsSimpleGroup X := e'.isSimpleGroup
      have hN : Nat.card X = 175560 :=
        (Nat.card_congr e'.toEquiv).trans CFSG.Sporadic.J1.card_J
      exact list3Two_of_simple hN (by norm_num) (by norm_num)

end CFSG.Quasithin.Vol2.Ch11.SecA

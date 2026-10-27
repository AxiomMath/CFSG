module

public import CFSG.Quasithin.Vol2.Ch11SecAKE14
public import CFSG.RankThree.PartOne.S12K.Rigidity
public import CFSG.Quasithin.Vol2.Ch11SecAKM1

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecA

open CFSG.Open CFSG.Blueprint CFSG.Timmesfeld

namespace C10KH

theorem not_dvd_GL_of_ppd {X : Type} [Group X] [Finite X] (hZ : Nat.card (Subgroup.center X) ∣ 3)
    {m r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) (hr3 : r ≠ 3) (hdvd : r ∣ Nat.card X)
    (hprim : ∀ j, 1 ≤ j → j ≤ m → ¬ r ∣ 2 ^ j - 1) :
    ¬ Nat.card (X ⧸ Subgroup.center X) ∣
      Nat.card (Matrix.GeneralLinearGroup (Fin m) (ZMod 2)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro h
  have hcop : Nat.Coprime r (Nat.card (Subgroup.center X)) :=
    Nat.Coprime.coprime_dvd_right hZ ((Nat.coprime_primes hr Nat.prime_three).mpr hr3)
  rw [(Subgroup.center X).card_eq_card_quotient_mul_card_subgroup] at hdvd
  have h1 := (hcop.dvd_of_dvd_mul_right hdvd).trans h
  rw [CFSG.SectionRank.Ccomm.card_GL_zmod] at h1
  obtain ⟨i, -, hi⟩ := (Prime.dvd_finsetProd_iff hr.prime _).mp h1
  have hi' : (i : ℕ) < m := i.2
  have hfac : 2 ^ m - 2 ^ (i : ℕ) = 2 ^ (i : ℕ) * (2 ^ (m - i) - 1) := by
    rw [Nat.mul_sub_one, ← pow_add, Nat.add_sub_cancel' hi'.le]
  rw [hfac] at hi
  rcases hr.dvd_mul.mp hi with h2 | h2
  · exact hr2 ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).mp (hr.dvd_of_dvd_pow h2))
  · exact hprim (m - i) (by omega) (by omega) h2

theorem ppd_not_dvd {r k m : ℕ} (h : IsPrimitivePrimeDivisor r k) (hk : m < k) :
    ∀ j, 1 ≤ j → j ≤ m → ¬ r ∣ 2 ^ j - 1 := fun j hj hjm hd =>
  absurd (Nat.le_of_dvd (by omega) ((h.dvd_sub_one_iff (by omega) j).mp hd)) (by omega)

theorem ppd_ne_two_three {r k : ℕ} (h : IsPrimitivePrimeDivisor r k) (hk : 3 ≤ k) :
    r ≠ 2 ∧ r ≠ 3 :=
  ⟨h.ne_two (by omega), fun h3 => by
    have := h.eq_two_of_dvd_three (by omega) (h3 ▸ dvd_rfl)
    omega⟩

theorem ppd_twelve_dvd {r n : ℕ} (hn : 1 ≤ n) (h : IsPrimitivePrimeDivisor r (12 * n)) :
    r ∣ (2 ^ n) ^ 6 + 1 ∧ r ∣ (2 ^ n) ^ 8 + (2 ^ n) ^ 4 + 1 := by
  have hk : 0 < 12 * n := by omega
  refine ⟨?_, ?_⟩
  · rw [← pow_mul]
    refine (h.dvd_add_one_iff hk _).mpr ⟨⟨1, by ring⟩, fun ⟨c, hc⟩ => ?_⟩
    have h' : n * 6 = n * (12 * c) := by rw [hc]; ring
    have := Nat.eq_of_mul_eq_mul_left (by omega) h'
    omega
  · have h1 : (2 ^ n) ^ 12 - 1 = ((2 ^ n) ^ 4 - 1) * ((2 ^ n) ^ 8 + (2 ^ n) ^ 4 + 1) := by
      have h2 : 1 ≤ (2 ^ n) ^ 4 := Nat.one_le_pow _ _ (Nat.pow_pos (by norm_num))
      have h3 : 1 ≤ (2 ^ n) ^ 12 := Nat.one_le_pow _ _ (Nat.pow_pos (by norm_num))
      zify [h2, h3]
      ring
    have h4 : r ∣ (2 ^ n) ^ 12 - 1 := by rw [← pow_mul, mul_comm]; exact h.dvd
    rw [h1] at h4
    rcases h.prime.dvd_mul.mp h4 with h5 | h5
    · rw [← pow_mul] at h5
      have := (h.dvd_sub_one_iff hk _).mp h5
      exact absurd (Nat.le_of_dvd (by omega) this) (by omega)
    · exact h5

end C10KH


theorem factModulesList2Bang_holds : FactModulesList2Bang := by
  intro X _ _ n hn h
  have hZ := (factList2Table_holds X n hn (Or.inr (Or.inr h))).2.1
  rcases h with h | h | h | h | ⟨⟨m, rfl⟩, h⟩
  ·
    obtain ⟨r, hr⟩ := exists_isPrimitivePrimeDivisor (k := 4 * n) (by omega) (by omega)
    obtain ⟨hr2, hr3⟩ := C10KH.ppd_ne_two_three hr (by omega)
    refine C10KH.not_dvd_GL_of_ppd hZ hr.prime hr2 hr3 ?_ (C10KH.ppd_not_dvd hr (by omega))
    have hg : Nat.gcd 2 (2 ^ n - 1) = 1 :=
      Nat.coprime_two_left.mpr (Nat.Even.sub_odd Nat.one_le_two_pow
        ((Nat.even_pow' (by omega)).mpr even_two) odd_one)
    rw [(card_statedClassicalModel_two (h : StatedClassicalModel X .PSp 2 2 n)).2.2.1 rfl, ordBC,
      hg, Nat.div_one]
    refine Dvd.dvd.mul_left ((?_ : r ∣ (2 ^ n) ^ (2 * 2) - 1).trans
      (Finset.dvd_prod_of_mem (fun i => (2 ^ n) ^ (2 * i) - 1)
        (by decide : 2 ∈ Finset.Icc 1 2))) _
    rw [← pow_mul, show n * (2 * 2) = 4 * n by ring]
    exact hr.dvd
  ·
    obtain ⟨r, hr⟩ := exists_isPrimitivePrimeDivisor (k := 6 * n) (by omega) (by omega)
    obtain ⟨hr2, hr3⟩ := C10KH.ppd_ne_two_three hr (by omega)
    refine C10KH.not_dvd_GL_of_ppd hZ hr.prime hr2 hr3 ?_ (C10KH.ppd_not_dvd hr (by omega))
    rw [ExceptionalOrders.card_of_untwistedChevalleyModel_G2 h.2, ordG2]
    refine Dvd.dvd.mul_right (Dvd.dvd.mul_left ?_ _) _
    rw [← pow_mul, show n * 6 = 6 * n by ring]
    exact hr.dvd
  ·
    obtain ⟨r, hr⟩ := exists_isPrimitivePrimeDivisor (k := 12 * n) (by omega) (by omega)
    obtain ⟨hr2, hr3⟩ := C10KH.ppd_ne_two_three hr (by omega)
    refine C10KH.not_dvd_GL_of_ppd hZ hr.prime hr2 hr3 ?_ (C10KH.ppd_not_dvd hr (by omega))
    rw [CFSG.RankThree.PartOne.S12K.card_of_reeTitsModel_twistedF4 h,
      ordTwistedF4]
    exact Dvd.dvd.mul_right (Dvd.dvd.mul_right (Dvd.dvd.mul_right
      (Dvd.dvd.mul_left (C10KH.ppd_twelve_dvd (by omega) hr).1 _) _) _) _
  ·
    obtain ⟨r, hr⟩ := exists_isPrimitivePrimeDivisor (k := 12 * n) (by omega) (by omega)
    obtain ⟨hr2, hr3⟩ := C10KH.ppd_ne_two_three hr (by omega)
    refine C10KH.not_dvd_GL_of_ppd hZ hr.prime hr2 hr3 ?_ (C10KH.ppd_not_dvd hr (by omega))
    rw [ExceptionalOrders.card_of_twistedChevalleyModel_D4_two (by omega) h.2, ordTrialityD4]
    exact Dvd.dvd.mul_right (Dvd.dvd.mul_right
      (Dvd.dvd.mul_left (C10KH.ppd_twelve_dvd (by omega) hr).2 _) _) _
  ·
    have hm : 1 ≤ m := by omega
    rw [show 3 * m / 3 = m by omega] at h
    obtain ⟨r, hr⟩ := exists_isPrimitivePrimeDivisor (k := 12 * m) (by omega) (by omega)
    obtain ⟨hr2, hr3⟩ := C10KH.ppd_ne_two_three hr (by omega)
    refine C10KH.not_dvd_GL_of_ppd hZ hr.prime hr2 hr3 ?_ (C10KH.ppd_not_dvd hr (by omega))
    rw [ExceptionalOrders.card_of_twistedChevalleyModel_D4_two hm h.2, ordTrialityD4]
    exact Dvd.dvd.mul_right (Dvd.dvd.mul_right
      (Dvd.dvd.mul_left (C10KH.ppd_twelve_dvd hm hr).2 _) _) _

end CFSG.Quasithin.Vol2.Ch11.SecA

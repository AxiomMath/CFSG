module

public import CFSG.Quasithin.Vol2.Ch8Sec2L825L
public import CFSG.Quasithin.Vol2.Ch8Sec2HFactsL3B
public import CFSG.Quasithin.Background.HFL3Res

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Quasithin.E3 CFSG.Quasithin.H CFSG.Quasithin.ASInputs
open scoped IsMulCommutative

section L823Res

theorem not_dvd_823 {m : ℕ} (hm : 1 ≤ m) :
    ¬ 2 ^ (4 * m) - 1 ∣ 2 * (3 * m) * (2 * (2 ^ (2 * (3 * m)) - 1)) := by
  intro hdvd
  set a := 2 ^ (2 * m) with ha
  have ha1 : 2 ≤ a := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ a := Nat.pow_le_pow_right (by norm_num) (by omega)
  have e1 : 2 ^ (4 * m) - 1 = (a - 1) * (a + 1) := by
    have : 2 ^ (4 * m) = a * a := by rw [ha, ← pow_add]; ring_nf
    rw [this]
    have ha0 : 1 ≤ a := by omega
    zify [ha0, Nat.one_le_iff_ne_zero.mpr (mul_ne_zero (by omega : a ≠ 0) (by omega : a ≠ 0))]
    ring
  set R := a * (a + 1) + 1 with hR
  have e2 : 2 ^ (2 * (3 * m)) - 1 = (a - 1) * R := by
    have : 2 ^ (2 * (3 * m)) = a * a * a := by rw [ha, ← pow_add, ← pow_add]; ring_nf
    rw [this, hR]
    have h3 : 1 ≤ a * a * a := Nat.one_le_iff_ne_zero.mpr (by positivity)
    have ha0 : 1 ≤ a := by omega
    zify [ha0, h3]
    ring
  rw [e1, e2] at hdvd
  have h1 : (a - 1) * (a + 1) ∣ (a - 1) * (2 * (3 * m) * (2 * R)) := by
    have : 2 * (3 * m) * (2 * ((a - 1) * R)) = (a - 1) * (2 * (3 * m) * (2 * R)) := by ring
    rwa [this] at hdvd
  have h2 : a + 1 ∣ 2 * (3 * m) * (2 * R) := Nat.dvd_of_mul_dvd_mul_left (by omega) h1
  have hcopR : Nat.Coprime (a + 1) R := by
    rw [hR, mul_comm, Nat.coprime_mul_left_add_right]
    exact Nat.coprime_one_right _
  have hodd : Odd (a + 1) := by
    rw [ha]
    exact Even.add_one (Nat.even_pow.mpr ⟨even_two, by omega⟩)
  have hcop4 : Nat.Coprime (a + 1) 4 := by
    have h2c : Nat.Coprime (a + 1) 2 := (Nat.coprime_two_right).mpr hodd
    have : (4 : ℕ) = 2 ^ 2 := by norm_num
    rw [this]
    exact Nat.Coprime.pow_right 2 h2c
  have h3 : a + 1 ∣ 4 * (3 * m) * R := by
    have : 2 * (3 * m) * (2 * R) = 4 * (3 * m) * R := by ring
    rwa [this] at h2
  have h4 : a + 1 ∣ 4 * (3 * m) := hcopR.dvd_of_dvd_mul_right h3
  have h5 : a + 1 ∣ 3 * m := hcop4.dvd_of_dvd_mul_left h4
  have h6 : a + 1 ≤ 3 * m := Nat.le_of_dvd (by omega) h5
  have h7 : 2 * (2 * m) ≤ a := two_mul_le_two_pow_82 (by omega)
  omega

theorem pow_eq_one_of_large_l3 {V : Type} [CommGroup V] [Finite V] {L M : Subgroup (MulAut V)}
    (hLM : Mathieu.IsOver L M) {n : ℕ} (hn : 1 ≤ n) (hL : BinaryNineTensor L ⊤ ⊥ n)
    {A : Subgroup (MulAut V)} (hAL : A ≤ L) (hAe : IsElemAbelian2 A)
    (hcard : 2 ^ (3 * n) < Nat.card A) {x : MulAut V} (hx : x ∈ M) {Z : Subgroup V}
    (hZA : Z ≤ fixV A) (hZx : Z ≤ fixV (Subgroup.zpowers x)) (hZ : 2 ^ (3 * n) < Nat.card Z) :
    x ^ (2 * n * (2 * (2 ^ (2 * n) - 1))) = 1 := by
  obtain ⟨K, _, _, _, hK, e, hLe, hMN⟩ := exists_model_l3nine hLM hL
  have hK' : Nat.card K = 2 ^ (2 * n) := by rw [hK, ← pow_mul, mul_comm]
  have hA' : A.map (congrHom e) ≤ L3Nine.img hK := by
    rw [← hLe]
    exact Subgroup.map_mono hAL
  have hZA' : Z.map e.toMonoidHom ≤ fixV (A.map (congrHom e)) := by
    rw [fixV_map_congrHom]
    exact Subgroup.map_mono hZA
  have hZx' : Z.map e.toMonoidHom ≤ fixV (Subgroup.zpowers (congrHom e x)) := by
    rw [← MonoidHom.map_zpowers, fixV_map_congrHom]
    exact Subgroup.map_mono hZx
  have h := L3Nine.pow_eq_one_of_large hn hK hA' ((isElemAbelian2_map_congrHom e).2 hAe)
    (by rw [card_map_congrHom]; exact hcard) (hMN ⟨x, hx, rfl⟩) hZA' hZx'
    (by rw [Subgroup.card_map_of_injective e.injective]; exact hZ)
  rw [hK'] at h
  exact congrHom_injective e (by rw [map_pow, h, map_one])

variable {G : Type} [Group G] [Finite G]

theorem res823L3_holds (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h39 : A39ForSQTK)
    (hmod : StmtFSUModule) (hE214 : AS_E_2_14) : Res823L3 := by
  intro G _ _ T L I hyp h731 h821 hc hcase H h k hH hhH hC n hrow hk3
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hV, hN⟩ := hmod G T L I hyp.fsu
  have hNM := normalizer_fsuV_le_fsuM h37 h38 h39 hyp.fsu hV hN
  have hLM := isOver_autI_82 hV hNM
  have hn1 : 1 ≤ n := hrow.1
  obtain ⟨m, rfl⟩ : 3 ∣ n := by omega
  have hk : k = 4 * m := by omega
  subst hk
  have hm1 : 1 ≤ m := by omega
  have hk2 : 2 ≤ 4 * m := by omega
  obtain ⟨-, hhI, hIC, hZ1, -, hSyl, hMIeq, hker, -, hcases, hVZ, hBor, hA7, hAC, -, -, hm, -,
    h28, hchar, hTI⟩ := hC
  have hVZ' : E2.star (fsuM T L ⊓ ch82I (fsuV T I) h) (ch82I (fsuV T I) h) (fsuV T I) ≤
      E2.star (fsuM T L ⊓ ch82I (fsuV T I) h) (ch82I (fsuV T I) h)
        (T ⊓ ch82I (fsuV T I) h) := by
    rw [hVZ]
    exact inf_le_left
  have hPSL : IsPSL 2 2 (4 * m)
      (E2.StarQuot (fsuM T L ⊓ ch82I (fsuV T I) h) (ch82I (fsuV T I) h)) := by
    rcases hcases with ⟨h21, -⟩ | hP | hS
    · omega
    · exact hP
    · exact absurd hS (not_isSz_of_even_82 ⟨2 * m, by ring⟩)
  obtain ⟨-, -, h7, -, h9⟩ :=
    e214_82 hE214 hV hhI hIC hZ1 h28 hchar hTI (Or.inr (Or.inl ⟨4 * m, hPSL⟩))
  obtain ⟨x, -, hxN, -, hxV, hxo⟩ := exists_cartan_elt_82 hV hk2 hhI hSyl hMIeq hker
    (Or.inl hPSL) hVZ' hBor (h9 (4 * m) (by omega) hPSL)
  have hxo' := hxo hPSL
  obtain ⟨hAel, hAN⟩ := ch82A_facts_82 hV hA7
  have hAel2 := isElemAbelian2_autI hV hAel hAN
  have hAbM : autI hV (ch82A (fsuV T I) h) ≤ autI hV ⊤ := autI_mono hV le_top
  have hrkAm := rk_autI_eq_mQuot hV hAN
  rw [hAC] at hm hrkAm
  have hA : ch82A (fsuV T I) h = conjSubgroup (fsuV T I) h⁻¹ ⊓
      Subgroup.normalizer (fsuV T I : Set G) := by rw [hA7, conjSub_eq_conjSubgroup_82]
  have hrkA2 : rk ↥(autI hV (ch82A (fsuV T I) h)) ≤ CFSG.Open.pRank 2 (autI hV ⊤) := by
    rw [hA]
    exact rk_autI_le_pRank hV
  have hm2 := (hTab82Nine_holds (IntMod (fsuV T I) hV) (autI hV (fsuL0 T L)) (autI hV ⊤) hLM
    (3 * m) hn1 hrow.2).1
  have hcl := hIC.2.2.2.1
  rw [inf_inf_eq_82 (M := fsuM T L) hIC.1] at hcl
  have hP := pair_82 hV h28.le_T h28.normal_T hSyl hMIeq hhI hcl
  have hZA : (ch82ZI (fsuV T I) h).comap (E3.valHom hV) ≤
      fixV (autI hV (ch82A (fsuV T I) h)) := by
    rw [fixV_autI_eq_comap hV hAN]
    exact Subgroup.comap_mono (ch82ZI_le_ch82U_82 hP)
  have hZx : (ch82ZI (fsuV T I) h).comap (E3.valHom hV) ≤
      fixV (Subgroup.zpowers (convI hV ⟨x, hxN⟩)) := by
    rw [← autI_zpowers_82 hV hxN, fixV_autI_eq_comap hV (Subgroup.zpowers_le.mpr hxN), hxV]
  have hZidx : rkIdx ((ch82ZI (fsuV T I) h).comap (E3.valHom hV)) =
      mQuot (fsuV T I) (ch82ZI (fsuV T I) h) :=
    (mQuot_eq_rkIdx_comap hV (U := ch82ZI (fsuV T I) h) inf_le_left).symm
  have hV9 : rk ↥(fsuV T I) = 9 * (3 * m) :=
    rk_eq_of_card_82 (card_of_binaryNineTensor_82 hrow.1 hrow.2)
  have hrkZ := rk_add_rkIdx hV ((ch82ZI (fsuV T I) h).comap (E3.valHom hV))
  have hV9' : rk (IntMod (fsuV T I) hV) = 9 * (3 * m) := hV9
  have hrel : rk ↥(autI hV (ch82A (fsuV T I) h)) + 4 * m =
      rkIdx ((ch82ZI (fsuV T I) h).comap (E3.valHom hV)) := by
    rw [hrkAm, hm, hZidx]
  obtain ⟨-, hL3, -, hL6, -⟩ := hL3Nine82_holds (IntMod (fsuV T I) hV) (autI hV (fsuL0 T L))
    (autI hV ⊤) hLM (3 * m) hn1 hrow.2
  have hidx := CFSG.Quasithin.rkIdx_anti hZA
  by_cases hsmall : rk ↥(autI hV (ch82A (fsuV T I) h)) ≤ 2 * (4 * m)
  ·
    have hcardA : Nat.card ↥(autI hV (ch82A (fsuV T I) h)) ≤ 2 ^ (2 * (4 * m)) := by
      rw [card_eq_two_pow_rk hAel2]
      exact Nat.pow_le_pow_right (by norm_num) hsmall
    obtain ⟨hAc, hZc⟩ := h7 (4 * m) (Or.inl hPSL) hcardA
      (one_lt_qOf_82 hV (ch82I (fsuV T I) h) (not_isFFModule_of_hyp702 hyp hV hNM))
    have hrkA8 : rk ↥(autI hV (ch82A (fsuV T I) h)) = 2 * (4 * m) := by
      unfold rk
      rw [hAc, padicValNat.prime_pow]
    have hZq : mQuot (fsuV T I) (ch82ZI (fsuV T I) h) = 3 * (4 * m) := by
      unfold mQuot
      rw [hZc, padicValNat.prime_pow]
    have hAL := hL6 _ hAbM hAel2 (by omega)
    have h5 := hL3 _ hAbM hAel2 (Or.inr ⟨hAL, by omega⟩)
    omega
  · push Not at hsmall
    have hAL := hL6 _ hAbM hAel2 (by omega)
    have h5 := hL3 _ hAbM hAel2 (Or.inr ⟨hAL, by omega⟩)
    have hcardA : 2 ^ (3 * (3 * m)) < Nat.card ↥(autI hV (ch82A (fsuV T I) h)) := by
      rw [card_eq_two_pow_rk hAel2]
      exact Nat.pow_lt_pow_right (by norm_num) (by omega)
    have hcardZ : 2 ^ (3 * (3 * m)) <
        Nat.card ↥((ch82ZI (fsuV T I) h).comap (E3.valHom hV)) := by
      rw [card_eq_two_pow (fun v => IntMod.sq_eq_one v)]
      exact Nat.pow_lt_pow_right (by norm_num) (by omega)
    have hpow := pow_eq_one_of_large_l3 hLM hn1 hrow.2 hAL hAel2 hcardA
      (convI_mem_autI hV (Subgroup.mem_top x) hxN) hZA hZx hcardZ
    have hdvd := orderOf_dvd_of_pow_eq_one hpow
    rw [hxo'] at hdvd
    exact not_dvd_823 hm1 hdvd

end L823Res

end CFSG.Quasithin.H13

module

public import CFSG.Quasithin.Vol2.Ch7Lem741

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Quasithin.E3 CFSG.Quasithin.H
open scoped IsMulCommutative

section Module

variable {W : Type*} [CommGroup W] [Finite W]

theorem alphaE_le_of_isFOneOffender (hW : ∀ w : W, w ^ 2 = 1) {M A : Subgroup (MulAut W)}
    (hFF : ¬ IsFFModule M) (hA : IsFOneOffender M A) : alphaE M ≤ rkIdx (fixV A) := by
  obtain ⟨⟨hAM, hA1, hA2⟩, hr⟩ := hA
  have : Finite (MulAut W) := MulEquiv.finite_left
  have hAU : A ≤ M ⊓ centSub (fixV A) := fun a ha => ⟨hAM ha, fun u hu => hu a ha⟩
  have hrkA : rk ↥A ≤ CFSG.Open.pRank 2 (M ⊓ centSub (fixV A)) := rk_le_pRank hAU hA2
  by_cases hk : 2 ≤ rkIdx (fixV A)
  · have hmem : rkIdx (fixV A) ∈ alphaSet M := by
      refine ⟨hk, fixV A, fun htop => ?_, rfl, by omega⟩
      rw [htop] at hk
      simp [rkIdx] at hk
    unfold alphaE
    exact iInf₂_le _ hmem
  · exfalso
    apply hFF
    refine ⟨A, hAM, hA1, hA2, ?_⟩
    have hcardW := card_eq_two_pow_of_isPGroup (isPGroup_two_of_sq_eq_one hW)
    have h1 := (fixV A).card_mul_index
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp
      (hcardW ▸ (fixV A).index_dvd_card)
    have hjk : rkIdx (fixV A) = j := by
      unfold rkIdx
      rw [hj, padicValNat.prime_pow]
    have hA2le : 2 ≤ Nat.card A := by
      have : Nontrivial A := (Subgroup.nontrivial_iff_ne_bot A).mpr hA1
      exact Finite.one_lt_card
    have hj1 : 2 ^ j ≤ 2 := by
      calc 2 ^ j ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) (by omega)
        _ = 2 := by norm_num
    rw [← h1, hj, mul_comm]
    exact Nat.mul_le_mul (hj1.trans hA2le) le_rfl

end Module

section Lift

variable {G : Type} [Group G] [Finite G]

theorem eq_one_of_odd_of_pow_two_pow {M : Type*} [Monoid M] {x : M} (hx : Odd (orderOf x))
    {k : ℕ} (hk : x ^ 2 ^ k = 1) : x = 1 := by
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one hk)
  rcases Nat.eq_zero_or_pos j with h0 | hpos
  · rwa [h0, pow_zero, orderOf_eq_one_iff] at hj
  · rw [hj] at hx
    exact absurd ((Nat.even_pow' hpos.ne').mpr even_two) (Nat.not_even_iff_odd.mpr hx)

theorem exists_odd_lift {V U : Subgroup G} (hV : IsElemAbelian 2 V) (hUV : U ≤ V)
    {y' : MulAut (IntMod V hV)} (hy : y' ∈ autI hV ⊤) (hy1 : y' ≠ 1) (hyo : Odd (orderOf y'))
    (hfix : LeFixI hV U (Subgroup.zpowers y')) :
    ∃ y ∈ Subgroup.normalizer (V : Set G) ⊓ Subgroup.centralizer (U : Set G),
      Odd (orderOf y) ∧ y ∉ Subgroup.centralizer (V : Set G) := by
  obtain ⟨g, -, rfl⟩ := (mem_autI hV).1 hy
  obtain ⟨k, m, hm, hk⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos (g : G)).ne'
  have hyN : (g : G) ^ 2 ^ k ∈ Subgroup.normalizer (V : Set G) := pow_mem g.2 _
  have hconv : convI hV ⟨(g : G) ^ 2 ^ k, hyN⟩ = convI hV g ^ 2 ^ k := by
    rw [← map_pow]
    rfl
  refine ⟨(g : G) ^ 2 ^ k, Subgroup.mem_inf.2 ⟨hyN, ?_⟩, ?_, ?_⟩
  · rw [Subgroup.mem_centralizer_iff]
    intro u hu
    have h1 := hfix (IntMod.mk hV ⟨u, hUV hu⟩) hu (convI hV g ^ 2 ^ k)
      (pow_mem (Subgroup.mem_zpowers _) _)
    rw [← hconv] at h1
    have h2 := congrArg IntMod.val h1
    rw [convI_apply_val] at h2
    change (g : G) ^ 2 ^ k * u * ((g : G) ^ 2 ^ k)⁻¹ = u at h2
    calc u * (g : G) ^ 2 ^ k = ((g : G) ^ 2 ^ k * u * ((g : G) ^ 2 ^ k)⁻¹) * (g : G) ^ 2 ^ k := by
          rw [h2]
      _ = (g : G) ^ 2 ^ k * u := by group
  · refine Odd.of_dvd_nat hm (orderOf_dvd_of_pow_eq_one ?_)
    rw [← pow_mul, ← hk, pow_orderOf_eq_one]
  · intro hc
    have h1 : convI hV ⟨(g : G) ^ 2 ^ k, hyN⟩ = 1 := (convI_eq_one_iff hV _).2 hc
    rw [hconv] at h1
    exact hy1 (eq_one_of_odd_of_pow_two_pow hyo h1)

theorem betaH_le_of_odd {V U : Subgroup G} (hV : IsElemAbelian 2 V) (hUV : U ≤ V) {y : G}
    (hy : y ∈ Subgroup.normalizer (V : Set G) ⊓ Subgroup.centralizer (U : Set G))
    (hyo : Odd (orderOf y)) (hy1 : y ∉ Subgroup.centralizer (V : Set G)) :
    betaH (autI hV ⊤) ≤ (mQuot V U : ℕ∞) := by
  have : Finite (MulAut (IntMod V hV)) := MulEquiv.finite_left
  obtain ⟨hyN, hyC⟩ := hy
  set y' := convI hV ⟨y, hyN⟩ with hy'
  have hy'1 : y' ≠ 1 := fun h => hy1 ((convI_eq_one_iff hV _).1 h)
  have hy'o : Odd (orderOf y') := by
    refine Odd.of_dvd_nat hyo ?_
    have h := orderOf_map_dvd (convI hV) ⟨y, hyN⟩
    rwa [Subgroup.orderOf_mk] at h
  have hfix : ∀ u ∈ U.comap (E3.valHom hV), y' u = u := by
    intro u hu
    refine IntMod.val_injective ?_
    rw [hy', convI_apply_val]
    have h := Subgroup.mem_centralizer_iff.1 hyC u.val hu
    change y * u.val * y⁻¹ = u.val
    rw [← h, mul_inv_cancel_right]
  have hyU : y' ∈ autI hV ⊤ ⊓ centSub (U.comap (E3.valHom hV)) :=
    ⟨convI_mem_autI hV (Subgroup.mem_top y) hyN, hfix⟩
  have hU'top : U.comap (E3.valHom hV) ≠ ⊤ := by
    intro htop
    refine hy'1 (MulEquiv.ext fun u => ?_)
    rw [MulAut.one_apply]
    exact hfix u (htop ▸ Subgroup.mem_top u)
  have hres : twoResidual (autI hV ⊤ ⊓ centSub (U.comap (E3.valHom hV))) ≠ ⊥ := by
    rw [Ne, twoResidual_eq_bot_iff]
    intro hp
    obtain ⟨k, hk⟩ := hp ⟨y', hyU⟩
    exact hy'1 (eq_one_of_odd_of_pow_two_pow hy'o (by simpa using congrArg Subtype.val hk))
  rw [mQuot_eq_rkIdx_comap hV hUV]
  unfold betaH
  exact iInf_le_of_le _ (iInf_le_of_le hU'top (iInf_le _ hres))

end Lift

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G}

theorem exists_odd_741 (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h39 : A39ForSQTK)
    (hmod : StmtFSUModule) (h325 : Stmt3_2_5) (hin : Input8_1_2)
    (hyp : Hyp7_0_2 G T L I) (h731 : Hyp7_3_1 T L I)
    (hML : fsuM T L ≤ Subgroup.normalizer (L : Set G)) (hV : IsElemAbelian 2 (fsuV T I))
    {U : Subgroup G} (hUV : U ≤ fsuV T I)
    (hC : ¬ Subgroup.centralizer (U : Set G) ≤ Subgroup.normalizer (fsuV T I : Set G))
    (hα : (mQuot (fsuV T I) U : ℕ∞) < alphaE (autI hV ⊤)) :
    ∃ y ∈ Subgroup.normalizer (fsuV T I : Set G) ⊓ Subgroup.centralizer (U : Set G),
      Odd (orderOf y) ∧ y ∉ Subgroup.centralizer (fsuV T I : Set G) := by
  obtain ⟨-, hN⟩ := hmod G T L I hyp.fsu
  have hNM := normalizer_fsuV_le_fsuM h37 h38 h39 hyp.fsu hV hN
  have hTL : T ≤ Subgroup.normalizer (L : Set G) := ((le_sup_right.trans hN).trans hNM).trans hML
  by_cases hU1 : U = ⊥
  ·
    subst hU1
    have hres := twoResidual_autI_ne_bot hyp hTL hV hN
    rw [Ne, twoResidual_eq_bot_iff] at hres
    obtain ⟨x, hx⟩ := not_forall.1 (show ¬ ∀ x : ↥(autI hV ⊤), ∃ k : ℕ, x ^ 2 ^ k = 1 from hres)
    obtain ⟨k, m, hm, hk⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos x).ne'
    refine exists_odd_lift hV bot_le (y' := (x : MulAut (IntMod (fsuV T I) hV)) ^ 2 ^ k)
      (pow_mem x.2 _) (fun h => hx ⟨k, Subtype.ext (by simpa using h)⟩) ?_ ?_
    · refine Odd.of_dvd_nat hm (orderOf_dvd_of_pow_eq_one ?_)
      rw [← pow_mul, ← hk, ← Subgroup.orderOf_coe, pow_orderOf_eq_one]
    · intro v hv z _
      have hv1 : v = 1 := IntMod.val_injective (Subgroup.mem_bot.1 hv)
      rw [hv1, map_one]
  · have hTI := isTISetUnder_of_le_normalizer h325 hyp.fsu hTL
    have hCM : ¬ Subgroup.centralizer (U : Set G) ≤ fsuM T L := fun h =>
      hC fun g hg => mem_normalizer_of_ti hTI hUV hU1 (h hg) hg
    rcases hin G T L I hyp h731 hML hV U hUV hU1 hCM with ⟨A, hA, hfix⟩ | ⟨y, hy, hy1, hyo, hfix⟩
    ·
      have h1 := alphaE_le_of_isFOneOffender (fun v => IntMod.sq_eq_one v)
        (not_isFFModule_of_hyp702 hyp hV hNM) hA
      have h2 : rkIdx (fixV A) ≤ mQuot (fsuV T I) U := by
        rw [mQuot_eq_rkIdx_comap hV hUV]
        exact rkIdx_anti ((leFixI_iff hV).1 hfix)
      exact absurd (h1.trans (Nat.cast_le.2 h2)) (not_le.2 hα)
    · exact exists_odd_lift hV hUV hy hy1 hyo hfix

theorem stmt7_4_1_of (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h39 : A39ForSQTK)
    (hmod : StmtFSUModule) (h325 : Stmt3_2_5) (hin : Input8_1_2) : Stmt7_4_1 := by
  intro G _ _ T L I hyp h731 hML hV
  unfold rParam
  refine le_iInf₂ fun U hU => ?_
  obtain ⟨hUV, hC⟩ := hU
  by_cases hα : alphaE (autI hV ⊤) ≤ (mQuot (fsuV T I) U : ℕ∞)
  · exact (min_le_left _ _).trans hα
  · obtain ⟨y, hy, hyo, hy1⟩ :=
      exists_odd_741 h37 h38 h39 hmod h325 hin hyp h731 hML hV hUV hC (not_le.1 hα)
    exact (min_le_right _ _).trans (betaH_le_of_odd hV hUV hy hyo hy1)

end CFSG.Quasithin.H13

module

public import CFSG.Quasithin.Vol2.Ch7E61
public import CFSG.Quasithin.Vol2.Ch7Lem755

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Quasithin.E3 CFSG.Quasithin.H
open scoped IsMulCommutative

section Module

variable {W : Type*} [CommGroup W] [Finite W]

theorem not_isFOneModule_of_alphaH (hW : ∀ w : W, w ^ 2 = 1) {M : Subgroup (MulAut W)}
    (hα : alphaH M = 1) (hFF : ¬ IsFFModule M) : ¬ IsFOneModule M := by
  rintro ⟨A, ⟨hAM, hA1, hA2⟩, hr⟩
  have : Finite (MulAut W) := MulEquiv.finite_left
  have hAU : A ≤ M ⊓ centSub (fixV A) := fun a ha => ⟨hAM ha, fun u hu => hu a ha⟩
  have hrkA : rk ↥A ≤ CFSG.Open.pRank 2 (M ⊓ centSub (fixV A)) := rk_le_pRank hAU hA2
  by_cases hk : 2 ≤ rkIdx (fixV A)
  · have hmem : rkIdx (fixV A) ∈ alphaSet M := by
      refine ⟨hk, fixV A, fun htop => ?_, rfl, by omega⟩
      rw [htop] at hk
      simp [rkIdx] at hk
    have hne : (alphaSet M).Nonempty := ⟨_, hmem⟩
    unfold alphaH at hα
    rw [if_pos hne] at hα
    have := (Nat.sInf_mem hne).1
    omega
  · apply hFF
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

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G}

theorem twoResidual_autI_ne_bot (hyp : Hyp7_0_2 G T L I)
    (hTL : T ≤ Subgroup.normalizer (L : Set G)) (hV : IsElemAbelian 2 (fsuV T I))
    (hN : fsuL0 T L ⊔ T ≤ Subgroup.normalizer (fsuV T I : Set G)) :
    twoResidual (autI hV ⊤) ≠ ⊥ := by
  rw [Ne, twoResidual_eq_bot_iff]
  intro hp
  have hLN : L ≤ Subgroup.normalizer (fsuV T I : Set G) :=
    (le_fsuL0 T L).trans (le_sup_left.trans hN)
  have hLC : L ≤ Subgroup.centralizer (fsuV T I : Set G) := by
    have hnorm : ((L ⊓ Subgroup.centralizer (fsuV T I : Set G)).subgroupOf L).Normal := by
      rw [← ker_convHom hV L hLN]
      exact MonoidHom.normal_ker _
    have heq := hyp.fsu.faithful.2.1 (L ⊓ Subgroup.centralizer (fsuV T I : Set G))
      inf_le_left hnorm fun x hx => by
        have hxM : convI hV ⟨x, hLN hx⟩ ∈ autI hV ⊤ :=
          convI_mem_autI hV (Subgroup.mem_top x) (hLN hx)
        obtain ⟨k, hk⟩ := hp ⟨_, hxM⟩
        refine ⟨k, L.pow_mem hx _, ?_⟩
        have h1 : convI hV (⟨x, hLN hx⟩ ^ 2 ^ k) = 1 := by
          rw [map_pow]
          simpa using congrArg Subtype.val hk
        simpa using (convI_eq_one_iff hV _).mp h1
    rw [← heq]
    exact inf_le_right
  apply hyp.fsu.irrPlus.2.1
  rw [← hyp.fsu.irrPlus.2.2.2.1]
  change ⁅I, fsuL0 T L⁆ = ⊥
  rw [fsuL0_eq_of_le_normalizer hTL, Subgroup.commutator_eq_bot_iff_le_centralizer]
  intro i hi
  rw [Subgroup.mem_centralizer_iff]
  intro l hl
  exact (Subgroup.mem_centralizer_iff.mp (hLC hl) i (le_fsuV I T hi)).symm

theorem betaH_le_rParam_of_alpha (hin : Input8_1_2) (h325 : Stmt3_2_5)
    (hyp : Hyp7_0_2 G T L I) (h731 : Hyp7_3_1 T L I)
    (hTL : T ≤ Subgroup.normalizer (L : Set G)) (hV : IsElemAbelian 2 (fsuV T I))
    (hN : fsuL0 T L ⊔ T ≤ Subgroup.normalizer (fsuV T I : Set G))
    (hNM : Subgroup.normalizer (fsuV T I : Set G) ≤ fsuM T L)
    (hα : alphaH (autI hV ⊤) = 1) : betaH (autI hV ⊤) ≤ rParam (fsuV T I) := by
  have : Finite (MulAut (IntMod (fsuV T I) hV)) := MulEquiv.finite_left
  have hLM := fsuM_le_normalizer_of_le_normalizer hTL
  have hTI := isTISetUnder_of_le_normalizer h325 hyp.fsu hTL
  have hF1 := not_isFOneModule_of_alphaH (fun v => IntMod.sq_eq_one v) hα
    (not_isFFModule_of_hyp702 hyp hV hNM)
  unfold rParam
  refine le_iInf₂ fun U hU => ?_
  obtain ⟨hUV, hC⟩ := hU
  rw [mQuot_eq_rkIdx_comap hV hUV]
  by_cases hU1 : U = ⊥
  ·
    subst hU1
    have hbot : (⊥ : Subgroup G).comap (E3.valHom hV) = ⊥ :=
      (MonoidHom.comap_bot _).trans ((MonoidHom.ker_eq_bot_iff _).mpr (E3.valHom_injective hV))
    rw [hbot]
    have hne : (⊥ : Subgroup (IntMod (fsuV T I) hV)) ≠ ⊤ := by
      intro h
      have h1 := congrArg (fun H : Subgroup (IntMod (fsuV T I) hV) => Nat.card H) h
      simp only [Subgroup.card_bot, Subgroup.card_top] at h1
      have h2 : Nat.card (IntMod (fsuV T I) hV) = Nat.card (fsuV T I) := rfl
      have h3 : (fsuV T I) ≠ ⊥ := fsuV_ne_bot hyp.fsu
      rw [h2, eq_comm, Subgroup.card_eq_one] at h1
      exact h3 h1
    have hres : twoResidual (autI hV ⊤ ⊓ centSub ⊥) ≠ ⊥ := by
      have hcent : centSub (⊥ : Subgroup (IntMod (fsuV T I) hV)) = ⊤ := by
        rw [eq_top_iff]
        intro g _ u hu
        rw [Subgroup.mem_bot] at hu
        rw [hu, map_one]
      rw [hcent, inf_top_eq]
      exact twoResidual_autI_ne_bot hyp hTL hV hN
    unfold betaH
    exact iInf_le_of_le ⊥ (iInf_le_of_le hne (iInf_le _ hres))
  · have hCM : ¬ Subgroup.centralizer (U : Set G) ≤ fsuM T L := fun h =>
      hC fun g hg => mem_normalizer_of_ti hTI hUV hU1 (h hg) hg
    rcases hin G T L I hyp h731 hLM hV U hUV hU1 hCM with ⟨A, hA, -⟩ | ⟨y, hy, hy1, hyo, hfix⟩
    · exact absurd ⟨A, hA⟩ hF1
    · have hfix' := (leFixI_iff hV).1 hfix
      have hyU : y ∈ autI hV ⊤ ⊓ centSub (U.comap (E3.valHom hV)) :=
        ⟨hy, fun u hu => hfix' hu y (Subgroup.mem_zpowers y)⟩
      have hU'top : U.comap (E3.valHom hV) ≠ ⊤ := by
        intro htop
        apply hy1
        refine MulEquiv.ext fun u => ?_
        rw [MulAut.one_apply]
        exact hfix' (htop ▸ Subgroup.mem_top u) y (Subgroup.mem_zpowers y)
      have hres : twoResidual (autI hV ⊤ ⊓ centSub (U.comap (E3.valHom hV))) ≠ ⊥ := by
        rw [Ne, twoResidual_eq_bot_iff]
        intro hp
        obtain ⟨k, hk⟩ := hp ⟨y, hyU⟩
        have hk' : y ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
        have hdvd := orderOf_dvd_of_pow_eq_one hk'
        obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
        rcases Nat.eq_zero_or_pos j with h0 | hpos
        · rw [h0, pow_zero, orderOf_eq_one_iff] at hj
          exact hy1 hj
        · rw [hj] at hyo
          exact (Nat.not_even_iff_odd.mpr hyo) ((Nat.even_pow' hpos.ne').mpr even_two)
      unfold betaH
      exact iInf_le_of_le _ (iInf_le_of_le hU'top (iInf_le _ hres))

theorem betaH_le_of_fwci' (h734 : Stmt7_3_4) (hin : Input8_1_2) (h325 : Stmt3_2_5)
    (hyp : Hyp7_0_2 G T L I) (h731 : Hyp7_3_1 T L I) (hV : IsElemAbelian 2 (fsuV T I))
    (hN : fsuL0 T L ⊔ T ≤ Subgroup.normalizer (fsuV T I : Set G))
    (hNM : Subgroup.normalizer (fsuV T I : Set G) ≤ fsuM T L)
    (hTL : T ≤ Subgroup.normalizer (L : Set G)) (hα : alphaH (autI hV ⊤) = 1)
    {B c : ℕ} (hB : (B : ℕ∞) ≤ c * betaH (autI hV ⊤)) :
    B ≤ c * (CFSG.Open.pRank 2 (autI hV ⊤) + nPrime (autI hV ⊤)) := by
  have hfw := lemma_7_5_1 hyp hV hN hNM
  obtain ⟨-, hwn, -, -⟩ := h734 G T L I hyp h731 hV
  have hr := betaH_le_rParam_of_alpha hin h325 hyp h731 hTL hV hN hNM hα
  exact le_of_fwci hfw hwn hr hB

theorem stmt7_5_2_of_input812
    (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h39 : A39ForSQTK) (hmod : StmtFSUModule)
    (h711 : Stmt7_1_1_normal) (h325 : Stmt3_2_5) (h734 : Stmt7_3_4) (hin : Input8_1_2)
    (hM22 : Stmt7_2_1_M22Hat) : Stmt7_5_2 := by
  intro G _ _ T L I hyp h731 hc
  obtain ⟨hV, hN⟩ := hmod G T L I hyp.fsu
  have hNM := normalizer_fsuV_le_fsuM h37 h38 h39 hyp.fsu hV hN
  obtain ⟨-, -, -, hn'⟩ := h734 G T L I hyp h731 hV
  obtain ⟨hkSU3, hkSz, -, hkM, hkSL3, -, -, -, -⟩ := hn' hc
  have key := betaH_le_of_fwci' h734 hin h325 hyp h731 hV hN hNM
  refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
  · rintro ⟨n, hn2, hrow⟩
    obtain ⟨-, -, hm2, hβ, hα⟩ := stmt7_2_1_SU3 G T L I hyp hV hNM hc n hn2 hrow
    have h1 := key (h711 G T L I hyp hc (Or.inl ⟨n, hn2, hrow⟩)) hα (B := 4 * n) (c := 1)
      (by rw [Nat.cast_one, one_mul]; exact hβ)
    rw [hkSU3 n hn2 hrow] at h1
    omega
  · rintro ⟨n, hrow⟩
    obtain ⟨hm2, hβ, hα⟩ := stmt7_2_1_Sz G T L I hyp hV hNM hc n hrow
    have h1 := key (h711 G T L I hyp hc (Or.inr (Or.inl ⟨n, hrow⟩))) hα (B := 8 * n) (c := 3)
      (by exact_mod_cast hβ)
    rw [hkSz n hrow] at h1
    obtain ⟨a, ha, rfl, -⟩ := hrow
    omega
  · intro hrow
    obtain ⟨hm2, hβ, hα⟩ := hM22 G T L I hyp hV hNM hc hrow
    have h1 := key (h711 G T L I hyp hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hrow))))))
      hα (B := 8) (c := 1) (by rw [Nat.cast_one, one_mul]; exact_mod_cast hβ)
    rw [hkM (Or.inr (Or.inl hrow))] at h1
    omega
  · intro n hrow
    have hn0 : n ≠ 0 := by
      rintro rfl
      obtain ⟨-, K, _, _, hK, -⟩ := hrow
      have : (1 : ℕ) < Nat.card K := Finite.one_lt_card
      rw [hK, pow_zero] at this
      exact lt_irrefl 1 this
    by_contra hn1
    have hn2 : 2 ≤ n := by omega
    obtain ⟨hm2, hβ, hα⟩ := stmt7_2_1_SL3Pair G T L I hyp hV hN hNM hc n hn2 hrow
    have hrow' : ∃ n : ℕ, Row711SL3Pair T L I n := ⟨n, hrow⟩
    have h1 := key (h711 G T L I hyp hc
      (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inl hrow'))))))))))))) hα (B := 4 * n) (c := 1)
      (by rw [Nat.cast_one, one_mul]; exact hβ)
    rw [hkSL3 n hrow] at h1
    omega

end CFSG.Quasithin.H13

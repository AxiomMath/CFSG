module

public import CFSG.Quasithin.Vol2.Ch8Sec2L825M

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Quasithin.E3 CFSG.Quasithin.H CFSG.Quasithin.ASInputs
open scoped IsMulCommutative

section L825N

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G}

theorem code_values_82 (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h39 : A39ForSQTK)
    (hmod : StmtFSUModule) (hyp : Hyp7_0_2 G T L I) {H : Subgroup G} {h : G}
    (hC : Concl822 T L I H h 1) (hV : IsElemAbelian 2 (fsuV T I))
    (hw : wParam T (fsuV T I) = 1) (hWO : IsWOffender T (fsuV T I) (ch82A (fsuV T I) h))
    {p : ℕ} (hp : 5 ≤ p) (hm2 : CFSG.Open.pRank 2 (autI hV ⊤) ≤ p)
    (hr : ((p + 1 : ℕ) : ℕ∞) ≤ rParam (fsuV T I)) (hrkV : rk ↥(fsuV T I) = p + 5) :
    rParam (fsuV T I) = ((p + 1 : ℕ) : ℕ∞) ∧ rk ↥(autI hV (ch82A (fsuV T I) h)) = p ∧
      rkIdx (fixV (autI hV (ch82A (fsuV T I) h))) = p + 1 ∧
      ch82ZI (fsuV T I) h = ch82U (fsuV T I) h ∧ rk ↥(ch82U (fsuV T I) h) = 4 := by
  obtain ⟨-, hN⟩ := hmod G T L I hyp.fsu
  have hNM := normalizer_fsuV_le_fsuM h37 h38 h39 hyp.fsu hV hN
  obtain ⟨-, hhI, hIC, -, -, hSyl, hMIeq, -, -, -, -, -, hA7, hAC, -, -, hm, -, h28, -, -⟩ :=
    hC
  obtain ⟨hAel, hAN⟩ := ch82A_facts_82 hV hA7
  have hAel2 := isElemAbelian2_autI hV hAel hAN
  have hVp : IsPGroup 2 ↥(fsuV T I) := B2F.isPGroup_of_isElemAbelian hV
  have hA : ch82A (fsuV T I) h = conjSubgroup (fsuV T I) h⁻¹ ⊓
      Subgroup.normalizer (fsuV T I : Set G) := by rw [hA7, conjSub_eq_conjSubgroup_82]
  have hrkA2 : rk ↥(autI hV (ch82A (fsuV T I) h)) ≤ CFSG.Open.pRank 2 (autI hV ⊤) := by
    rw [hA]
    exact rk_autI_le_pRank hV
  have hrkAm := rk_autI_eq_mQuot hV hAN
  rw [hAC] at hm hrkAm
  have hrA := rParam_sub_wParam_le_82 hyp hV hN hNM hWO
  have hfw := lemma_7_5_1 hyp hV hN hNM
  rw [hw] at hrA hfw
  have hne : rParam (fsuV T I) ≠ ⊤ := fun htop => by
    rw [htop] at hfw
    exact absurd hfw (by simp)
  obtain ⟨r, hr'⟩ := ENat.ne_top_iff_exists.mp hne
  rw [← hr'] at hfw hrA hr
  have hfw' : r ≤ CFSG.Open.pRank 2 (autI hV ⊤) + 1 := by exact_mod_cast hfw
  have hr1 : p + 1 ≤ r := by exact_mod_cast hr
  have hrA' : r - 1 ≤ rk ↥(autI hV (ch82A (fsuV T I) h)) := by
    have h1 : ((r - 1 : ℕ) : ℕ∞) = (r : ℕ∞) - 1 := by
      rw [ENat.natCast_sub r 1, Nat.cast_one]
    have h2 : ((r - 1 : ℕ) : ℕ∞) ≤ ((rk ↥(autI hV (ch82A (fsuV T I) h)) : ℕ) : ℕ∞) :=
      h1 ▸ hrA
    exact_mod_cast h2
  have hrp : r = p + 1 := by omega
  have hrkA : rk ↥(autI hV (ch82A (fsuV T I) h)) = p := by omega
  have hA1 : autI hV (ch82A (fsuV T I) h) ≠ ⊥ := by
    intro hb
    rw [hb] at hrkA
    have : rk ↥(⊥ : Subgroup (MulAut (IntMod (fsuV T I) hV))) = 0 := by
      unfold rk
      rw [Subgroup.card_bot]
      exact padicValNat_one_right 2
    omega
  have hlt := card_lt_of_not_ff_82 hyp hV hNM (autI_mono hV le_top) hA1 hAel2
  rw [card_eq_two_pow_rk hAel2, card_eq_two_pow_of_isPGroup (isPGroup_intMod_82 hV _),
    card_intMod_eq hV, ← pow_add] at hlt
  have hlt' := (Nat.pow_lt_pow_iff_right (by norm_num)).mp hlt
  have hadd := rk_add_rkIdx hV (fixV (autI hV (ch82A (fsuV T I) h)))
  have hVV : rk (IntMod (fsuV T I) hV) = p + 5 := hrkV
  have hfixU : fixV (autI hV (ch82A (fsuV T I) h)) =
      (ch82U (fsuV T I) h).comap (E3.valHom hV) := fixV_autI_eq_comap hV hAN
  have hUq : rkIdx (fixV (autI hV (ch82A (fsuV T I) h))) =
      mQuot (fsuV T I) (ch82U (fsuV T I) h) := by
    rw [hfixU, mQuot_eq_rkIdx_comap hV (U := ch82U (fsuV T I) h) inf_le_left]
  have hcl := hIC.2.2.2.1
  rw [inf_inf_eq_82 (M := fsuM T L) hIC.1] at hcl
  have hP := pair_82 hV h28.le_T h28.normal_T hSyl hMIeq hhI hcl
  have hZU := ch82ZI_le_ch82U_82 hP
  have hUZ := E3.mQuot_mono (V := fsuV T I) hZU
  have hmU : mQuot (fsuV T I) (ch82U (fsuV T I) h) = p + 1 := by omega
  have hZeq : ch82ZI (fsuV T I) h = ch82U (fsuV T I) h :=
    eq_of_le_of_mQuot_le_82 hVp hZU inf_le_left (by omega)
  have hrkU : rk ↥(ch82U (fsuV T I) h) = 4 := by
    have := mQuot_add_rk (A := fsuV T I) (B := ch82U (fsuV T I) h) inf_le_left
    omega
  refine ⟨?_, hrkA, by omega, hZeq, hrkU⟩
  rw [← hr', hrp]

theorem cocode_values_82 (h813 : Stmt8_1_3) (hyp : Hyp7_0_2 G T L I)
    (h731 : Hyp7_3_1 T L I) [hc : IsMulCommutative ↥(fsuV T I)] (hrow : Row711M24Cocode T L I)
    {H : Subgroup G} {h : G} {k : ℕ} (hC : Concl822 T L I H h k)
    (hV : IsElemAbelian 2 (fsuV T I)) (hWO : IsWOffender T (fsuV T I) (ch82A (fsuV T I) h)) :
    rParam (fsuV T I) = 8 ∧ rk ↥(autI hV (ch82A (fsuV T I) h)) = 6 ∧
      rk ↥(fixV (autI hV (ch82A (fsuV T I) h))) = 3 ∧
      ch82ZI (fsuV T I) h = ch82U (fsuV T I) h ∧ rk ↥(ch82U (fsuV T I) h) = 3 := by
  obtain ⟨-, r8, -, -, hA⟩ := h813 G T L I hyp h731 hc (Or.inr (Or.inr hrow))
  obtain ⟨hZ3, hA6, hU3⟩ := hA hV _ hWO
  obtain ⟨-, hhI, hIC, -, -, hSyl, hMIeq, -, -, -, -, -, hA7, hAC, -, -, -, -, h28, -, -⟩ :=
    hC
  obtain ⟨-, hAN⟩ := ch82A_facts_82 hV hA7
  have hfixU : fixV (autI hV (ch82A (fsuV T I) h)) =
      (ch82U (fsuV T I) h).comap (E3.valHom hV) := fixV_autI_eq_comap hV hAN
  have hrkU : rk ↥(ch82U (fsuV T I) h) = 3 := by
    rw [← rk_comap_valHom_82 hV (U := ch82U (fsuV T I) h) inf_le_left, ← hfixU]
    exact hU3
  have hcl := hIC.2.2.2.1
  rw [inf_inf_eq_82 (M := fsuM T L) hIC.1] at hcl
  have hP := pair_82 hV h28.le_T h28.normal_T hSyl hMIeq hhI hcl
  have hZU := ch82ZI_le_ch82U_82 hP
  have hVp : IsPGroup 2 ↥(fsuV T I) := B2F.isPGroup_of_isElemAbelian hV
  have hUp : IsPGroup 2 ↥(ch82U (fsuV T I) h) := hVp.to_le inf_le_left
  have hZp : IsPGroup 2 ↥(ch82ZI (fsuV T I) h) := hVp.to_le inf_le_left
  have hZ3' : rk ↥(ch82ZI (fsuV T I) h) = 3 := by rw [← hAC]; exact hZ3
  have hZeq : ch82ZI (fsuV T I) h = ch82U (fsuV T I) h := by
    refine Subgroup.eq_of_le_of_card_ge hZU ?_
    rw [card_eq_two_pow_of_isPGroup hUp, card_eq_two_pow_of_isPGroup hZp, hrkU, hZ3']
  exact ⟨r8, hA6, hU3, hZeq, hrkU⟩

end L825N

end CFSG.Quasithin.H13

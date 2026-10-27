module

public import CFSG.Quasithin.Vol2.Ch8Sec1
public import CFSG.Quasithin.Background.HMathieuFacts23

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Quasithin.E3 CFSG.Quasithin.H
open scoped IsMulCommutative

theorem stmt8_1_2_M22M23_of
    (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h39 : A39ForSQTK)
    (hmod : StmtFSUModule) (h711 : Stmt7_1_1_normal) (h325 : Stmt3_2_5) (h811 : Stmt8_1_1)
    (hin : Input8_1_2) :
    ∀ (G : Type) [Group G] [Finite G] (T L I : Subgroup G), Hyp7_0_2 G T L I →
      Hyp7_3_1 T L I → ∀ _ : IsMulCommutative ↥(fsuV T I),
        (Row711M22Cocode T L I → (6 : ℕ∞) ≤ rParam (fsuV T I)) ∧
        (Row711M23Cocode T L I → (7 : ℕ∞) ≤ rParam (fsuV T I)) := by
  intro G _ _ T L I hyp h731 hc
  obtain ⟨hV, hN⟩ := hmod G T L I hyp.fsu
  have hNM := normalizer_fsuV_le_fsuM h37 h38 h39 hyp.fsu hV hN
  have hover := isOver_autI (T := T) (L := L) (I := I) hV hNM
  refine ⟨fun hrow => ?_, fun hrow => ?_⟩
  · have hn := Mathieu.cocode22_card (V := IntMod (fsuV T I) hV) hrow
    exact le_rParam_of_bound h711 h325 h811 hin hyp h731 (Or.inl hrow) hV hn (j := 4)
      fun U hU hd => Mathieu.cocode22_rk_le_four hover hrow U hU hd
  · have hn := Mathieu.cocode23_card (V := IntMod (fsuV T I) hV) hrow
    exact le_rParam_of_bound h711 h325 h811 hin hyp h731 (Or.inr (Or.inl hrow)) hV hn (j := 4)
      fun U hU hd => Mathieu.cocode23_rk_le_four hover hrow U hU hd

theorem stmt8_1_3_M24_of'
    (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h39 : A39ForSQTK)
    (hmod : StmtFSUModule) (h711 : Stmt7_1_1_normal) (h325 : Stmt3_2_5) (h811 : Stmt8_1_1)
    (hin : Input8_1_2) (h734 : Stmt7_3_4) : Stmt8_1_3_M24 := by
  intro G _ _ T L I hyp h731 hc hrow
  obtain ⟨hV, hN⟩ := hmod G T L I hyp.fsu
  have hNM := normalizer_fsuV_le_fsuM h37 h38 h39 hyp.fsu hV hN
  have hT := hypE322_of_fsu hyp.fsu hV hN
  have h24 := hypE324_of_hyp702 hyp hV hNM
  have hover := isOver_autI (T := T) (L := L) (I := I) hV hNM
  have : Finite (MulAut (IntMod (fsuV T I) hV)) := MulEquiv.finite_left
  obtain ⟨-, hwn, -, hn'⟩ := h734 G T L I hyp h731 hV
  have hn2 := nPrime_eq_two_of_cocodeRow hrow hn'
  rw [hn2] at hwn
  have hw2 : wParam T (fsuV T I) ≤ 2 := by exact_mod_cast hwn
  have hwtop : wParam T (fsuV T I) ≠ ⊤ := ne_top_of_le_ne_top (by simp) hw2
  obtain ⟨g, hg⟩ := exists_isWOffenderAt hV hT hwtop
  have hrA := e3_28_two_left hV hT h24 hg
  have hAm := rk_autI_le_pRank hV (g := g)
  have hAel := isElemAbelian2_autI hV (B2F.isElemAbelian_mono inf_le_left
    (isElemAbelian_conjSubgroup hV g)) inf_le_right
  set Ab := autI hV (conjSubgroup (fsuV T I) g ⊓ Subgroup.normalizer (fsuV T I : Set G))
    with hAb
  have hAle : Ab ≤ autI hV ⊤ := autI_mono hV le_top
  obtain ⟨w', hw'⟩ := ENat.ne_top_iff_exists.1 hwtop
  have hw'2 : w' ≤ 2 := by rw [← hw'] at hw2; exact_mod_cast hw2
  have hrtop : rParam (fsuV T I) ≠ ⊤ := ne_top_of_le_ne_top (by rw [← hw']; simp) hrA
  obtain ⟨r', hr'⟩ := ENat.ne_top_iff_exists.1 hrtop
  have hrA' : r' ≤ w' + rk ↥Ab := by
    rw [← hw', ← hr'] at hrA
    exact_mod_cast hrA
  have hcardAb := card_eq_two_pow_rk hAel
  have hmin : w' ≤ r' → min (wParam T (fsuV T I)) (rParam (fsuV T I)) = (w' : ℕ∞) := by
    intro h
    rw [← hw', ← hr']
    exact min_eq_left (Nat.cast_le.2 h)
  obtain ⟨h22, h23⟩ := stmt8_1_2_M22M23_of h37 h38 h39 hmod h711 h325 h811 hin G T L I hyp h731 hc
  rcases hrow with hr | hr | hr
  ·
    exfalso
    have hm2 := Mathieu.cocode22_pRank hover hr
    have h6 := h22 hr
    rw [← hr'] at h6
    have h6' : 6 ≤ r' := by exact_mod_cast h6
    have hfacts := Mathieu.stmtH15M22 _ _ _ hover hr
    have hAm' := hAm.trans hm2
    by_cases h5 : rk ↥Ab = 5
    · rw [h5] at hcardAb
      obtain ⟨hxi, hfour⟩ := hfacts.1 Ab hAle hAel hcardAb
      by_cases hw1 : w' = 1
      · have hk : ((4 : ℕ) : ℕ∞) + wParam T (fsuV T I) + 1 ≤ rParam (fsuV T I) := by
          rw [← hw', ← hr', hw1]
          exact_mod_cast (show 4 + 1 + 1 ≤ r' by omega)
        have h := min_le_rkIdx_of_le_gammaCheck hV hT hg hk (X := Mathieu.xiV Ab)
          (xiV_le_gammaCheck hAel (by omega))
        rw [hxi, rkIdx_top_eq, hmin (by omega)] at h
        have : w' ≤ 0 := by exact_mod_cast h
        omega
      · have hw2' : w' = 2 := by omega
        have hk : ((3 : ℕ) : ℕ∞) + wParam T (fsuV T I) + 1 ≤ rParam (fsuV T I) := by
          rw [← hw', ← hr', hw2']
          exact_mod_cast (show 3 + 2 + 1 ≤ r' by omega)
        have h := min_le_rkIdx_of_le_gammaCheck hV hT hg hk
          (iSup_fixV_four_le_gammaCheck (by omega))
        rw [hfour, rkIdx_top_eq, hmin (by omega)] at h
        have : w' ≤ 0 := by exact_mod_cast h
        omega
    · have h4 : rk ↥Ab = 4 := by omega
      have hw2' : w' = 2 := by omega
      rw [h4] at hcardAb
      have hxi := hfacts.2 Ab hAle hAel hcardAb
      have hk : ((3 : ℕ) : ℕ∞) + wParam T (fsuV T I) + 1 ≤ rParam (fsuV T I) := by
        rw [← hw', ← hr', hw2']
        exact_mod_cast (show 3 + 2 + 1 ≤ r' by omega)
      have h := min_le_rkIdx_of_le_gammaCheck hV hT hg hk (X := Mathieu.xiV Ab)
        (xiV_le_gammaCheck hAel (by omega))
      rw [hmin (by omega)] at h
      have h' : w' ≤ rkIdx (Mathieu.xiV Ab) := by exact_mod_cast h
      omega
  ·
    exfalso
    have hm2 := Mathieu.cocode23_pRank hover hr
    have h7 := h23 hr
    rw [← hr'] at h7
    have h7' : 7 ≤ r' := by exact_mod_cast h7
    have := hAm.trans hm2
    omega
  · exact hr

end CFSG.Quasithin.H13

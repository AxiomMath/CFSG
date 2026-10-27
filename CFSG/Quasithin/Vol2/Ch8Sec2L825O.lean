module

public import CFSG.Quasithin.Vol2.Ch8Sec2L825N
public import CFSG.Quasithin.Vol2.Ch8Sec2L823Res
public import CFSG.Quasithin.Vol2.Ch8Sec2L824Res

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Quasithin.E3 CFSG.Quasithin.H CFSG.Quasithin.ASInputs
open scoped IsMulCommutative

theorem stmt8_2_5_of
    (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h39 : A39ForSQTK)
    (hmod : StmtFSUModule) (h325 : Stmt3_2_5) (hin : Input8_1_2) (h711n : Stmt7_1_1_normal)
    (h734 : Stmt7_3_4) (h756 : Stmt7_5_6_two) (h813 : Stmt8_1_3) (h755 : Input7_5_5)
    (hE214 : AS_E_2_14) (hcard : Mathieu.StmtH13Card) : Stmt8_2_5 := by
  have htab : HTab82 := hTab82_holds
  have hL9 : HL3Nine82 := hL3Nine82_holds
  have hcode : HCode82 := hCode82_holds
  have hnorm : HOffNormal82 := hOffNormal82_holds
  have hdiv : Step823L3Div := step823L3Div_holds h37 h38 h39 hmod hE214
  have hres : Res823L3 := res823L3_holds h37 h38 h39 hmod hE214
  have hres4 : Res824L3 := res824L3_holds h37 h38 h39 hmod h325 hin h711n h734 h756 hE214 htab
    hL9 hdiv hres
  intro G _ _ T L I hyp h731 h821 hc hrow H h k hH hhH hC
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hV, hN⟩ := hmod G T L I hyp.fsu
  have hNM := normalizer_fsuV_le_fsuM h37 h38 h39 hyp.fsu hV hN
  have hTL : T ≤ Subgroup.normalizer (L : Set G) := le_normalizer_of_case82 h711n hyp hrow
  have hTV : T ≤ Subgroup.normalizer (fsuV T I : Set G) := le_sup_right.trans hN
  obtain ⟨hw, hWO⟩ := stmt8_2_3_82 h37 h38 h39 hmod h325 hin h711n h734 h756 h813 h755 hE214
    htab hL9 hcode hcard hdiv hres hyp h731 h821 hrow hH hhH hC
  have hC' := hC
  obtain ⟨-, -, -, -, hZC, hSyl, -, -, -, -, -, -, hA7, hAC, -, -, -, -, -, -, -⟩ := hC'
  obtain ⟨hAel, hAN⟩ := ch82A_facts_82 hV hA7
  have hAel2 := isElemAbelian2_autI hV hAel hAN
  have hrkAm := rk_autI_eq_mQuot hV hAN
  have hfixU : fixV (autI hV (ch82A (fsuV T I) h)) =
      (ch82U (fsuV T I) h).comap (E3.valHom hV) := fixV_autI_eq_comap hV hAN
  have hrkfix : rk ↥(fixV (autI hV (ch82A (fsuV T I) h))) = rk ↥(ch82U (fsuV T I) h) := by
    rw [hfixU, rk_comap_valHom_82 hV (U := ch82U (fsuV T I) h) inf_le_left]
  have hUq : rkIdx (fixV (autI hV (ch82A (fsuV T I) h))) =
      mQuot (fsuV T I) (ch82U (fsuV T I) h) := by
    rw [hfixU, mQuot_eq_rkIdx_comap hV (U := ch82U (fsuV T I) h) inf_le_left]
  obtain ⟨-, hT22, hT24⟩ := tab_82 (stmt7_4_1_of h37 h38 h39 hmod h325 hin) htab hyp h731 hTL
    hV hNM
  have hM22 : Row711M22Code T L I → wParam T (fsuV T I) = 1 ∧ rParam (fsuV T I) = 6 ∧
      rk ↥(autI hV (ch82A (fsuV T I) h)) = 5 ∧ rkIdx (fixV (autI hV (ch82A (fsuV T I) h))) = 6 ∧
      ch82ZI (fsuV T I) h = ch82U (fsuV T I) h ∧ rk ↥(ch82U (fsuV T I) h) = 4 := by
    intro hr
    obtain ⟨hwk, hk1⟩ := code_k_eq_82 h37 h38 h39 hmod h325 hin h711n h734 h755 hE214 htab hcode
      hcard hyp h731 (Or.inl hr) hH hC
    subst hk1
    have hV10 : rk ↥(fsuV T I) = 10 :=
      rk_eq_of_card_82 ((hcard ↥(fsuV T I) (autOn (fsuL0 T L) (fsuV T I))).2.2 (Or.inr hr))
    obtain ⟨hm2, hr6⟩ := hT22 hr
    obtain ⟨hr', hA', hI', hZ', hU'⟩ := code_values_82 (p := 5) h37 h38 h39 hmod hyp hC hV
      (by exact_mod_cast hwk) hWO le_rfl hm2 (by exact_mod_cast hr6) (by omega)
    exact ⟨by exact_mod_cast hwk, by exact_mod_cast hr', hA', hI', hZ', hU'⟩
  have hM24 : Row711M24Code T L I → wParam T (fsuV T I) = 1 ∧ rParam (fsuV T I) = 7 ∧
      rk ↥(autI hV (ch82A (fsuV T I) h)) = 6 ∧ rkIdx (fixV (autI hV (ch82A (fsuV T I) h))) = 7 ∧
      ch82ZI (fsuV T I) h = ch82U (fsuV T I) h ∧ rk ↥(ch82U (fsuV T I) h) = 4 := by
    intro hr
    obtain ⟨hwk, hk1⟩ := code_k_eq_82 h37 h38 h39 hmod h325 hin h711n h734 h755 hE214 htab hcode
      hcard hyp h731 (Or.inr hr) hH hC
    subst hk1
    have hV11 : rk ↥(fsuV T I) = 11 :=
      rk_eq_of_card_82 ((hcard ↥(fsuV T I) (autOn (fsuL0 T L) (fsuV T I))).1 (Or.inr hr))
    obtain ⟨hm2, -, -, -⟩ := hT24 hr
    have hr7 := seven_le_rParam_82 h37 h38 h39 hmod h325 hin h755 htab hcode hcard hyp h731 hTL
      hV hr
    obtain ⟨hr', hA', hI', hZ', hU'⟩ := code_values_82 (p := 6) h37 h38 h39 hmod hyp hC hV
      (by exact_mod_cast hwk) hWO (by norm_num) hm2 (by exact_mod_cast hr7) (by omega)
    exact ⟨by exact_mod_cast hwk, by exact_mod_cast hr', hA', hI', hZ', hU'⟩
  have hCoc : Row711M24Cocode T L I → wParam T (fsuV T I) = 2 ∧ rParam (fsuV T I) = 8 ∧
      rk ↥(autI hV (ch82A (fsuV T I) h)) = 6 ∧ rk ↥(fixV (autI hV (ch82A (fsuV T I) h))) = 3 ∧
      ch82ZI (fsuV T I) h = ch82U (fsuV T I) h ∧ rk ↥(ch82U (fsuV T I) h) = 3 := by
    intro hr
    obtain ⟨-, -, hw2, -, -⟩ := h813 G T L I hyp h731 hc (Or.inr (Or.inr hr))
    obtain ⟨hr8, hA6, hU3, hZ', hU'⟩ := cocode_values_82 h813 hyp h731 hr hC hV hWO
    exact ⟨hw2, hr8, hA6, hU3, hZ', hU'⟩
  have hL3 := fun n (hr : Row711L3Nine T L I n) => l3_table_82 h37 h38 h39 hmod h325 hin h711n
    h734 h756 h755 hE214 htab hL9 hdiv hres hres4 hyp h731 h821 hr hH hhH hC hV
  have hdata : ch82ZI (fsuV T I) h = ch82U (fsuV T I) h ∧
      ((BinaryNineTensor (autI hV (fsuL0 T L)) ⊤ ⊥ 1 ∧ rk ↥(autI hV (ch82A (fsuV T I) h)) = 4 ∧
          rk ↥(fixV (autI hV (ch82A (fsuV T I) h))) = 4) ∨
        (MathieuCode22 (autI hV (fsuL0 T L)) ⊤ ⊥ ∧ rk ↥(autI hV (ch82A (fsuV T I) h)) = 5 ∧
          rkIdx (fixV (autI hV (ch82A (fsuV T I) h))) = 6) ∨
        (MathieuCode24 (autI hV (fsuL0 T L)) ⊤ ⊥ ∧ rk ↥(autI hV (ch82A (fsuV T I) h)) = 6 ∧
          rkIdx (fixV (autI hV (ch82A (fsuV T I) h))) = 7) ∨
        (MathieuCocode24 (autI hV (fsuL0 T L)) ⊤ ⊥ ∧ rk ↥(autI hV (ch82A (fsuV T I) h)) = 6 ∧
          rk ↥(fixV (autI hV (ch82A (fsuV T I) h))) = 3)) ∧
      0 < rk ↥(ch82U (fsuV T I) h) := by
    rcases hrow with ⟨n, hr⟩ | hr | hr | hr
    · obtain ⟨hn1, -, -, hA4, hF4, hZ⟩ := hL3 n hr
      subst hn1
      exact ⟨hZ, Or.inl ⟨hr.2, hA4, hF4⟩, by omega⟩
    · obtain ⟨-, -, hA5, hI6, hZ, hU4⟩ := hM22 hr
      exact ⟨hZ, Or.inr (Or.inl ⟨hr, hA5, hI6⟩), by omega⟩
    · obtain ⟨-, -, hA6, hI7, hZ, hU4⟩ := hM24 hr
      exact ⟨hZ, Or.inr (Or.inr (Or.inl ⟨hr, hA6, hI7⟩)), by omega⟩
    · obtain ⟨-, -, hA6, hF3, hZ, hU3⟩ := hCoc hr
      exact ⟨hZ, Or.inr (Or.inr (Or.inr ⟨hr, hA6, hF3⟩)), by omega⟩
  obtain ⟨hZeq, hrowA, hUpos⟩ := hdata
  have hTsyl : QuasithinUnique.IsSylowTwoOf T (Subgroup.normalizer (fsuV T I : Set G)) :=
    ⟨hTV, hyp.fsu.sylow.1,
      fun h2 => hyp.fsu.sylow.2 (h2.trans (Subgroup.relIndex_dvd_index_of_le hTV))⟩
  have hTsyl' := B2F.isSylowTwoOf_autI hV le_rfl hTsyl
  rw [autI_normalizer_eq_top hV] at hTsyl'
  have hAT : ch82A (fsuV T I) h ≤ T := fun x hx =>
    (CFSG.QuasithinUnique.EscapingLocal.pCoreOf_le_of_isSylowTwoOf hSyl hx.2).1
  have hS := hnorm (IntMod (fsuV T I) hV) (autI hV (fsuL0 T L)) (autI hV ⊤)
    (isOver_autI_82 hV hNM) (autI hV T) (autI hV (ch82A (fsuV T I) h)) hTsyl'.1 hTsyl'.2.1
    hTsyl'.2.2 (autI_mono hV hAT) hAel2 hrowA
  have hTU : T ≤ Subgroup.normalizer (ch82U (fsuV T I) h : Set G) :=
    le_normalizer_ch82U_82 hV hTV hAN hS
  have hVp : IsPGroup 2 ↥(fsuV T I) := B2F.isPGroup_of_isElemAbelian hV
  have hUp : IsPGroup 2 ↥(ch82U (fsuV T I) h) := hVp.to_le inf_le_left
  have hInH : InH T (Subgroup.normalizer (ch82U (fsuV T I) h : Set G)) := by
    refine ⟨hTU, fun hbot => ?_⟩
    have h1 := CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
      (Subgroup.le_normalizer : ch82U (fsuV T I) h ≤ _) le_rfl hUp
    rw [hbot] at h1
    have h2 : ch82U (fsuV T I) h = ⊥ := le_bot_iff.mp h1
    rw [h2] at hUpos
    unfold rk at hUpos
    rw [Subgroup.card_bot, padicValNat_one_right] at hUpos
    exact absurd hUpos (lt_irrefl 0)
  have hUC : ch82U (fsuV T I) h ≤ Subgroup.centralizer (ch82I (fsuV T I) h : Set G) :=
    hZeq ▸ hZC
  refine ⟨hw, hWO, fun n hr => (hL3 n hr).1, ?_, ?_, ?_, ?_, hTU, hInH,
    hZeq.symm.trans hAC.symm, hZeq.symm, hUC, Subgroup.le_centralizer_iff.mp hUC⟩
  · rintro ⟨n, hr⟩
    obtain ⟨hn1, hw1, hr5, hA4, hF4, -⟩ := hL3 n hr
    exact ⟨hw1, hr5, hrkAm ▸ hA4, hrkfix ▸ hF4⟩
  · intro hr
    obtain ⟨hw1, hr6, hA5, -, -, hU4⟩ := hM22 hr
    exact ⟨hw1, hr6, hrkAm ▸ hA5, hU4⟩
  · intro hr
    obtain ⟨hw1, hr7, hA6, -, -, hU4⟩ := hM24 hr
    exact ⟨hw1, hr7, hrkAm ▸ hA6, hU4⟩
  · intro hr
    obtain ⟨hw2, hr8, hA6, -, -, hU3⟩ := hCoc hr
    exact ⟨hw2, hr8, hrkAm ▸ hA6, hU3⟩

end CFSG.Quasithin.H13

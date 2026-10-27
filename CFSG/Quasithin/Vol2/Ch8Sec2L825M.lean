module

public import CFSG.Quasithin.Vol2.Ch8Sec2L825L

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Quasithin.E3 CFSG.Quasithin.H CFSG.Quasithin.ASInputs
open scoped IsMulCommutative

section L825M

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G}

theorem eq_of_le_of_mQuot_le_82 {V U Z : Subgroup G} (hV : IsPGroup 2 ↥V) (hZU : Z ≤ U)
    (hUV : U ≤ V) (h : mQuot V Z ≤ mQuot V U) : Z = U := by
  have h1 := mQuot_add hZU hUV
  have h2 : mQuot U Z = 0 := by omega
  have h3 := relIndex_eq_two_pow (hV.to_le hUV) Z
  rw [h2, pow_zero] at h3
  exact le_antisymm hZU (Subgroup.relIndex_eq_one.mp h3)

omit [Finite G] in
theorem mem_fixV_of_normalizer_82 {W : Type*} [CommGroup W] {A : Subgroup (MulAut W)}
    {x : MulAut W} (hx : x ∈ Subgroup.normalizer (A : Set (MulAut W))) {v : W}
    (hv : v ∈ fixV A) : x v ∈ fixV A :=
  CFSG.Quasithin.fixV_apply_mem_of_mem_normalizer hx hv

omit [Finite G] in
theorem le_normalizer_ch82U_82 {V A : Subgroup G} (hV : IsElemAbelian 2 V)
    (hTV : T ≤ Subgroup.normalizer (V : Set G)) (hAN : A ≤ Subgroup.normalizer (V : Set G))
    (hS : autI hV T ≤ Subgroup.normalizer (autI hV A : Set (MulAut (IntMod V hV)))) :
    T ≤ Subgroup.normalizer ((V ⊓ Subgroup.centralizer (A : Set G) : Subgroup G) : Set G) := by
  have hfix := fixV_autI_eq_comap hV hAN
  have key : ∀ t ∈ T, ∀ u ∈ V ⊓ Subgroup.centralizer (A : Set G),
      t * u * t⁻¹ ∈ V ⊓ Subgroup.centralizer (A : Set G) := by
    intro t ht u hu
    have htN := hTV ht
    have h1 : (IntMod.mk hV ⟨u, hu.1⟩ : IntMod V hV) ∈ fixV (autI hV A) := by
      rw [hfix]
      exact hu
    have h2 := mem_fixV_of_normalizer_82 (hS (convI_mem_autI hV ht htN)) h1
    rw [hfix] at h2
    have h3 : ((convI hV ⟨t, htN⟩ (IntMod.mk hV ⟨u, hu.1⟩) : IntMod V hV).val : G) =
        t * u * t⁻¹ := convI_apply_val hV ⟨t, htN⟩ _
    have h4 : ((convI hV ⟨t, htN⟩ (IntMod.mk hV ⟨u, hu.1⟩) : IntMod V hV).val : G) ∈
        V ⊓ Subgroup.centralizer (A : Set G) := h2
    rwa [h3] at h4
  intro t ht
  refine B6.mem_normalizer_of_forall_mem (fun u hu => key t ht u hu) (fun u hu => ?_)
  have := key t⁻¹ (T.inv_mem ht) u hu
  simpa using this

theorem five_le_rParam_82 (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h39 : A39ForSQTK)
    (hmod : StmtFSUModule) (h325 : Stmt3_2_5) (hin : Input8_1_2) (h755 : Input7_5_5)
    (htab : HTab82) (hL9 : HL3Nine82)
    (hyp : Hyp7_0_2 G T L I) (h731 : Hyp7_3_1 T L I) [IsMulCommutative ↥(fsuV T I)]
    (hTL : T ≤ Subgroup.normalizer (L : Set G)) (hV : IsElemAbelian 2 (fsuV T I))
    (hrow : Row711L3Nine T L I 1) : (5 : ℕ∞) ≤ rParam (fsuV T I) := by
  obtain ⟨-, hN⟩ := hmod G T L I hyp.fsu
  have hNM := normalizer_fsuV_le_fsuM h37 h38 h39 hyp.fsu hV hN
  have hL0 : fsuL0 T L = L := fsuL0_eq_of_le_normalizer hTL
  have hML : fsuM T L ≤ Subgroup.normalizer (L : Set G) := by
    show Subgroup.normalizer (fsuL0 T L : Set G) ≤ _
    rw [hL0]
  have hTI : IsTISetUnder (fsuV T I) (fsuM T L) :=
    isTISetUnder_of_stmt3_2_5_of_le_normalizer h325 hyp.fsu hTL
  obtain ⟨hT9, -, -⟩ := htab (IntMod (fsuV T I) hV) (autI hV (fsuL0 T L)) (autI hV ⊤)
    (isOver_autI_82 hV hNM)
  obtain ⟨-, -, hα, -⟩ := hT9 1 le_rfl hrow.2
  obtain ⟨hβ, -, -, -, h461⟩ := hL9 (IntMod (fsuV T I) hV) (autI hV (fsuL0 T L))
    (autI hV ⊤) (isOver_autI_82 hV hNM) 1 le_rfl hrow.2
  have hV9 : rk ↥(fsuV T I) = 9 := rk_eq_of_card_82 (card_of_binaryNineTensor_82 le_rfl hrow.2)
  have hV9' : rk (IntMod (fsuV T I) hV) = 9 := hV9
  unfold rParam
  refine le_iInf₂ fun U hU => ?_
  obtain ⟨hUV, hC⟩ := hU
  have h4 := lt_mQuot_of_odd_82 h37 h38 h39 hmod h325 hin h755 hyp h731 hML hV hTI (m := 4)
    (by norm_num) (by omega) (lt_of_lt_of_le (by norm_num) (hα rfl)) (fun y hy hy1 hyo hyU => by
      have h5 := hβ y hy hy1 hyo hyU
      have h6 := rk_add_rkIdx hV (fixV (Subgroup.zpowers y))
      obtain ⟨hc, hy3⟩ := h461 rfl y hy hyo h5
      exact ⟨by omega, hy3, hc⟩) hUV hC
  exact_mod_cast h4

theorem l3_rk_82 (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h39 : A39ForSQTK)
    (hmod : StmtFSUModule) (h325 : Stmt3_2_5) (hin : Input8_1_2) (h711n : Stmt7_1_1_normal)
    (h734 : Stmt7_3_4) (h756 : Stmt7_5_6_two) (hE214 : AS_E_2_14)
    (htab : HTab82) (hL9 : HL3Nine82) (hdiv : Step823L3Div) (hres : Res823L3)
    (hyp : Hyp7_0_2 G T L I) (h731 : Hyp7_3_1 T L I) (h821 : Hyp8_2_1 T L I)
    [IsMulCommutative ↥(fsuV T I)] {n : ℕ} (hrow : Row711L3Nine T L I n) {H : Subgroup G}
    {h : G} {k : ℕ} (hH : IsHStar T (fsuM T L) H) (hhH : h ∈ H) (hC : Concl822 T L I H h k)
    (hV : IsElemAbelian 2 (fsuV T I)) :
    k = n ∧ wParam T (fsuV T I) = k ∧ rk ↥(autI hV (ch82A (fsuV T I) h)) = 4 * k ∧
      rk ↥(fixV (autI hV (ch82A (fsuV T I) h))) = 4 * k ∧
      ch82ZI (fsuV T I) h = ch82U (fsuV T I) h ∧
      mQuot (fsuV T I) (ch82ZI (fsuV T I) h) = 5 * k ∧ rParam (fsuV T I) ≤ ((5 * k : ℕ) : ℕ∞) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, hN⟩ := hmod G T L I hyp.fsu
  have hNM := normalizer_fsuV_le_fsuM h37 h38 h39 hyp.fsu hV hN
  have hcase : Case8_2 T L I := Or.inl ⟨n, hrow⟩
  have hTL : T ≤ Subgroup.normalizer (L : Set G) := le_normalizer_of_case82 h711n hyp hcase
  obtain ⟨hw, hkn⟩ := l3_k_eq_82 h37 h38 h39 hmod h325 hin h711n h734 h756 hE214 htab hL9 hdiv
    hres hyp h731 h821 hrow hH hhH hC
  subst hkn
  obtain ⟨-, -, hk', hAC'⟩ := bounds_82 hmod h734 hyp h731 hH hC hV
  have hC' := hC
  obtain ⟨-, hhI, hIC, hZ1, -, hSyl, hMIeq, hker, -, hcases, hVZ, hBor, hA7, hAC, -, -, hm, -,
    h28, hchar, hTI⟩ := hC'
  have hWO := isWOffender_ch82A_82 hA7 hk' hAC' hw
  obtain ⟨hAel, hAN⟩ := ch82A_facts_82 hV hA7
  have hAel2 := isElemAbelian2_autI hV hAel hAN
  have hVp : IsPGroup 2 ↥(fsuV T I) := B2F.isPGroup_of_isElemAbelian hV
  obtain ⟨hT9, -, -⟩ := tab_82 (stmt7_4_1_of h37 h38 h39 hmod h325 hin) htab hyp h731 hTL hV hNM
  obtain ⟨hm2, hr4n, -, -⟩ := hT9 k hrow
  have hrA := rParam_sub_wParam_le_82 hyp hV hN hNM hWO
  have hfw := lemma_7_5_1 hyp hV hN hNM
  have hA : ch82A (fsuV T I) h = conjSubgroup (fsuV T I) h⁻¹ ⊓
      Subgroup.normalizer (fsuV T I : Set G) := by rw [hA7, conjSub_eq_conjSubgroup_82]
  have hrkA2 : rk ↥(autI hV (ch82A (fsuV T I) h)) ≤ CFSG.Open.pRank 2 (autI hV ⊤) := by
    rw [hA]
    exact rk_autI_le_pRank hV
  have hrkAm := rk_autI_eq_mQuot hV hAN
  rw [hw] at hfw hrA
  have hne : rParam (fsuV T I) ≠ ⊤ := fun htop => by
    rw [htop] at hfw
    exact absurd hfw (by simp)
  obtain ⟨r, hr⟩ := ENat.ne_top_iff_exists.mp hne
  rw [← hr] at hfw hrA hr4n
  have hfw' : r ≤ CFSG.Open.pRank 2 (autI hV ⊤) + k := by exact_mod_cast hfw
  have hr4n' : 4 * k ≤ r := by exact_mod_cast hr4n
  have hrA' : r - k ≤ rk ↥(autI hV (ch82A (fsuV T I) h)) := by
    have h1 : ((r - k : ℕ) : ℕ∞) = (r : ℕ∞) - (k : ℕ∞) := ENat.natCast_sub r k
    have h2 : ((r - k : ℕ) : ℕ∞) ≤ ((rk ↥(autI hV (ch82A (fsuV T I) h)) : ℕ) : ℕ∞) :=
      h1 ▸ hrA
    exact_mod_cast h2
  obtain ⟨-, hL3, -, -, -⟩ := hL9 (IntMod (fsuV T I) hV) (autI hV (fsuL0 T L))
    (autI hV ⊤) (isOver_autI_82 hV hNM) k hrow.1 hrow.2
  have h5n := hL3 _ (autI_mono hV le_top) hAel2 (Or.inl (by omega))
  have hfixU : fixV (autI hV (ch82A (fsuV T I) h)) =
      (ch82U (fsuV T I) h).comap (E3.valHom hV) := fixV_autI_eq_comap hV hAN
  have hUq : rkIdx (fixV (autI hV (ch82A (fsuV T I) h))) =
      mQuot (fsuV T I) (ch82U (fsuV T I) h) := by
    rw [hfixU, mQuot_eq_rkIdx_comap hV (U := ch82U (fsuV T I) h) inf_le_left]
  rw [hAC] at hm hrkAm
  have hcl := hIC.2.2.2.1
  rw [inf_inf_eq_82 (M := fsuM T L) hIC.1] at hcl
  have hP := pair_82 hV h28.le_T h28.normal_T hSyl hMIeq hhI hcl
  have hZU := ch82ZI_le_ch82U_82 hP
  have hUZ := E3.mQuot_mono (V := fsuV T I) hZU
  have hrkA4 : rk ↥(autI hV (ch82A (fsuV T I) h)) = 4 * k := by omega
  have hmU : mQuot (fsuV T I) (ch82U (fsuV T I) h) = 5 * k := by omega
  have hZeq : ch82ZI (fsuV T I) h = ch82U (fsuV T I) h :=
    eq_of_le_of_mQuot_le_82 hVp hZU inf_le_left (by omega)
  have hV9 : rk ↥(fsuV T I) = 9 * k :=
    rk_eq_of_card_82 (card_of_binaryNineTensor_82 hrow.1 hrow.2)
  have hrkU : rk ↥(fixV (autI hV (ch82A (fsuV T I) h))) = 4 * k := by
    rw [hfixU, rk_comap_valHom_82 hV (U := ch82U (fsuV T I) h) inf_le_left]
    have := mQuot_add_rk (A := fsuV T I) (B := ch82U (fsuV T I) h) inf_le_left
    omega
  refine ⟨rfl, hw, hrkA4, hrkU, hZeq, by rw [hZeq]; exact hmU, ?_⟩
  rw [← hr]
  exact_mod_cast (by omega : r ≤ 5 * k)

theorem l3_table_82 (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h39 : A39ForSQTK)
    (hmod : StmtFSUModule) (h325 : Stmt3_2_5) (hin : Input8_1_2) (h711n : Stmt7_1_1_normal)
    (h734 : Stmt7_3_4) (h756 : Stmt7_5_6_two) (h755 : Input7_5_5) (hE214 : AS_E_2_14)
    (htab : HTab82) (hL9 : HL3Nine82) (hdiv : Step823L3Div) (hres : Res823L3)
    (hres4 : Res824L3) (hyp : Hyp7_0_2 G T L I) (h731 : Hyp7_3_1 T L I) (h821 : Hyp8_2_1 T L I)
    [hc : IsMulCommutative ↥(fsuV T I)] {n : ℕ} (hrow : Row711L3Nine T L I n) {H : Subgroup G}
    {h : G} {k : ℕ} (hH : IsHStar T (fsuM T L) H) (hhH : h ∈ H) (hC : Concl822 T L I H h k)
    (hV : IsElemAbelian 2 (fsuV T I)) :
    n = 1 ∧ wParam T (fsuV T I) = 1 ∧ rParam (fsuV T I) = 5 ∧
      rk ↥(autI hV (ch82A (fsuV T I) h)) = 4 ∧ rk ↥(fixV (autI hV (ch82A (fsuV T I) h))) = 4 ∧
      ch82ZI (fsuV T I) h = ch82U (fsuV T I) h := by
  have hcase : Case8_2 T L I := Or.inl ⟨n, hrow⟩
  have hTL : T ≤ Subgroup.normalizer (L : Set G) := le_normalizer_of_case82 h711n hyp hcase
  obtain ⟨hkn, hw, hrkA4, hrkU, hZeq, -, hr5k⟩ := l3_rk_82 h37 h38 h39 hmod h325 hin h711n h734
    h756 hE214 htab hL9 hdiv hres hyp h731 h821 hrow hH hhH hC hV
  subst hkn
  have hk1 : k = 1 := hres4 G T L I hyp h731 h821 hc hcase H h k hH hhH hC k hrow
  subst hk1
  have hr5 := five_le_rParam_82 h37 h38 h39 hmod h325 hin h755 htab hL9 hyp h731 hTL hV hrow
  have hr5k' : rParam (fsuV T I) ≤ 5 := by simpa using hr5k
  exact ⟨rfl, hw, le_antisymm hr5k' hr5, hrkA4, hrkU, hZeq⟩

end L825M

end CFSG.Quasithin.H13

module

public import CFSG.Quasithin.Vol2.Ch8Statements
public import CFSG.Quasithin.Vol2.Ch3Sec2Lem327
public import CFSG.Quasithin.Vol2.Ch7Elim
public import CFSG.Quasithin.Background.E3OffenderB
public import CFSG.Quasithin.EmptyFaithful.S1422Basic
public import CFSG.Quasithin.Vol2.Ch8Inputs

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Quasithin.E3 CFSG.Quasithin.H
open scoped IsMulCommutative

variable {G : Type} [Group G] [Finite G]

section Internal

variable {V : Subgroup G} (hV : IsElemAbelian 2 V)

omit [Finite G] in
theorem map_comap_valHom {U : Subgroup G} (hUV : U ≤ V) :
    (U.comap (valHom hV)).map (valHom hV) = U := by
  rw [Subgroup.map_comap_eq]
  refine inf_eq_right.2 fun u hu => ?_
  exact ⟨IntMod.mk hV ⟨u, hUV hu⟩, rfl⟩

theorem mQuot_eq_rkIdx_comap {U : Subgroup G} (hUV : U ≤ V) :
    mQuot V U = rkIdx (U.comap (valHom hV)) := by
  rw [rkIdx_eq_mQuot_map, map_comap_valHom hV hUV]

omit [Finite G] in
theorem leFixI_iff {U : Subgroup G} {X : Subgroup (MulAut (IntMod V hV))} :
    LeFixI hV U X ↔ U.comap (valHom hV) ≤ fixV X :=
  ⟨fun h _ hv x hx => h _ hv x hx, fun h _ hv x hx => h hv x hx⟩

theorem rk_add_rkIdx (W : Subgroup (IntMod V hV)) :
    rk ↥W + rkIdx W = rk (IntMod V hV) := by
  unfold rk rkIdx
  rw [← padicValNat.mul Nat.card_pos.ne' W.index_ne_zero_of_finite, W.card_mul_index]

theorem card_intMod_eq : Nat.card (IntMod V hV) = 2 ^ rk (IntMod V hV) :=
  card_eq_two_pow_of_isPGroup (isPGroup_two_of_sq_eq_one IntMod.sq_eq_one)

omit [Finite G] in
theorem rk_intMod_of_card {n : ℕ} (h : Nat.card (IntMod V hV) = 2 ^ n) :
    rk (IntMod V hV) = n := by
  unfold rk
  rw [h, padicValNat.prime_pow]

end Internal

omit [Finite G] in
theorem centralizer_le_normalizer_of_ti {V M U : Subgroup G} (hTI : IsTISetUnder V M)
    (hUV : U ≤ V) (hU : U ≠ ⊥) (hCM : Subgroup.centralizer (U : Set G) ≤ M) :
    Subgroup.centralizer (U : Set G) ≤ Subgroup.normalizer (V : Set G) := by
  intro g hg
  by_contra hgN
  apply hU
  rw [eq_bot_iff, ← hTI g (hCM hg) hgN]
  intro u hu
  refine Subgroup.mem_inf.2 ⟨hUV hu, ?_⟩
  have hcomm : g * u = u * g := (Subgroup.mem_centralizer_iff.1 hg u hu).symm
  refine ⟨u, hUV hu, ?_⟩
  change g⁻¹ * u * g⁻¹⁻¹ = u
  rw [inv_inv, mul_assoc, ← hcomm, ← mul_assoc, inv_mul_cancel, one_mul]

theorem le_normalizer_of_cocodeRow (h711 : Stmt7_1_1_normal) {T L I : Subgroup G}
    (hyp : Hyp7_0_2 G T L I) [IsMulCommutative ↥(fsuV T I)] (hrow : CocodeRow T L I) :
    T ≤ Subgroup.normalizer (L : Set G) := by
  refine h711 G T L I hyp inferInstance ?_
  rcases hrow with h | h | h
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      (Or.inl h))))))))))

theorem isTISetUnder_of_cocodeRow (h711 : Stmt7_1_1_normal) (h325 : Stmt3_2_5)
    {T L I : Subgroup G} (hyp : Hyp7_0_2 G T L I) [IsMulCommutative ↥(fsuV T I)]
    (hrow : CocodeRow T L I) : IsTISetUnder (fsuV T I) (fsuM T L) :=
  isTISetUnder_of_stmt3_2_5_of_le_normalizer h325 hyp.fsu
    (le_normalizer_of_cocodeRow h711 hyp hrow)

omit [Finite G] in
theorem isOver_autI {T L I : Subgroup G} (hV : IsElemAbelian 2 (fsuV T I))
    (hNM : Subgroup.normalizer (fsuV T I : Set G) ≤ fsuM T L) :
    Mathieu.IsOver (autI hV (fsuL0 T L)) (autI hV ⊤) :=
  ⟨autI_fsuL0_le hV, autI_top_le_normalizer hV hNM⟩

theorem le_rParam_of_bound (h711 : Stmt7_1_1_normal) (h325 : Stmt3_2_5) (h811 : Stmt8_1_1)
    (hin : Input8_1_2) {T L I : Subgroup G} (hyp : Hyp7_0_2 G T L I) (h731 : Hyp7_3_1 T L I)
    [IsMulCommutative ↥(fsuV T I)] (hrow : CocodeRow T L I) (hV : IsElemAbelian 2 (fsuV T I))
    {n j : ℕ} (hn : Nat.card (IntMod (fsuV T I) hV) = 2 ^ n)
    (hj : ∀ U : Subgroup (IntMod (fsuV T I) hV),
      (∀ v ∈ U, ¬ Mathieu.IsCocodeO2 (autI hV (fsuL0 T L)) v) →
      ((∃ A : Subgroup (MulAut (IntMod (fsuV T I) hV)), IsFOneOffender (autI hV ⊤) A ∧
          U ≤ fixV A) ∨
        (∃ y ∈ autI hV ⊤, y ≠ 1 ∧ Odd (orderOf y) ∧ U ≤ fixV (Subgroup.zpowers y))) →
      rk ↥U ≤ j) :
    ((n - j : ℕ) : ℕ∞) ≤ rParam (fsuV T I) := by
  have hTL := le_normalizer_of_cocodeRow h711 hyp hrow
  have hLM := fsuM_le_normalizer_of_le_normalizer hTL
  have hTI := isTISetUnder_of_cocodeRow h711 h325 hyp hrow
  have hrkV := rk_intMod_of_card hV hn
  unfold rParam
  refine le_iInf₂ fun U hU => ?_
  obtain ⟨hUV, hC⟩ := hU
  rw [mQuot_eq_rkIdx_comap hV hUV]
  have hadd := rk_add_rkIdx hV (U.comap (valHom hV))
  rw [hrkV] at hadd
  by_cases hU1 : U = ⊥
  · have h0 : U.comap (valHom hV) = ⊥ := by
      rw [eq_bot_iff]
      intro v hv
      rw [Subgroup.mem_comap, hU1, Subgroup.mem_bot] at hv
      rw [Subgroup.mem_bot]
      exact valHom_injective hV (hv.trans (map_one _).symm)
    rw [h0, rk_bot] at hadd
    rw [h0]
    have : n - j ≤ rkIdx (⊥ : Subgroup (IntMod (fsuV T I) hV)) := by omega
    exact_mod_cast this
  · have hCM : ¬ Subgroup.centralizer (U : Set G) ≤ fsuM T L := fun h =>
      hC (centralizer_le_normalizer_of_ti hTI hUV hU1 h)
    have hO2 : ∀ v ∈ U.comap (valHom hV), ¬ Mathieu.IsCocodeO2 (autI hV (fsuL0 T L)) v := by
      intro v hv hvO
      apply hCM
      refine le_trans (Subgroup.centralizer_le ?_) (h811 G T L I hyp h731 inferInstance hrow hV v
        hvO)
      rw [Set.singleton_subset_iff]
      exact hv
    have hdich : (∃ A : Subgroup (MulAut (IntMod (fsuV T I) hV)), IsFOneOffender (autI hV ⊤) A ∧
          U.comap (valHom hV) ≤ fixV A) ∨
        (∃ y ∈ autI hV ⊤, y ≠ 1 ∧ Odd (orderOf y) ∧
          U.comap (valHom hV) ≤ fixV (Subgroup.zpowers y)) := by
      rcases hin G T L I hyp h731 hLM hV U hUV hU1 hCM with ⟨A, hA, hfix⟩ | ⟨y, hy, hy1, hyo, hfix⟩
      · exact Or.inl ⟨A, hA, (leFixI_iff hV).1 hfix⟩
      · exact Or.inr ⟨y, hy, hy1, hyo, (leFixI_iff hV).1 hfix⟩
    have := hj _ hO2 hdich
    exact_mod_cast (show n - j ≤ rkIdx (U.comap (valHom hV)) by omega)

theorem stmt8_1_2_of (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h39 : A39ForSQTK)
    (hmod : StmtFSUModule) (h711 : Stmt7_1_1_normal) (h325 : Stmt3_2_5) (h811 : Stmt8_1_1)
    (hin : Input8_1_2) (hcard : Mathieu.StmtH13Card) (hO2 : Mathieu.StmtH15O2) :
    Stmt8_1_2 := by
  intro G _ _ T L I hyp h731 hc
  obtain ⟨hV, hN⟩ := hmod G T L I hyp.fsu
  have hNM := normalizer_fsuV_le_fsuM h37 h38 h39 hyp.fsu hV hN
  have hover := isOver_autI (T := T) (L := L) (I := I) hV hNM
  have hbound := fun U hU hd => hO2 (IntMod (fsuV T I) hV) (autI hV (fsuL0 T L)) (autI hV ⊤)
    hover U hU hd
  refine ⟨fun hrow => ?_, fun hrow => ?_, fun hrow => ?_⟩
  · have hn := (hcard (IntMod (fsuV T I) hV) (autI hV (fsuL0 T L))).2.2 (Or.inl hrow)
    have h := le_rParam_of_bound h711 h325 h811 hin hyp h731 (Or.inl hrow) hV
      hn (j := 4) fun U hU hd => (hbound U hU hd).1 hrow
    exact h
  · have hn := (hcard (IntMod (fsuV T I) hV) (autI hV (fsuL0 T L))).2.1 (Or.inl hrow)
    have h := le_rParam_of_bound h711 h325 h811 hin hyp h731
      (Or.inr (Or.inl hrow)) hV hn (j := 4) fun U hU hd => (hbound U hU hd).2.1 hrow
    exact h
  · have hn := (hcard (IntMod (fsuV T I) hV) (autI hV (fsuL0 T L))).1 (Or.inl hrow)
    have h := le_rParam_of_bound h711 h325 h811 hin hyp h731
      (Or.inr (Or.inr hrow)) hV hn (j := 3) fun U hU hd => (hbound U hU hd).2.2 hrow
    exact h

section Gamma

variable {W : Type*} [CommGroup W] [Finite W]

omit [Finite W] in
theorem mQuot_add_rk {X : Type*} [Group X] [Finite X] {A B : Subgroup X} (hBA : B ≤ A) :
    mQuot A B + rk ↥B = rk ↥A := by
  unfold mQuot rk
  have h := Subgroup.relIndex_mul_card B A
  rw [inf_eq_left.2 hBA] at h
  rw [← padicValNat.mul (relIndex_ne_zero' A B) Nat.card_pos.ne', h]

theorem card_eq_two_pow_rk {A : Subgroup (MulAut W)} (hA : IsElemAbelian2 A) :
    Nat.card ↥A = 2 ^ rk ↥A := by
  have : Finite (MulAut W) := MulEquiv.finite_left
  exact card_eq_two_pow_of_isPGroup (isPGroup_of_isElemAbelian2 hA)

theorem xiV_le_gammaCheck {A : Subgroup (MulAut W)} (hA : IsElemAbelian2 A) {k : ℕ}
    (hk : rk ↥A ≤ k + 1) : Mathieu.xiV A ≤ gammaCheck k A := by
  have : Finite (MulAut W) := MulEquiv.finite_left
  unfold Mathieu.xiV gammaCheck
  refine iSup_le fun a => iSup_le fun ha => iSup_le fun ha1 => ?_
  have hle : Subgroup.zpowers a ≤ A := (Subgroup.zpowers_le).2 ha
  have hord : orderOf a = 2 := orderOf_eq_prime (hA.2 a ha) ha1
  have hrk : rk ↥(Subgroup.zpowers a) = 1 := by
    unfold rk
    rw [Nat.card_zpowers, hord, padicValNat_self]
  have hm := mQuot_add_rk hle
  refine le_iSup_of_le (Subgroup.zpowers a) (le_iSup_of_le hle (le_iSup_of_le ?_ le_rfl))
  omega

theorem iSup_fixV_four_le_gammaCheck {A : Subgroup (MulAut W)} {k : ℕ}
    (hk : rk ↥A ≤ k + 2) :
    (⨆ (B : Subgroup (MulAut W)) (_ : B ≤ A) (_ : Nat.card B = 4), fixV B) ≤ gammaCheck k A := by
  have : Finite (MulAut W) := MulEquiv.finite_left
  unfold gammaCheck
  refine iSup_le fun B => iSup_le fun hBA => iSup_le fun hB4 => ?_
  have hrk : rk ↥B = 2 := by
    unfold rk
    rw [hB4, show (4 : ℕ) = 2 ^ 2 from rfl, padicValNat.prime_pow]
  have hm := mQuot_add_rk hBA
  refine le_iSup_of_le B (le_iSup_of_le hBA (le_iSup_of_le ?_ le_rfl))
  omega

end Gamma

section WeakClosure

variable {T V : Subgroup G}

theorem min_le_rkIdx_of_le_gammaCheck (hV : IsElemAbelian 2 V) (hT : HypE322 T V) {g : G}
    (hg : IsWOffenderAt T V g) {k : ℕ} (hk : (k : ℕ∞) + wParam T V + 1 ≤ rParam V)
    {X : Subgroup (IntMod V hV)}
    (hX : X ≤ gammaCheck k (autI hV (conjSubgroup V g ⊓ Subgroup.normalizer (V : Set G)))) :
    min (wParam T V) (rParam V) ≤ (rkIdx X : ℕ∞) := by
  have h1 := e3_32 hV hg hk
  have h2 : X.map (valHom hV) ≤ V ⊓ Subgroup.normalizer (conjSubgroup V g : Set G) :=
    (Subgroup.map_mono hX).trans h1
  have h3 := min_le_mQuot_inf_normalizer_conj hV hT hg.1
  rw [rkIdx_eq_mQuot_map]
  exact h3.trans (Nat.cast_le.2 (mQuot_mono h2))

omit [Finite G] in
theorem rkIdx_top_eq (X : Type*) [Group X] : rkIdx (⊤ : Subgroup X) = 0 := by
  simp [rkIdx]

end WeakClosure

omit [Finite G] in
theorem nPrime_eq_two_of_cocodeRow {T L I : Subgroup G} [IsMulCommutative ↥(fsuV T I)]
    (hrow : CocodeRow T L I) {k : ℕ} (hk : IsNPrime721 T L I k) : k = 2 := by
  refine (hk inferInstance).2.2.2.1 ?_
  rcases hrow with h | h | h
  · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))

theorem stmt8_1_3_of (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h39 : A39ForSQTK)
    (hmod : StmtFSUModule) (h812 : Stmt8_1_2) (h734 : Stmt7_3_4) (hcard : Mathieu.StmtH13Card)
    (hpr : Mathieu.StmtH14PRank) (hM22 : Mathieu.StmtH15M22) (hM24 : Mathieu.StmtH15M24) :
    Stmt8_1_3 := by
  intro G _ _ T L I hyp h731 hc hrow
  obtain ⟨hV, hN⟩ := hmod G T L I hyp.fsu
  have hNM := normalizer_fsuV_le_fsuM h37 h38 h39 hyp.fsu hV hN
  have hT := hypE322_of_fsu hyp.fsu hV hN
  have h24 := hypE324_of_hyp702 hyp hV hNM
  have hover := isOver_autI (T := T) (L := L) (I := I) hV hNM
  have : Finite (MulAut (IntMod (fsuV T I) hV)) := MulEquiv.finite_left
  obtain ⟨hHn, hwn, -, hn'⟩ := h734 G T L I hyp h731 hV
  have hn2 := nPrime_eq_two_of_cocodeRow hrow hn'
  rw [hn2] at hwn hHn
  have hw2 : wParam T (fsuV T I) ≤ 2 := by exact_mod_cast hwn
  have hwtop : wParam T (fsuV T I) ≠ ⊤ := ne_top_of_le_ne_top (by simp) hw2
  have key : ∀ g : G, IsWOffenderAt T (fsuV T I) g →
      rParam (fsuV T I) ≤ wParam T (fsuV T I) +
        ((rk ↥(autI hV (conjSubgroup (fsuV T I) g ⊓
          Subgroup.normalizer (fsuV T I : Set G))) : ℕ) : ℕ∞) ∧
      rk ↥(autI hV (conjSubgroup (fsuV T I) g ⊓ Subgroup.normalizer (fsuV T I : Set G))) ≤
        CFSG.Open.pRank 2 (autI hV ⊤) ∧
      IsElemAbelian2 (autI hV (conjSubgroup (fsuV T I) g ⊓
        Subgroup.normalizer (fsuV T I : Set G))) := by
    intro g hg
    refine ⟨e3_28_two_left hV hT h24 hg, rk_autI_le_pRank hV, ?_⟩
    exact isElemAbelian2_autI hV (B2F.isElemAbelian_mono inf_le_left
      (isElemAbelian_conjSubgroup hV g)) inf_le_right
  obtain ⟨g, hg⟩ := exists_isWOffenderAt hV hT hwtop
  obtain ⟨hrA, hAm, hAel⟩ := key g hg
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
  obtain ⟨h22, h23, h24r⟩ := h812 G T L I hyp h731 hc
  rcases hrow with hr | hr | hr
  ·
    exfalso
    have hm2 := (hpr _ _ _ hover).2.2 (Or.inl hr)
    have h6 := h22 hr
    rw [← hr'] at h6
    have h6' : 6 ≤ r' := by exact_mod_cast h6
    have hfacts := hM22 _ _ _ hover hr
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
    have hm2 := (hpr _ _ _ hover).2.1 (Or.inl hr)
    have h7 := h23 hr
    rw [← hr'] at h7
    have h7' : 7 ≤ r' := by exact_mod_cast h7
    omega
  ·
    have hm2 := (hpr _ _ _ hover).1 (Or.inl hr)
    have h8 := h24r hr
    rw [← hr'] at h8
    have h8' : 8 ≤ r' := by exact_mod_cast h8
    have hw2' : w' = 2 := by omega
    have hr8 : r' = 8 := by omega
    have hwP : wParam T (fsuV T I) = 2 := by rw [← hw', hw2']; rfl
    have hrP : rParam (fsuV T I) = 8 := by rw [← hr', hr8]; rfl
    have hcardV := (hcard (IntMod (fsuV T I) hV) (autI hV (fsuL0 T L))).1 (Or.inl hr)
    refine ⟨hr, hrP, hwP, fun H hH => ?_, fun hV' A hA => ?_⟩
    · obtain ⟨h1, h2⟩ := hHn H hH
      rw [hwP] at h1
      exact le_antisymm (by exact_mod_cast h2) h1
    · obtain ⟨g', rfl, hg'⟩ := hA
      obtain ⟨hrA2, hAm2, hAel2⟩ := key g' hg'
      rw [hwP, hrP] at hrA2
      have hrk6 : rk ↥(autI hV (conjSubgroup (fsuV T I) g' ⊓
          Subgroup.normalizer (fsuV T I : Set G))) = 6 := by
        have : 8 ≤ 2 + rk ↥(autI hV (conjSubgroup (fsuV T I) g' ⊓
            Subgroup.normalizer (fsuV T I : Set G))) := by exact_mod_cast hrA2
        omega
      refine ⟨?_, hrk6, ?_⟩
      ·
        have hVg : rk ↥(conjSubgroup (fsuV T I) g') = 11 := by
          unfold rk
          rw [card_conjSubgroup, show Nat.card ↥(fsuV T I) = Nat.card (IntMod (fsuV T I) hV)
            from rfl, hcardV, padicValNat.prime_pow]
        have hm1 := mQuot_add_rk (inf_le_left : conjSubgroup (fsuV T I) g' ⊓
          Subgroup.normalizer (fsuV T I : Set G) ≤ conjSubgroup (fsuV T I) g')
        have hm3 := mQuot_add_rk (inf_le_left : conjSubgroup (fsuV T I) g' ⊓
          Subgroup.normalizer (fsuV T I : Set G) ⊓ Subgroup.centralizer (fsuV T I : Set G) ≤
            conjSubgroup (fsuV T I) g' ⊓ Subgroup.normalizer (fsuV T I : Set G))
        rw [← rk_autI_eq_mQuot hV inf_le_right, hrk6] at hm3
        have hwm := hg'.2
        rw [hwP] at hwm
        have hwm' : mQuot (conjSubgroup (fsuV T I) g') (conjSubgroup (fsuV T I) g' ⊓
            Subgroup.normalizer (fsuV T I : Set G)) = 2 := by exact_mod_cast hwm.symm
        omega
      ·
        have hcard64 : Nat.card ↥(autI hV (conjSubgroup (fsuV T I) g' ⊓
            Subgroup.normalizer (fsuV T I : Set G))) = 64 := by
          rw [card_eq_two_pow_rk hAel2, hrk6]; rfl
        rcases hM24 _ _ _ hover hr _ (autI_mono hV le_top) hAel2 hcard64 with hxi | h3
        · exfalso
          have hk : ((5 : ℕ) : ℕ∞) + wParam T (fsuV T I) + 1 ≤ rParam (fsuV T I) := by
            rw [hwP, hrP]; rfl
          have h := min_le_rkIdx_of_le_gammaCheck hV hT hg' hk
            (X := Mathieu.xiV (autI hV (conjSubgroup (fsuV T I) g' ⊓
              Subgroup.normalizer (fsuV T I : Set G)))) (xiV_le_gammaCheck hAel2 (by omega))
          rw [hxi, rkIdx_top_eq, hwP, hrP] at h
          exact absurd h (by decide)
        · exact h3

theorem stmt8_1_3_M24_of (h813 : Stmt8_1_3) : Stmt8_1_3_M24 := by
  intro G _ _ T L I hyp h731 hc hrow
  exact (h813 G T L I hyp h731 hc hrow).1

end CFSG.Quasithin.H13

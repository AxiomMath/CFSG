module

public import CFSG.RankThree.PartTwo.Sec4.Sporadic.J2Sig5
public import CFSG.RankThree.PartTwo.KFacts.L34Sylow

public section

namespace CFSG.RankThree.PartTwo.Sec4.Sporadic.J2

open CFSG.ComponentClassification.J2Cover CFSG.Certificates CFSG.Certificates.Native
  CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.RankThree.Native CFSG.Monster.B.Mathieu
  CFSG.RankThree.Asc83Table Subgroup CFSG.Fischer Matrix
open scoped commutatorElement Pointwise

theorem u34Gens_size : u34Gens.size = 4 := rfl

theorem ok_u (j : Fin 4) : okA u34Gens[j.1]! = true := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, h, -⟩ := elts45
  exact allLt_spec h (by rw [u34Gens_size]; exact j.2)

@[expose] noncomputable def uJ (j : Fin 4) : GJ := eltOf u34Gens[j.1]! (ok_u j)

theorem rep_u (j : Fin 4) : Rep 315 u34Gens[j.1]! (uJ j).1 := rep_eltOf _

theorem valid_u (j : Fin 4) : validA 315 u34Gens[j.1]! = true := (okA_spec (ok_u j)).1

theorem uJ_mem (j : Fin 4) : uJ j ∈ SJ 0 :=
  mem_S_of_inCert (rep_u j) (List.all_eq_true.1 chkS_16 j.1 (List.mem_range.2 j.2))

@[expose] noncomputable def phiE (a b c : ℕ) : GJ :=
  (uJ 0 ^ (a % 2) * uJ 1 ^ (a / 2)) * ((uJ 2 ^ (b % 2) * uJ 3 ^ (b / 2)) *
    (⁅uJ 0, uJ 2⁆ ^ (c % 2) * ⁅uJ 0, uJ 3⁆ ^ (c / 2)))

theorem rep_commutator {t u : Array ℕ} {g h : GJ} (ht : Rep 315 t g.1)
    (hvt : validA 315 t = true) (hu : Rep 315 u h.1) (hvu : validA 315 u = true) :
    Rep 315 (commutatorA 315 t u) ⁅g, h⁆.1 := by
  have := rep_commutatorA hvt hvu
  rw [(rep_of_validA hvt).unique ht, (rep_of_validA hvu).unique hu] at this
  simpa [commutatorElement_def] using this

theorem rep_phi (a b c : ℕ) : Rep 315 (phiA a b c) (phiE a b c).1 :=
  rep_mul (rep_mul (rep_pow (rep_u 0) _) (rep_pow (rep_u 1) _))
    (rep_mul (rep_mul (rep_pow (rep_u 2) _) (rep_pow (rep_u 3) _))
      (rep_mul (rep_pow (rep_commutator (rep_u 0) (valid_u 0) (rep_u 2) (valid_u 2)) _)
        (rep_pow (rep_commutator (rep_u 0) (valid_u 0) (rep_u 3) (valid_u 3)) _)))

theorem phiE_mem (a b c : ℕ) : phiE a b c ∈ SJ 0 := by
  have h0 := uJ_mem 0
  have h1 := uJ_mem 1
  have h2 := uJ_mem 2
  have h3 := uJ_mem 3
  have c2 : ⁅uJ 0, uJ 2⁆ ∈ SJ 0 := by
    rw [commutatorElement_def]
    exact mul_mem (mul_mem (mul_mem h0 h2) (inv_mem h0)) (inv_mem h2)
  have c3 : ⁅uJ 0, uJ 3⁆ ∈ SJ 0 := by
    rw [commutatorElement_def]
    exact mul_mem (mul_mem (mul_mem h0 h3) (inv_mem h0)) (inv_mem h3)
  exact mul_mem (mul_mem (pow_mem h0 _) (pow_mem h1 _))
    (mul_mem (mul_mem (pow_mem h2 _) (pow_mem h3 _)) (mul_mem (pow_mem c2 _) (pow_mem c3 _)))

theorem phiE_mul {a b c a' b' c' : ℕ} (ha : a < 4) (hb : b < 4) (hc : c < 4) (ha' : a' < 4)
    (hb' : b' < 4) (hc' : c' < 4) :
    phiE a b c * phiE a' b' c' = phiE (a ^^^ a') (b ^^^ b') (c ^^^ c' ^^^ mulCode4 a' b) := by
  have h := List.all_eq_true.1 chkS_17 a (List.mem_range.2 ha)
  have h := List.all_eq_true.1 h b (List.mem_range.2 hb)
  have h := List.all_eq_true.1 h c (List.mem_range.2 hc)
  have h := List.all_eq_true.1 h a' (List.mem_range.2 ha')
  have h := List.all_eq_true.1 h b' (List.mem_range.2 hb')
  have h := List.all_eq_true.1 h c' (List.mem_range.2 hc')
  exact eq_of_rep (rep_mul (rep_phi a b c) (rep_phi a' b' c')) (rep_phi _ _ _) h

theorem phiE_injective {a b c a' b' c' : ℕ} (ha : a < 4) (hb : b < 4) (hc : c < 4)
    (ha' : a' < 4) (hb' : b' < 4) (hc' : c' < 4) (h : phiE a b c = phiE a' b' c') :
    a = a' ∧ b = b' ∧ c = c' := by
  have h1 := List.all_eq_true.1 chkVk_4 a (List.mem_range.2 ha)
  have h1 := List.all_eq_true.1 h1 b (List.mem_range.2 hb)
  have h1 := List.all_eq_true.1 h1 c (List.mem_range.2 hc)
  have h1 := List.all_eq_true.1 h1 a' (List.mem_range.2 ha')
  have h1 := List.all_eq_true.1 h1 b' (List.mem_range.2 hb')
  have h1 := List.all_eq_true.1 h1 c' (List.mem_range.2 hc')
  have he : eqA 315 (phiA a b c) (phiA a' b' c') = true :=
    (eqA_iff (rep_phi a b c) (rep_phi a' b' c')).2 (by rw [h])
  rw [he] at h1
  simpa [and_assoc] using h1

theorem phiE_zero : phiE 0 0 0 = 1 := by simp [phiE]

theorem code_add (x y : F4) : ((x + y).code : ℕ) = (x.code : ℕ) ^^^ (y.code : ℕ) := by
  revert x y
  decide

theorem code_mul (x y : F4) : ((x * y).code : ℕ) = mulCode4 x.code y.code := by
  revert x y
  decide

@[expose] noncomputable def phiS (p : F4 × F4 × F4) : SJ 0 :=
  ⟨phiE p.1.code p.2.1.code p.2.2.code, phiE_mem _ _ _⟩

theorem phiS_injective : Function.Injective phiS := by
  rintro ⟨⟨a⟩, ⟨b⟩, ⟨c⟩⟩ ⟨⟨a'⟩, ⟨b'⟩, ⟨c'⟩⟩ h
  have h' := congrArg Subtype.val h
  obtain ⟨h1, h2, h3⟩ := phiE_injective a.2 b.2 c.2 a'.2 b'.2 c'.2 h'
  simp only [Prod.mk.injEq, F4.mk.injEq]
  exact ⟨Fin.ext h1, Fin.ext h2, Fin.ext h3⟩

theorem card_F4_cube : Nat.card (F4 × F4 × F4) = 64 := by
  rw [Nat.card_eq_fintype_card, Fintype.card_prod, Fintype.card_prod, F4.card]

theorem phiS_bijective : Function.Bijective phiS :=
  phiS_injective.bijective_of_nat_card_le (le_of_eq (by rw [card_S, card_F4_cube]))

@[expose] noncomputable def phiEquiv : F4 × F4 × F4 ≃ SJ 0 :=
  Equiv.ofBijective phiS phiS_bijective

@[expose] def utLaw (p q : F4 × F4 × F4) : F4 × F4 × F4 :=
  (p.1 + q.1, p.2.1 + q.2.1, p.2.2 + q.2.2 + q.1 * p.2.1)

theorem phiS_mul (p q : F4 × F4 × F4) : phiS p * phiS q = phiS (utLaw p q) := by
  apply Subtype.ext
  simp only [phiS, utLaw, Subgroup.coe_mul]
  rw [phiE_mul p.1.code.2 p.2.1.code.2 p.2.2.code.2 q.1.code.2 q.2.1.code.2 q.2.2.code.2,
    code_add, code_add, code_add, code_add, code_mul]

theorem phiS_zero : phiS (0, 0, 0) = 1 := Subtype.ext phiE_zero

@[expose] noncomputable def utMat (p : F4 × F4 × F4) : Matrix (Fin 3) (Fin 3) (GaloisField 2 2) :=
  !![1, F4.equivGaloisField p.2.1, F4.equivGaloisField p.2.2;
    0, 1, F4.equivGaloisField p.1; 0, 0, 1]

theorem det_utMat (p : F4 × F4 × F4) : (utMat p).det = 1 := by
  simp [utMat, Matrix.det_fin_three]

theorem utMat_mul (p q : F4 × F4 × F4) : utMat p * utMat q = utMat (utLaw p q) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [utMat, utLaw, Matrix.mul_apply, Fin.sum_univ_three, map_add, map_mul] <;> ring

@[expose] noncomputable def utGL (p : F4 × F4 × F4) : GL (Fin 3) (GaloisField 2 2) :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero (utMat p) (by rw [det_utMat]; exact one_ne_zero)

theorem utGL_mul (p q : F4 × F4 × F4) : utGL p * utGL q = utGL (utLaw p q) :=
  Units.ext (by simp only [Units.val_mul, utGL, GeneralLinearGroup.val_mkOfDetNeZero, utMat_mul])

theorem utGL_zero : utGL (0, 0, 0) = 1 := by
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j <;> simp [utGL, utMat]

theorem utGL_mem_ker (p : F4 × F4 × F4) :
    utGL p ∈ (GeneralLinearGroup.det : GL (Fin 3) (GaloisField 2 2) →* (GaloisField 2 2)ˣ).ker :=
  MonoidHom.mem_ker.2 (Units.ext (det_utMat p))

theorem eq_zero_of_center {p : F4 × F4 × F4}
    (h : utGL p ∈ Subgroup.center (GL (Fin 3) (GaloisField 2 2))) : p = (0, 0, 0) := by
  obtain ⟨a, b, c⟩ := p
  rw [GeneralLinearGroup.center_eq_range_scalar] at h
  obtain ⟨u, hu⟩ := h
  have hM := congrArg (fun M : GL (Fin 3) (GaloisField 2 2) =>
    (M : Matrix (Fin 3) (Fin 3) (GaloisField 2 2))) hu
  simp only [utGL, GeneralLinearGroup.val_mkOfDetNeZero, GeneralLinearGroup.coe_scalar] at hM
  have h01 := congrFun (congrFun hM 0) 1
  have h12 := congrFun (congrFun hM 1) 2
  have h02 := congrFun (congrFun hM 0) 2
  have hb : F4.equivGaloisField b = 0 := by simpa [utMat] using h01.symm
  have ha : F4.equivGaloisField a = 0 := by simpa [utMat] using h12.symm
  have hc : F4.equivGaloisField c = 0 := by simpa [utMat] using h02.symm
  rw [map_eq_zero_iff _ F4.equivGaloisField.injective] at ha hb hc
  rw [ha, hb, hc]

noncomputable abbrev L34 : Subgroup (ProjGenLinGroup (Fin 3) (GaloisField 2 2)) :=
  CFSG.Assembly.RankThreeEven.projSL 3 (GaloisField 2 2)

theorem mk_utGL_mem (p : F4 × F4 × F4) : ProjGenLinGroup.mk (utGL p) ∈ L34 :=
  Subgroup.mem_map_of_mem _ (utGL_mem_ker p)

theorem card_galoisField_four : Nat.card (GaloisField 2 2) = 4 := by
  rw [GaloisField.card 2 2 (by norm_num)]
  norm_num

theorem card_projSL_three : Nat.card L34 = 20160 := by
  have hrange : L34 = (SpecialLinearGroup.toPGL : SpecialLinearGroup (Fin 3) (GaloisField 2 2) →*
      ProjGenLinGroup (Fin 3) (GaloisField 2 2)).range := by
    rw [L34, CFSG.Assembly.RankThreeEven.projSL, CFSG.Assembly.RankThreeEven.projImage,
      SpecialLinearGroup.toPGL, MonoidHom.range_comp, SpecialLinearGroup.range_toGL_eq_ker_det]
  rw [hrange, ← Nat.card_congr (QuotientGroup.quotientKerEquivRange _).toEquiv,
    ← CFSG.RankThree.PartTwo.KFacts.L34.card_projectiveSL card_galoisField_four]
  refine Nat.card_congr (QuotientGroup.quotientMulEquivOfEq ?_).toEquiv
  rw [SpecialLinearGroup.toPGL_ker,
    CFSG.LocalAnalysis.ComponentInitial.LinearFlag.scalars_eq_center]

theorem factorization_L34 : (Nat.card L34).factorization 2 = 6 := by
  rw [card_projSL_three]
  exact factorization_eq_of_eq Nat.prime_two (show (20160 : ℕ) = 2 ^ 6 * 315 by norm_num)
    (by norm_num)

@[expose] noncomputable def toL34 : SJ 0 →* L34 where
  toFun s := ⟨ProjGenLinGroup.mk (utGL (phiEquiv.symm s)), mk_utGL_mem _⟩
  map_one' := by
    have : phiEquiv.symm 1 = (0, 0, 0) := by
      rw [Equiv.symm_apply_eq]
      exact phiS_zero.symm
    apply Subtype.ext
    show ProjGenLinGroup.mk (utGL (phiEquiv.symm 1)) = 1
    rw [this, utGL_zero, map_one]
  map_mul' s t := by
    have : phiEquiv.symm (s * t) = utLaw (phiEquiv.symm s) (phiEquiv.symm t) := by
      rw [Equiv.symm_apply_eq]
      change s * t = phiS (utLaw (phiEquiv.symm s) (phiEquiv.symm t))
      rw [← phiS_mul]
      exact congrArg₂ (· * ·) (phiEquiv.apply_symm_apply s).symm
        (phiEquiv.apply_symm_apply t).symm
    apply Subtype.ext
    show ProjGenLinGroup.mk (utGL (phiEquiv.symm (s * t))) =
      ProjGenLinGroup.mk (utGL (phiEquiv.symm s)) * ProjGenLinGroup.mk (utGL (phiEquiv.symm t))
    rw [this, ← utGL_mul, map_mul]

theorem toL34_injective : Function.Injective toL34 := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro s hs
  rw [MonoidHom.mem_ker] at hs
  have h1 : ProjGenLinGroup.mk (utGL (phiEquiv.symm s)) = 1 := congrArg Subtype.val hs
  rw [ProjGenLinGroup.mk_eq_one] at h1
  have h0 := eq_zero_of_center h1
  rw [Equiv.symm_apply_eq] at h0
  rw [Subgroup.mem_bot, h0]
  exact phiS_zero

theorem card_range_toL34 : Nat.card toL34.range = 64 := by
  rw [← Nat.card_congr (MonoidHom.ofInjective toL34_injective).toEquiv, card_S]

theorem exists_sylow_equiv : ∃ T : Sylow 2 L34, Nonempty (SJ 0 ≃* (T : Subgroup L34)) := by
  have : Finite (ProjGenLinGroup (Fin 3) (GaloisField 2 2)) :=
    Finite.of_surjective _ ProjGenLinGroup.mk_surjective
  exact ⟨Sylow.ofCard toL34.range (by rw [card_range_toL34, factorization_L34]; norm_num),
    ⟨MonoidHom.ofInjective toL34_injective⟩⟩

theorem S0_inf_Cz : SJ 0 ⊓ centralizer ({zJ} : Set GJ) = WJ 0 := by
  apply le_antisymm
  · rintro g ⟨hgS, hgC⟩
    obtain ⟨k, hk, hr⟩ := exists_rep_subOf (by decide) (enumS 0 (by norm_num)).1 hgS
    have hck := allLt_spec chkS_12 hk
    rw [Bool.or_eq_true, Bool.not_eq_true'] at hck
    rcases hck with h | h
    · rw [commA_of_commute hr rep_z (mem_centralizer_singleton_iff.1 hgC)] at h
      exact absurd h Bool.noConfusion
    · exact mem_W_of_inW (i := 0) hr h
  · exact le_inf W0_le_S0 (W_le_Cz 0)

theorem vSel (e : ℕ) : ∃ v ∈ VJ, Rep 315 (if e = 0 then idA 315 else if e = 1 then v1Arr else
    if e = 2 then v2Arr else compA 315 v1Arr v2Arr) v.1 := by
  split_ifs
  · exact ⟨1, one_mem _, rep_one⟩
  · exact ⟨v1J, v1_mem_V, rep_v1⟩
  · exact ⟨v2J, v2_mem_V, rep_v2⟩
  · exact ⟨v1J * v2J, mul_mem v1_mem_V v2_mem_V, rep_mul rep_v1 rep_v2⟩

theorem S0_eq_mul : (WJ 0 : Set GJ) * (VkJ 0 : Set GJ) * (VkJ 1 : Set GJ) = (SJ 0 : Set GJ) := by
  apply Set.Subset.antisymm
  · rintro _ ⟨_, ⟨w, hw, v, hv, rfl⟩, u, hu, rfl⟩
    exact (SJ 0).mul_mem ((SJ 0).mul_mem (W0_le_S0 hw) (V0_le_S0 hv)) (V1_le_S0 hu)
  · intro g hg
    obtain ⟨k, hk, hr⟩ := exists_rep_subOf (by decide) (enumS 0 (by norm_num)).1 hg
    have hck := allLt_spec chkS_13 hk
    rw [List.any_eq_true] at hck
    obtain ⟨wa, hwa, hck⟩ := hck
    rw [List.any_eq_true] at hck
    obtain ⟨e, -, hck⟩ := hck
    rw [List.any_eq_true] at hck
    obtain ⟨f, -, hck⟩ := hck
    obtain ⟨w, hw, hrw⟩ := wElts_rep (i := 0) hwa
    obtain ⟨v, hv, hrv⟩ := vSel e
    obtain ⟨u, hu, hru⟩ := vSel f
    have hg' := eq_of_rep hr (rep_mul hrw (rep_mul (rep_conj (rep_c 0) (valid_c 0) hrv)
      (rep_conj (rep_c 1) (valid_c 1) hru))) hck
    refine ⟨w * (cJ 0 * v * (cJ 0)⁻¹), ⟨w, hw, cJ 0 * v * (cJ 0)⁻¹, ⟨v, hv, rfl⟩, rfl⟩,
      cJ 1 * u * (cJ 1)⁻¹, ⟨u, hu, rfl⟩, ?_⟩
    rw [hg']
    simp only [mul_assoc]

theorem closure_a01 : closure ({aJ 0, aJ 1} : Set GJ) = E0 := by
  apply le_antisymm
  · rw [closure_le]
    rintro _ (rfl | rfl)
    · exact aJ_mem_E0 0
    · exact aJ_mem_E0 1
  · have h0 : aJ 0 = xJ := by simp [aJ]
    have h1 : aJ 1 = zJ * xJ := by simp [aJ]
    have hx : xJ ∈ closure ({aJ 0, aJ 1} : Set GJ) := by
      rw [← h0]; exact subset_closure (Set.mem_insert _ _)
    have ha1 : aJ 1 ∈ closure ({aJ 0, aJ 1} : Set GJ) :=
      subset_closure (Set.mem_insert_of_mem _ rfl)
    rw [show E0 = closure {⁅xJ, yJ⁆, xJ} from rfl, closure_le]
    rintro _ (rfl | rfl)
    · rw [← z_eq]
      have : zJ = aJ 1 * xJ⁻¹ := by rw [h1]; group
      rw [this]
      exact mul_mem ha1 (inv_mem hx)
    · exact hx

theorem sig5_E0 :
    ∃ S ∈ maxInvariantPiSubgroups ⊤ E0 (piOf 2),
      maxInvariantPiSubgroups ⊤ E0 (piOf 2) = (conjugate S) '' (P3 : Set GJ) ∧
      (maxInvariantPiSubgroups ⊤ E0 (piOf 2)).ncard = 3 ∧
      (∃ T : Sylow 2 L34, Nonempty (S ≃* (T : Subgroup L34))) ∧
      ∃ a b : GJ, closure {a, b} = E0 ∧
        ((S ⊓ centralizer ((P3 ⊓ centralizer (P3 : Set GJ) : Subgroup GJ) : Set GJ) :
            Subgroup GJ) : Set GJ) *
          (inSubgroup (CFSG.pCore 2) (centralizer {a}) : Set GJ) *
          (inSubgroup (CFSG.pCore 2) (centralizer {b}) : Set GJ) = S := by
  refine ⟨SJ 0, by rw [maxInvariant_E0]; exact ⟨0, rfl⟩, by rw [maxInvariant_E0, range_S_eq],
    ncard_maxInvariant_E0, exists_sylow_equiv, aJ 0, aJ 1, closure_a01, ?_⟩
  rw [inf_centralizer_P3, ← z_eq, centralizer_zpowers_eq, S0_inf_Cz, pCore_centralizer_a,
    pCore_centralizer_a]
  exact S0_eq_mul

end CFSG.RankThree.PartTwo.Sec4.Sporadic.J2

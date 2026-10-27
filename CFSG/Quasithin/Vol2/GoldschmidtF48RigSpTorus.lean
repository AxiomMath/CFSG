module

public import CFSG.Quasithin.Vol2.GoldschmidtF431F45SpGeomBase

public section

namespace CFSG.Quasithin.H13.F431.F48Sp

open Matrix CFSG.ComponentClassification.UnbalancedCatalog.SpChain
  CFSG.QuasithinUnique.Setup.X7b CFSG.RankThree.PartOne.KCRootAxis
  CFSG.Quasithin.H13.F431.F45 CFSG.Quasithin.H13.F431.F45.SpGeom

variable {F : Type} [Field F]

@[expose] def tMat (s r : Fˣ) : Matrix (Fin 4) (Fin 4) F :=
  !![(s : F), 0, 0, 0; 0, (r : F), 0, 0; 0, 0, ((r⁻¹ : Fˣ) : F), 0; 0, 0, 0, ((s⁻¹ : Fˣ) : F)]

theorem tMat_mul (s r s' r' : Fˣ) :
    (tMat s r : Matrix (Fin 4) (Fin 4) F) * tMat s' r' = tMat (s * s') (r * r') := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [tMat, Matrix.mul_apply, Fin.sum_univ_four, mul_comm]

theorem tMat_one : (tMat 1 1 : Matrix (Fin 4) (Fin 4) F) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [tMat]

theorem tMat_mem (s r : Fˣ) : (tMat s r : Matrix (Fin 4) (Fin 4) F)ᵀ * minorJ F * tMat s r =
    minorJ F := by
  ext k j
  rw [transpose_mul_minorJ_mul_apply, minorJ_apply]
  fin_cases k <;> fin_cases j <;> simp [tMat]

@[expose] def tElt (s r : Fˣ) : antiSp F :=
  ⟨⟨tMat s r, tMat s⁻¹ r⁻¹, by rw [tMat_mul, mul_inv_cancel, mul_inv_cancel, tMat_one],
    by rw [tMat_mul, inv_mul_cancel, inv_mul_cancel, tMat_one]⟩, tMat_mem s r⟩

theorem mat_tElt (s r : Fˣ) : mat (tElt s r : antiSp F) = tMat s r := rfl

theorem actLin_tElt_ev (s r : Fˣ) (j : Fin 4) :
    actLin (tElt s r : antiSp F) (ev j) =
      (![(s : F), r, ((r⁻¹ : Fˣ) : F), ((s⁻¹ : Fˣ) : F)] j) • ev j := by
  ext i
  rw [actLin_ev, mat_tElt, Pi.smul_apply, smul_eq_mul]
  fin_cases i <;> fin_cases j <;> simp [tMat, ev_apply]

theorem exists_unit_ne_one [Finite F] (hq : 2 < Nat.card F) : ∃ ω : Fˣ, ω ≠ 1 := by
  have h : 1 < Nat.card Fˣ := by rw [Nat.card_units F]; omega
  have := Finite.one_lt_card_iff_nontrivial.mp h
  exact exists_ne 1

section CharTwo

variable [CharP F 2]

theorem tElt_mul_uElt (s r : Fˣ) (a b c d : F) :
    tElt s r * uElt a b c d =
      uElt ((s : F) * ((r⁻¹ : Fˣ) : F) * a) ((s : F) * r * b) ((s : F) ^ 2 * c) ((r : F) ^ 2 * d) *
        tElt s r := by
  apply antiSp_ext
  show tMat s r * uMat a b c d = uMat _ _ _ _ * tMat s r
  have hs : (s : F) * ((s⁻¹ : Fˣ) : F) = 1 := Units.mul_inv s
  have hr : (r : F) * ((r⁻¹ : Fˣ) : F) = 1 := Units.mul_inv r
  ext i j
  fin_cases i <;> fin_cases j <;> simp [tMat, uMat, Matrix.mul_apply, Fin.sum_univ_four] <;> grind
theorem conj_tElt_uElt (s r : Fˣ) (a b c d : F) :
    tElt s r * uElt a b c d * (tElt s r)⁻¹ =
      uElt ((s : F) * ((r⁻¹ : Fˣ) : F) * a) ((s : F) * r * b) ((s : F) ^ 2 * c)
        ((r : F) ^ 2 * d) := by
  rw [mul_inv_eq_iff_eq_mul]
  exact tElt_mul_uElt s r a b c d

theorem unit_ne_one_sq {ω : Fˣ} (h : ω ≠ 1) : (ω : F) ^ 2 ≠ 1 := by
  intro h2
  apply h
  have h3 : ((ω : F) - 1) ^ 2 = 0 := by
    linear_combination h2 + (1 - (ω : F)) * (CharP.cast_eq_zero F 2)
  exact Units.ext (sub_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp h3))

theorem cent_radA2 {t : Fˣ} (ht : t ≠ 1) {q : antiSp F} (hq : q ∈ radA2 F)
    (hc : tElt t 1 * q * (tElt t 1)⁻¹ = q) : q = 1 := by
  obtain ⟨a, b, c, rfl⟩ := hq
  rw [conj_tElt_uElt] at hc
  obtain ⟨ha, hb, hc2, -⟩ := uElt_inj hc
  have ht1 : (t : F) ≠ 1 := fun h => ht (Units.ext h)
  have ht2 : (t : F) ^ 2 ≠ 1 := unit_ne_one_sq ht
  simp only [inv_one, Units.val_one, mul_one] at ha hb hc2
  have ha0 : a = 0 := by
    have : ((t : F) - 1) * a = 0 := by linear_combination ha
    exact (mul_eq_zero.mp this).resolve_left (sub_ne_zero.mpr ht1)
  have hb0 : b = 0 := by
    have : ((t : F) - 1) * b = 0 := by linear_combination hb
    exact (mul_eq_zero.mp this).resolve_left (sub_ne_zero.mpr ht1)
  have hc0 : c = 0 := by
    have : ((t : F) ^ 2 - 1) * c = 0 := by linear_combination hc2
    exact (mul_eq_zero.mp this).resolve_left (sub_ne_zero.mpr ht2)
  rw [ha0, hb0, hc0]
  exact uElt_zero_eq_one

theorem cent_radA1 {t : Fˣ} (ht : t ≠ 1) {q : antiSp F} (hq : q ∈ radA1 F)
    (hc : tElt t t * q * (tElt t t)⁻¹ = q) : q = 1 := by
  obtain ⟨b, c, d, rfl⟩ := hq
  rw [conj_tElt_uElt] at hc
  obtain ⟨-, hb, hc2, hd⟩ := uElt_inj hc
  have ht2 : (t : F) ^ 2 ≠ 1 := unit_ne_one_sq ht
  have hb0 : b = 0 := by
    have : ((t : F) ^ 2 - 1) * b = 0 := by linear_combination hb
    exact (mul_eq_zero.mp this).resolve_left (sub_ne_zero.mpr ht2)
  have hc0 : c = 0 := by
    have : ((t : F) ^ 2 - 1) * c = 0 := by linear_combination hc2
    exact (mul_eq_zero.mp this).resolve_left (sub_ne_zero.mpr ht2)
  have hd0 : d = 0 := by
    have : ((t : F) ^ 2 - 1) * d = 0 := by linear_combination hd
    exact (mul_eq_zero.mp this).resolve_left (sub_ne_zero.mpr ht2)
  rw [hb0, hc0, hd0]
  exact uElt_zero_eq_one
omit [CharP F 2] in
theorem tElt_smul_epts (s r : Fˣ) (i : Fin 4) : (tElt s r : antiSp F) • (epts i : Pt F) = epts i :=
  smul_pt_eq_of_mem (v := ev i) rfl (by
    rw [actLin_tElt_ev]
    exact Submodule.smul_mem _ _ (mem_mkPt (ev_ne_zero i)))

theorem tElt_smul_eline (s r : Fˣ) {i j : Fin 4} (h : i ≠ j)
    (hb : minorForm F (ev i : W F) (ev j) = 0) :
    (tElt s r : antiSp F) • (eline i j h hb : Ln F) = eline i j h hb :=
  smul_ln_eq_of_le (mapSub_le_of_gens (p₁ := epts i) (p₂ := epts j) (v₁ := ev i) (v₂ := ev j)
    rfl rfl rfl
    (by
      rw [actLin_tElt_ev]
      exact Submodule.smul_mem _ _ (inc_eline_left h hb (mem_mkPt (ev_ne_zero i))))
    (by
      rw [actLin_tElt_ev]
      exact Submodule.smul_mem _ _ (inc_eline_right h hb (mem_mkPt (ev_ne_zero j)))))

theorem dist_pt0_ptStar : (Gr F).dist (Sum.inl (pt0 : Pt F)) (Sum.inl ptStar) = 4 := by
  rw [gqAxioms.dist_inl_inl_eq_four]
  refine ⟨epts_ne (by decide), ?_⟩
  rintro ⟨L, h1, h2⟩
  have := L.2.2 (ev 0) (h1 ev0_mem_pt0) (ev 3) (h2 ev3_mem_ptStar)
  rw [minorForm_apply] at this
  simp [ev_apply] at this

theorem dist_ln0_lnStar : (Gr F).dist (Sum.inr (ln0 : Ln F)) (Sum.inr lnStar) = 4 := by
  rw [gqAxioms.dist_inr_inr_eq_four]
  refine ⟨fun h => ?_, ?_⟩
  · have := (mem_lnStar_iff (ev 0)).mp (h ▸ ev0_mem_ln0)
    simp [ev_apply] at this
  · rintro ⟨p, h1, h2⟩
    obtain ⟨v, hv0, hv⟩ := pt_eq_span p
    have hvp : v ∈ p.1 := hv ▸ Submodule.mem_span_singleton_self v
    obtain ⟨a0, a1⟩ := (mem_ln0_iff v).mp (h1 hvp)
    obtain ⟨b0, b1⟩ := (mem_lnStar_iff v).mp (h2 hvp)
    apply hv0
    ext i
    fin_cases i <;> simp [a0, a1, b0, b1]

theorem exists_cartan_pt [Finite F] (hq : 2 < Nat.card F) :
    ∃ (h : antiSp F) (L₁ L₂ : Ln F) (P : Pt F), inc (pt0 : Pt F) L₁ ∧ inc (pt0 : Pt F) L₂ ∧
      L₁ ≠ L₂ ∧ (Gr F).dist (Sum.inl (pt0 : Pt F)) (Sum.inl P) = 4 ∧ h • (pt0 : Pt F) = pt0 ∧
      h • L₁ = L₁ ∧ h • L₂ = L₂ ∧ h • P = P ∧ ∀ q ∈ radA2 F, h * q * h⁻¹ = q → q = 1 := by
  obtain ⟨t, ht⟩ := exists_unit_ne_one hq
  have e20 : minorForm F (ev 2 : W F) (ev 0) = 0 := by rw [minorForm_apply]; simp [ev]
  have e01 : minorForm F (ev 0 : W F) (ev 1) = 0 := by rw [minorForm_apply]; simp [ev]
  have n21 : minorForm F (ev 2 : W F) (ev 1) ≠ 0 := by rw [minorForm_apply]; simp [ev]
  exact ⟨tElt t 1, ln0, eline 2 0 (by decide) e20, ptStar, inc_pt0_ln0, inc_eline_right _ _,
    (eline_ne (by decide) (by decide) e20 e01 n21).symm, dist_pt0_ptStar, tElt_smul_epts t 1 0,
    tElt_smul_eline t 1 _ _, tElt_smul_eline t 1 _ _, tElt_smul_epts t 1 3,
    fun q hq hc => cent_radA2 ht hq hc⟩

theorem exists_cartan_ln [Finite F] (hq : 2 < Nat.card F) :
    ∃ (h : antiSp F) (P₁ P₂ : Pt F) (L : Ln F), inc P₁ (ln0 : Ln F) ∧ inc P₂ (ln0 : Ln F) ∧
      P₁ ≠ P₂ ∧ (Gr F).dist (Sum.inr (ln0 : Ln F)) (Sum.inr L) = 4 ∧ h • (ln0 : Ln F) = ln0 ∧
      h • P₁ = P₁ ∧ h • P₂ = P₂ ∧ h • L = L ∧ ∀ q ∈ radA1 F, h * q * h⁻¹ = q → q = 1 := by
  obtain ⟨t, ht⟩ := exists_unit_ne_one hq
  exact ⟨tElt t t, epts 0, epts 1, lnStar, inc_pt0_ln0, inc_eline_right _ _,
    epts_ne (by decide), dist_ln0_lnStar, tElt_smul_eline t t _ _, tElt_smul_epts t t 0,
    tElt_smul_epts t t 1, tElt_smul_eline t t _ _, fun q hq hc => cent_radA1 ht hq hc⟩

end CharTwo

end CFSG.Quasithin.H13.F431.F48Sp

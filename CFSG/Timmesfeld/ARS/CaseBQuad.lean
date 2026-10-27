module

public import CFSG.Timmesfeld.ARS.CaseBSlope

public section

namespace CFSG.Timmesfeld.ARS

open scoped commutatorElement Pointwise
open CFSG.LieType.Universal CFSG.LieType.Steinberg Matrix
open CFSG.LieType.Universal.Spin.Twisted

namespace CaseB

variable {G : Type} [Group G] {R : Set (Subgroup G)} {F : Type} [Field F]
  {Ψ : SpecialLinearGroup (Fin 4) F →* G}

section Conj

variable [CharP F 2] (h : Hyp G R) (hS : Skel R Ψ) {e : ℕ} {ι : (Fin e → F) → G}
  (hι : LinParamU R Ψ e ι)
include h hS hι

theorem conj_ι_xs13 (v : Fin e → F) (s : F) :
    ι v * xs Ψ ne13 s * (ι v)⁻¹ =
      xs Ψ ne13 s * xs Ψ ne02 (s * Qc R Ψ (ι v)) * Lc R Ψ (ι (s • v)) := by
  have e := hι.commutator_xs13 h hS s v
  have hN := Lc_mem h hS (hι.mem (s • v))
  have hNN := mul_self_of_mem_hid h hS hN
  have hCC : xs Ψ ne02 (s * Qc R Ψ (ι v)) * xs Ψ ne02 (s * Qc R Ψ (ι v)) = 1 := by
    rw [← xs_add, CharTwo.add_self_eq_zero, xs_zero]
  have hc1 : Commute (xs Ψ ne13 s) (xs Ψ ne02 (s * Qc R Ψ (ι v))) :=
    commuting_xg (Ψ := Ψ) ne13 ne02 (by decide) (by decide) _ (xs_mem _ _) _ (xs_mem _ _)
  have hc2 : Commute (xs Ψ ne13 s) (Lc R Ψ (ι (s • v))) :=
    (commuting_hid_13 h hS _ hN _ (xs_mem _ _)).symm
  have hc3 : Commute (xs Ψ ne02 (s * Qc R Ψ (ι v))) (Lc R Ψ (ι (s • v))) :=
    (commuting_hid_02 h hS _ hN _ (xs_mem _ _)).symm
  calc ι v * xs Ψ ne13 s * (ι v)⁻¹ = (⁅xs Ψ ne13 s, ι v⁆)⁻¹ * xs Ψ ne13 s := by
        rw [commutatorElement_def]
        group
    _ = (Lc R Ψ (ι (s • v)))⁻¹ * (xs Ψ ne02 (s * Qc R Ψ (ι v)))⁻¹ * xs Ψ ne13 s := by
        rw [e]
        group
    _ = Lc R Ψ (ι (s • v)) * xs Ψ ne02 (s * Qc R Ψ (ι v)) * xs Ψ ne13 s := by
        rw [inv_eq_of_mul_eq_one_left hNN, inv_eq_of_mul_eq_one_left hCC]
    _ = xs Ψ ne13 s * xs Ψ ne02 (s * Qc R Ψ (ι v)) * Lc R Ψ (ι (s • v)) := by
        rw [mul_assoc, ((hc3.symm).mul_right hc2.symm).eq, ← hc1.eq]

theorem conjSub_conj_ι_piT (hP : PtHyp R Ψ) {v : Fin e → F} (hv : v ≠ 0) :
    conjSub (conjSub (xg Ψ 1 3) (ι v)) (piT Ψ) =
      conjSub (xg Ψ 1 3) (ι ((Qc R Ψ (ι v))⁻¹ • v)) := by
  have hQ : Qc R Ψ (ι v) ≠ 0 := fun h0 => hv (hι.eq_zero_of_Qc h hS hP h0)
  set w := (Qc R Ψ (ι v))⁻¹ • v with hw
  have hQw : Qc R Ψ (ι w) = (Qc R Ψ (ι v))⁻¹ := by
    rw [hw, hι.Qc_smul h hS]
    field_simp
  have key : ∀ s : F, piT Ψ * (ι v * xs Ψ ne13 s * (ι v)⁻¹) * (piT Ψ)⁻¹ =
      ι w * xs Ψ ne13 (s * Qc R Ψ (ι v)) * (ι w)⁻¹ := by
    intro s
    rw [conj_ι_xs13 h hS hι, conj_ι_xs13 h hS hι]
    have hN := Lc_mem h hS (hι.mem (s • v))
    have e1 : piT Ψ * (xs Ψ ne13 s * xs Ψ ne02 (s * Qc R Ψ (ι v)) * Lc R Ψ (ι (s • v))) *
        (piT Ψ)⁻¹ = (piT Ψ * xs Ψ ne13 s * (piT Ψ)⁻¹) *
          (piT Ψ * xs Ψ ne02 (s * Qc R Ψ (ι v)) * (piT Ψ)⁻¹) *
          (piT Ψ * Lc R Ψ (ι (s • v)) * (piT Ψ)⁻¹) := by group
    rw [e1, piT_conj_xs13, piT_conj_xs02, piT_conj_hid h hS hN, hQw]
    have e2 : s * Qc R Ψ (ι v) * (Qc R Ψ (ι v))⁻¹ = s := by field_simp
    have e3 : (s * Qc R Ψ (ι v)) • w = s • v := by
      rw [hw, smul_smul, mul_assoc, mul_inv_cancel₀ hQ, mul_one]
    rw [e2, e3]
    have hc : Commute (xs Ψ ne02 s) (xs Ψ ne13 (s * Qc R Ψ (ι v))) :=
      commuting_xg (Ψ := Ψ) ne02 ne13 (by decide) (by decide) _ (xs_mem _ _) _ (xs_mem _ _)
    rw [hc.eq]
  ext g
  constructor
  · rintro ⟨_, ⟨c, hc, rfl⟩, rfl⟩
    obtain ⟨s, rfl⟩ := (mem_xg_iff ne13).1 hc
    change piT Ψ * (ι v * xs Ψ ne13 s * (ι v)⁻¹) * (piT Ψ)⁻¹ ∈ _
    rw [key]
    exact conj_mem_conjSub _ (xs_mem _ _)
  · rintro ⟨c, hc, rfl⟩
    obtain ⟨s, rfl⟩ := (mem_xg_iff ne13).1 hc
    refine ⟨ι v * xs Ψ ne13 (s * (Qc R Ψ (ι v))⁻¹) * (ι v)⁻¹, conj_mem_conjSub _ (xs_mem _ _), ?_⟩
    change piT Ψ * (ι v * xs Ψ ne13 (s * (Qc R Ψ (ι v))⁻¹) * (ι v)⁻¹) * (piT Ψ)⁻¹ = _
    rw [key, show s * (Qc R Ψ (ι v))⁻¹ * Qc R Ψ (ι v) = s by field_simp]
    rfl

end Conj

section Norm

@[expose] def scaleFst (l : F) (p : Fin 2 → F) : Fin 2 → F := ![l * p 0, p 1]

theorem scaleFst_add (l : F) (p q : Fin 2 → F) :
    scaleFst l (p + q) = scaleFst l p + scaleFst l q := by
  ext k
  fin_cases k <;> simp [scaleFst, mul_add]

theorem scaleFst_smul (l r : F) (p : Fin 2 → F) : scaleFst l (r • p) = r • scaleFst l p := by
  ext k
  fin_cases k <;> simp [scaleFst]
  ring

theorem scaleFst_scaleFst_inv {l : F} (hl : l ≠ 0) (p : Fin 2 → F) :
    scaleFst l (scaleFst l⁻¹ p) = p := by
  ext k
  fin_cases k <;> simp [scaleFst, hl]

theorem scaleFst_injective {l : F} (hl : l ≠ 0) : Function.Injective (scaleFst l) := by
  intro p q e
  ext k
  have := congrFun e k
  fin_cases k <;> simp [scaleFst, hl] at this ⊢ <;> exact this

variable [CharP F 2] (h : Hyp G R) (hS : Skel R Ψ) {ι : (Fin 2 → F) → G}
  (hι : LinParamU R Ψ 2 ι)
include h hS hι

omit [CharP F 2] h hS in
theorem LinParamU.scaleFst {l : F} (hl : l ≠ 0) :
    LinParamU R Ψ 2 (fun p => ι (scaleFst l p)) where
  add v w := by
    rw [← hι.add, scaleFst_add]
  inj v w e := scaleFst_injective hl (hι.inj e)
  mem v := hι.mem _
  surj u hu := by
    obtain ⟨v, rfl⟩ := hι.surj u hu
    exact ⟨_root_.CFSG.Timmesfeld.ARS.CaseB.scaleFst l⁻¹ v, by
      simp only [scaleFst_scaleFst_inv hl]⟩
  smul c v := by
    rw [hι.smul, scaleFst_smul]

theorem LinParamU.Qc_expand (p : Fin 2 → F) :
    Qc R Ψ (ι p) = p 0 ^ 2 * Qc R Ψ (ι ![1, 0]) +
      p 0 * p 1 * βU R Ψ ι ![1, 0] ![0, 1] + p 1 ^ 2 * Qc R Ψ (ι ![0, 1]) := by
  have hp : p = p 0 • (![1, 0] : Fin 2 → F) + p 1 • ![0, 1] := by
    ext k
    fin_cases k <;> simp
  conv_lhs => rw [hp]
  rw [LinParamU.Qc_add (R := R) (Ψ := Ψ) (ι := ι), hι.Qc_smul h hS, hι.Qc_smul h hS,
    hι.βU_smul_left h hS, hι.βU_smul_right h hS]
  ring

omit [CharP F 2] h hS hι in
theorem βU_eq_polarPlane {b c : F} (hQ : ∀ p, Qc R Ψ (ι p) = planeNorm b c p)
    (v w : Fin 2 → F) : βU R Ψ ι v w = polarPlane b c v w := by
  rw [βU, hQ, hQ, hQ]
  simp only [planeNorm, polarPlane, Pi.add_apply]
  ring

theorem exists_normParam [Finite F] (hP : PtHyp R Ψ) :
    ∃ (b c : F) (ι' : (Fin 2 → F) → G), LinParamU R Ψ 2 ι' ∧
      (∀ p, Qc R Ψ (ι' p) = planeNorm b c p) ∧ ∀ s : F, s ^ 2 + b * s + c ≠ 0 := by
  have hq0 : Qc R Ψ (ι ![1, 0]) ≠ 0 := fun h0 => by
    have h1 := congrFun (hι.eq_zero_of_Qc h hS hP h0) 0
    simp at h1
  set l := sqrtF F (Qc R Ψ (ι ![1, 0]))⁻¹ with hl
  have hl2 : l ^ 2 = (Qc R Ψ (ι ![1, 0]))⁻¹ := sqrtF_sq _
  have hl0 : l ≠ 0 := fun h0 => by
    rw [h0, zero_pow two_ne_zero] at hl2
    exact inv_ne_zero hq0 hl2.symm
  have hι' := hι.scaleFst hl0
  have h10 : Qc R Ψ (ι (scaleFst l ![1, 0])) = 1 := by
    rw [show scaleFst l ![1, 0] = l • (![1, 0] : Fin 2 → F) by
        ext k
        fin_cases k <;> simp [scaleFst],
      hι.Qc_smul h hS, hl2, inv_mul_cancel₀ hq0]
  refine ⟨βU R Ψ (fun p => ι (scaleFst l p)) ![1, 0] ![0, 1],
    Qc R Ψ (ι (scaleFst l ![0, 1])), fun p => ι (scaleFst l p), hι', fun p => ?_, fun s hs => ?_⟩
  · rw [hι'.Qc_expand h hS p, planeNorm, h10]
    ring
  · have e := hι'.eq_zero_of_Qc h hS hP (v := ![s, 1]) (by
      rw [hι'.Qc_expand h hS, h10]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
      linear_combination hs)
    have := congrFun e 1
    simp at this

end Norm

section ShortField

variable {b c : F}

theorem neg_eq_shortField [CharP F 2] (x : ShortField b c) : -x = x :=
  QuadraticAlgebra.ext (CharTwo.neg_eq _) (CharTwo.neg_eq _)

theorem add_self_shortField [CharP F 2] (x : ShortField b c) : x + x = 0 := by
  nth_rw 1 [← neg_eq_shortField x]
  exact neg_add_cancel x

theorem starCoord_eq_fieldCoord (t : ShortField b c) : starCoord t = fieldCoord (-star t) := by
  ext k
  fin_cases k <;> simp [starCoord, fieldCoord]

theorem fieldCoord_star_inv [Fact (∀ r : F, r ^ 2 ≠ -c + b * r)] (t : ShortField b c) :
    fieldCoord ((star t)⁻¹) = (planeNorm b c (fieldCoord t))⁻¹ • fieldCoord t := by
  rw [← starCoord_neg_inv, starCoord_eq_fieldCoord, star_neg, star_inv₀, neg_neg]

variable (Ψ) in
@[expose] noncomputable def yE [CharP F 2] (ι : (Fin 2 → F) → G) (t : ShortField b c) : G :=
  piT Ψ * ι (starCoord t) * (piT Ψ)⁻¹

variable (Ψ) in
noncomputable abbrev ptE (ι : (Fin 2 → F) → G) (t : ShortField b c) : Subgroup G :=
  conjSub (xg Ψ 1 3) (ι (fieldCoord t))

variable [CharP F 2] [Fact (∀ r : F, r ^ 2 ≠ -c + b * r)] (h : Hyp G R)
  (hS : Skel R Ψ) (hP : PtHyp R Ψ) {ι : (Fin 2 → F) → G} (hι : LinParamU R Ψ 2 ι)
  (hQ : ∀ p, Qc R Ψ (ι p) = planeNorm b c p)
include h hS hP hι hQ

omit [CharP F 2] [Fact (∀ r : F, r ^ 2 ≠ -c + b * r)] h hS hP hQ in
theorem xE_add (s t : ShortField b c) :
    ι (fieldCoord (s + t)) = ι (fieldCoord s) * ι (fieldCoord t) := by
  rw [fieldCoord_add, hι.add]

omit [CharP F 2] [Fact (∀ r : F, r ^ 2 ≠ -c + b * r)] h hS hP hQ in
theorem xE_zero : ι (fieldCoord (0 : ShortField b c)) = 1 := by
  rw [show fieldCoord (0 : ShortField b c) = 0 by ext k; fin_cases k <;> rfl, hι.map_zero]

omit [Fact (∀ r : F, r ^ 2 ≠ -c + b * r)] h hS hP hQ in
theorem yE_add (s t : ShortField b c) : yE Ψ ι (s + t) = yE Ψ ι s * yE Ψ ι t := by
  rw [yE, yE, yE, starCoord_add, hι.add]
  group

omit [Fact (∀ r : F, r ^ 2 ≠ -c + b * r)] h hS hP hQ in
theorem yE_zero : yE Ψ ι (0 : ShortField b c) = 1 := by
  rw [yE, show starCoord (0 : ShortField b c) = 0 by ext k; fin_cases k <;> simp [starCoord],
    hι.map_zero]
  group

omit [Fact (∀ r : F, r ^ 2 ≠ -c + b * r)] hS hP hQ in
theorem yE_mem (t : ShortField b c) : yE Ψ ι t ∈ hU R (perm Ψ σT) := by
  rw [hU_perm_T' h]
  exact conj_mem_conjSub _ (hι.mem _)

omit [Fact (∀ r : F, r ^ 2 ≠ -c + b * r)] h hS hP hQ in
theorem xE_mul_self (t : ShortField b c) : ι (fieldCoord t) * ι (fieldCoord t) = 1 := by
  rw [← xE_add hι, add_self_shortField, xE_zero hι]

omit [Fact (∀ r : F, r ^ 2 ≠ -c + b * r)] h hS hP hQ in
theorem yE_mul_self (t : ShortField b c) : yE Ψ ι t * yE Ψ ι t = 1 := by
  rw [← yE_add hι, add_self_shortField, yE_zero hι]

omit [CharP F 2] [Fact (∀ r : F, r ^ 2 ≠ -c + b * r)] h hS hP hQ in
theorem ptE_zero : ptE Ψ ι (0 : ShortField b c) = xg Ψ 1 3 := by
  rw [ptE, xE_zero hι, conjSub_one]

omit [CharP F 2] [Fact (∀ r : F, r ^ 2 ≠ -c + b * r)] h hS hP hQ in
theorem conjSub_ptE_xE (s t : ShortField b c) :
    conjSub (ptE Ψ ι s) (ι (fieldCoord t)) = ptE Ψ ι (s + t) := by
  rw [ptE, ← conjSub_mul, ← xE_add hι, add_comm]

omit [CharP F 2] [Fact (∀ r : F, r ^ 2 ≠ -c + b * r)] hP hQ in
theorem conjSub_02_xE (t : ShortField b c) :
    conjSub (xg Ψ 0 2) (ι (fieldCoord t)) = xg Ψ 0 2 :=
  conjSub_02_hU h hS (hι.mem _)

theorem conjSub_ptE_piT {s : ShortField b c} (hs : s ≠ 0) :
    conjSub (ptE Ψ ι s) (piT Ψ) = ptE Ψ ι ((star s)⁻¹) := by
  rw [ptE, ptE, conjSub_conj_ι_piT h hS hι hP (fieldCoord_ne_zero hs), hQ, fieldCoord_star_inv]

omit [Fact (∀ r : F, r ^ 2 ≠ -c + b * r)] h hS hP hι hQ in
theorem conjSub_yE (H : Subgroup G) (t : ShortField b c) :
    conjSub H (yE Ψ ι t) =
      conjSub (conjSub (conjSub H (piT Ψ)) (ι (fieldCoord (-star t)))) (piT Ψ) := by
  rw [yE, piT_inv, ← conjSub_mul, ← conjSub_mul, starCoord_eq_fieldCoord]

theorem conjSub_02_yE {t : ShortField b c} (ht : t ≠ 0) :
    conjSub (xg Ψ 0 2) (yE Ψ ι t) = ptE Ψ ι (-t⁻¹) := by
  have hs : -star t ≠ 0 := neg_ne_zero.2 ((star_ne_zero (x := t)).2 ht)
  rw [conjSub_yE, conjSub_02_piT, ← ptE_zero (b := b) (c := c) hι, conjSub_ptE_xE hι, zero_add,
    conjSub_ptE_piT h hS hP hι hQ hs, star_neg, star_star, inv_neg]

omit [Fact (∀ r : F, r ^ 2 ≠ -c + b * r)] hP hQ in
theorem conjSub_ptE0_yE (t : ShortField b c) :
    conjSub (ptE Ψ ι (0 : ShortField b c)) (yE Ψ ι t) = ptE Ψ ι (0 : ShortField b c) := by
  rw [conjSub_yE, ptE_zero hι, conjSub_13_piT, conjSub_02_xE h hS hι, conjSub_02_piT]

theorem conjSub_ptE_yE {a t : ShortField b c} (ha : a ≠ 0) (hat : a⁻¹ - t ≠ 0) :
    conjSub (ptE Ψ ι a) (yE Ψ ι t) = ptE Ψ ι ((a⁻¹ - t)⁻¹) := by
  have h1 : (star a)⁻¹ + -star t ≠ 0 := by
    rw [← star_inv₀, ← star_neg, ← star_add]
    rw [← sub_eq_add_neg]
    exact (star_ne_zero (x := a⁻¹ - t)).2 hat
  rw [conjSub_yE, conjSub_ptE_piT h hS hP hι hQ ha, conjSub_ptE_xE hι,
    conjSub_ptE_piT h hS hP hι hQ h1, star_add, star_inv₀, star_star, star_neg, star_star,
    ← sub_eq_add_neg]

theorem conjSub_ptE_yE_eq {a t : ShortField b c} (ha : a ≠ 0) (hat : a⁻¹ - t = 0) :
    conjSub (ptE Ψ ι a) (yE Ψ ι t) = xg Ψ 0 2 := by
  have h1 : (star a)⁻¹ + -star t = 0 := by
    rw [← star_inv₀, ← star_neg, ← star_add, ← sub_eq_add_neg, hat, star_zero]
  rw [conjSub_yE, conjSub_ptE_piT h hS hP hι hQ ha, conjSub_ptE_xE hι, h1, ptE_zero hι,
    conjSub_13_piT]

theorem rankOneE_conj {t : ShortField b c} (ht : t ≠ 0) (a : ShortField b c) :
    ι (fieldCoord t) * yE Ψ ι (-t⁻¹) * ι (fieldCoord t) * ι (fieldCoord a) *
        (ι (fieldCoord t) * yE Ψ ι (-t⁻¹) * ι (fieldCoord t))⁻¹ =
      yE Ψ ι (-(t ^ 2)⁻¹ * a) := by
  have hR := h.root
  set w := ι (fieldCoord t) * yE Ψ ι (-t⁻¹) * ι (fieldCoord t) with hw
  by_cases ha : a = 0
  · subst ha
    rw [xE_zero hι, mul_zero, yE_zero hι]
    group
  have hneg : ∀ x : ShortField b c, -x = x := neg_eq_shortField
  have hs : -t⁻¹ ≠ 0 := neg_ne_zero.2 (inv_ne_zero ht)
  have hwinv : w⁻¹ = w := by
    rw [hw, _root_.mul_inv_rev, _root_.mul_inv_rev, inv_eq_of_mul_eq_one_left (xE_mul_self hι t),
      inv_eq_of_mul_eq_one_left (yE_mul_self hι _)]
    group
  have hwC : conjSub (xg Ψ 0 2) w = ptE Ψ ι (0 : ShortField b c) := by
    rw [hw, conjSub_mul, conjSub_mul, conjSub_02_xE h hS hι, conjSub_02_yE h hS hP hι hQ hs,
      conjSub_ptE_xE hι, inv_neg, inv_inv, neg_neg, add_self_shortField]
  have hwD : conjSub (ptE Ψ ι a) w = ptE Ψ ι (t ^ 2 / a) := by
    rw [hw, conjSub_mul, conjSub_mul, conjSub_ptE_xE hι]
    by_cases hat : a + t = 0
    · have hat' : a = t := by
        have := eq_neg_of_add_eq_zero_left hat
        rwa [hneg] at this
      rw [hat, conjSub_ptE0_yE h hS hι, conjSub_ptE_xE hι, zero_add, hat', pow_two,
        mul_div_cancel_right₀ _ ht]
    · have e1 : (a + t)⁻¹ - -t⁻¹ = a * ((a + t) * t)⁻¹ := by
        rw [hneg, sub_eq_add_neg, hneg]
        field_simp
        linear_combination (add_self_shortField t)
      have h1 : (a + t)⁻¹ - -t⁻¹ ≠ 0 := by
        rw [e1]
        exact mul_ne_zero ha (inv_ne_zero (mul_ne_zero hat ht))
      rw [conjSub_ptE_yE h hS hP hι hQ hat h1, conjSub_ptE_xE hι]
      congr 1
      rw [e1]
      field_simp
      linear_combination a * (add_self_shortField (1 : ShortField b c))
  have hST := hS.perm σT
  have hPT := hP.perm hR σT
  have hU'1 : w * ι (fieldCoord a) * w⁻¹ ∈ hU R (perm Ψ σT) := by
    have hwc : w ∈ cent4 Ψ := by
      have h1 : ι (fieldCoord t) ∈ cent4 Ψ := hU_le_cent4 h hS (hι.mem _)
      have h2 : yE Ψ ι (-t⁻¹) ∈ cent4 Ψ := by
        rw [← cent4_perm_T]
        exact hU_le_cent4 h hST (yE_mem h hι _)
      exact Subgroup.mul_mem _ (Subgroup.mul_mem _ h1 h2) h1
    have hmem : w * ι (fieldCoord a) * w⁻¹ ∈ conjSub (hU R Ψ) w :=
      conj_mem_conjSub w (hι.mem _)
    rw [hU_eq_cent4_inf h hS hP, conjSub_inf, conjSub_of_mem hwc, Sec5.conjSub_M hR, hwC,
      ptE_zero hι] at hmem
    rw [hU_eq_cent4_inf h hST hPT, cent4_perm_T, xg_perm,
      show σT 0 = 1 from by decide, show σT 2 = 3 from by decide]
    exact hmem
  have hr : -(t ^ 2)⁻¹ * a ≠ 0 :=
    mul_ne_zero (neg_ne_zero.2 (inv_ne_zero (pow_ne_zero 2 ht))) ha
  have hL : conjSub (xg Ψ 0 2) (w * ι (fieldCoord a) * w⁻¹) = ptE Ψ ι (t ^ 2 / a) := by
    rw [conjSub_mul, conjSub_mul, hwinv, hwC, conjSub_ptE_xE hι, zero_add, hwD]
  have hRC : conjSub (xg Ψ 0 2) (yE Ψ ι (-(t ^ 2)⁻¹ * a)) = ptE Ψ ι (t ^ 2 / a) := by
    rw [conjSub_02_yE h hS hP hι hQ hr]
    congr 1
    rw [hneg, hneg, mul_inv, inv_inv, div_eq_mul_inv, mul_comm]
  set g := (yE Ψ ι (-(t ^ 2)⁻¹ * a))⁻¹ * (w * ι (fieldCoord a) * w⁻¹) with hg
  have hgU : g ∈ hU R (perm Ψ σT) :=
    Subgroup.mul_mem _ (Subgroup.inv_mem _ (yE_mem h hι _)) hU'1
  have hgC : conjSub (xg Ψ 0 2) g = xg Ψ 0 2 := by
    rw [hg, conjSub_mul, hL, ← hRC, ← conjSub_mul, inv_mul_cancel, conjSub_one]
  have hOm : xg Ψ 0 2 ∈ Om R (perm Ψ σT) := by
    rw [Om_perm, show σT 0 = 1 from by decide, show σT 1 = 0 from by decide,
      show σT 2 = 3 from by decide, show σT 3 = 2 from by decide, Set.inter_comm]
    exact mem_Om_02 h hS
  have hne : xg Ψ 0 2 ≠ xg (perm Ψ σT) 0 2 := by
    rw [xg_perm, show σT 0 = 1 from by decide, show σT 2 = 3 from by decide]
    exact hS.xg_ne ne02 ne13 (by decide)
  have h1 := eq_one_of_conjSub_eq h hST hPT hgU hOm hne hgC
  rw [hg, inv_mul_eq_one] at h1
  exact h1.symm

variable (Ψ) in
noncomputable def rankOneRelsE : RankOneRels G (ShortField b c) where
  x t := ι (fieldCoord t)
  y := yE Ψ ι
  x_add := xE_add hι
  y_add := yE_add hι
  conj_x _ ht a := rankOneE_conj h hS hP hι hQ ht a

theorem exists_hom_SL2_xE [Finite F] :
    ∃ Θ : @SpecialLinearGroup (Fin 2) _ _ (ShortField b c)
        (@Field.toCommRing (ShortField b c) inferInstance) →* G,
      (∀ t, Θ (sl2Upper t) = ι (fieldCoord t)) ∧ ∀ t, Θ (sl2Lower t) = yE Ψ ι t := by
  have := finite_shortField (b := b) (c := c)
  exact RankTwo.exists_hom_of_rankOneRels (rankOneRelsE Ψ h hS hP hι hQ)

end ShortField

end CaseB

end CFSG.Timmesfeld.ARS

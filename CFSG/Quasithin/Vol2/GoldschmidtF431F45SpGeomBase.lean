module

public import CFSG.Quasithin.Vol2.GoldschmidtF431F45SpGeomAx
public import CFSG.Quasithin.Vol2.GoldschmidtF431F45Transfer
public import CFSG.RankThree.PartOne.KC.EvenSymplecticFourRootAxisNormalizer

public section

namespace CFSG.Quasithin.H13.F431.F45

open Matrix CFSG.ComponentClassification.UnbalancedCatalog.SpChain
  CFSG.QuasithinUnique.Setup.X7b CFSG.RankThree.PartOne.KCRootAxis CFSG.Quasithin

namespace SpGeom

variable {F : Type} [Field F] [CharP F 2]

theorem actLin_uElt (a b c d : F) (x : W F) :
    actLin (uElt a b c d) x = ![x 0 + a * x 1 + b * x 2 + c * x 3,
      x 1 + d * x 2 + (b + a * d) * x 3, x 2 + a * x 3, x 3] := by
  ext i
  fin_cases i <;>
    simp [actLin_apply, mat, glMat_uElt, uMat, Matrix.mulVec, dotProduct, Fin.sum_univ_four]

omit [CharP F 2] in
theorem actLin_ev (g : antiSp F) (j i : Fin 4) : actLin g (ev j) i = mat g i j := by
  rw [actLin_apply, ev, Matrix.mulVec_single_one]
  rfl

omit [CharP F 2] in
theorem ev_apply (i j : Fin 4) : (ev i : W F) j = if j = i then 1 else 0 := by
  simp [ev, Pi.single_apply]

section Basic

@[expose] def pt0 : Pt F := epts 0

@[expose] def ptStar : Pt F := epts 3

@[expose] def ln0 : Ln F :=
  eline 0 1 (by decide) (by rw [minorForm_apply]; simp [ev])

@[expose] def lnStar : Ln F :=
  eline 2 3 (by decide) (by rw [minorForm_apply]; simp [ev])

theorem inc_pt0_ln0 : inc (pt0 : Pt F) ln0 := inc_eline_left _ _

omit [CharP F 2] in
theorem ev0_mem_pt0 : (ev 0 : W F) ∈ (pt0 : Pt F).1 := mem_mkPt (ev_ne_zero 0)

omit [CharP F 2] in
theorem ev3_mem_ptStar : (ev 3 : W F) ∈ (ptStar : Pt F).1 := mem_mkPt (ev_ne_zero 3)

theorem mem_ln0_iff (v : W F) : v ∈ (ln0 : Ln F).1 ↔ v 2 = 0 ∧ v 3 = 0 := by
  constructor
  · intro hv
    obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.mp hv
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hy
    obtain ⟨d, rfl⟩ := Submodule.mem_span_singleton.mp hz
    simp [ev]
  · rintro ⟨h2, h3⟩
    refine Submodule.mem_sup.mpr ⟨v 0 • ev 0,
      Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _), v 1 • ev 1,
      Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _), ?_⟩
    ext i
    fin_cases i <;> simp [ev, h2, h3]

theorem mem_lnStar_iff (v : W F) : v ∈ (lnStar : Ln F).1 ↔ v 0 = 0 ∧ v 1 = 0 := by
  constructor
  · intro hv
    obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.mp hv
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hy
    obtain ⟨d, rfl⟩ := Submodule.mem_span_singleton.mp hz
    simp [ev]
  · rintro ⟨h0, h1⟩
    refine Submodule.mem_sup.mpr ⟨v 2 • ev 2,
      Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _), v 3 • ev 3,
      Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _), ?_⟩
    ext i
    fin_cases i <;> simp [ev, h0, h1]

omit [CharP F 2] in
theorem smul_pt_eq_of_le {y : antiSp F} {p : Pt F} (h : mapSub y p.1 ≤ p.1) : y • p = p := by
  apply Subtype.ext
  show mapSub y p.1 = p.1
  exact Submodule.eq_of_le_of_finrank_eq h (by rw [finrank_mapSub])

omit [CharP F 2] in
theorem smul_pt_eq_of_mem {y : antiSp F} {p p' : Pt F} {v : W F} (hp : p.1 = Submodule.span F {v})
    (h : actLin y v ∈ p'.1) : y • p = p' := by
  apply Subtype.ext
  show mapSub y p.1 = p'.1
  have hle : mapSub y p.1 ≤ p'.1 := by
    show Submodule.map (actLin y) p.1 ≤ p'.1
    rw [hp, Submodule.map_span, Submodule.span_le]
    simpa using h
  exact Submodule.eq_of_le_of_finrank_eq hle (by rw [finrank_mapSub, p.2, p'.2])

omit [CharP F 2] in
theorem smul_ln_eq_of_le {y : antiSp F} {L L' : Ln F} (h : mapSub y L.1 ≤ L'.1) : y • L = L' := by
  apply Subtype.ext
  show mapSub y L.1 = L'.1
  exact Submodule.eq_of_le_of_finrank_eq h (by rw [finrank_mapSub, L.2.1, L'.2.1])

end Basic

section Points

omit [CharP F 2] in
theorem firstCol_iff (y : antiSp F) :
    actLin y (ev 0) ∈ Submodule.span F {(ev 0 : W F)} ↔ FirstCol y := by
  constructor
  · intro h
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp h
    have e1 := congrFun hc 1
    have e2 := congrFun hc 2
    have e3 := congrFun hc 3
    simp [ev_apply, actLin_ev] at e1 e2 e3
    exact ⟨e1.symm, e2.symm, e3.symm⟩
  · rintro ⟨h1, h2, h3⟩
    refine Submodule.mem_span_singleton.mpr ⟨mat y 0 0, ?_⟩
    ext i
    fin_cases i <;> simp [ev_apply, actLin_ev, h1, h2, h3]

theorem stab_pt0_iff (y : antiSp F) :
    y • (pt0 : Pt F) = pt0 ↔ y ∈ Subgroup.normalizer (radA2 F : Set (antiSp F)) := by
  rw [mem_normalizer_radA2_iff]
  constructor
  · intro h
    have hm : mapSub y (pt0 : Pt F).1 = (pt0 : Pt F).1 := congrArg Subtype.val h
    have : actLin y (ev 0) ∈ (pt0 : Pt F).1 := by
      rw [← hm]
      exact Submodule.mem_map_of_mem ev0_mem_pt0
    exact (firstCol_iff y).mp this
  · intro h
    exact smul_pt_eq_of_mem (v := ev 0) rfl ((firstCol_iff y).mpr h)

theorem qfix_pt0 {q : antiSp F} (hq : q ∈ radA2 F) {L : Ln F} (hL : inc (pt0 : Pt F) L) :
    q • L = L := by
  obtain ⟨a, b, c, rfl⟩ := hq
  apply smul_ln_eq_of_le
  intro y hy
  obtain ⟨x, hx, rfl⟩ := mem_mapSub.mp hy
  have e0 : (ev 0 : W F) ∈ L.1 := hL ev0_mem_pt0
  have hx3 : x 3 = 0 := by
    have := L.2.2 (ev 0) e0 x hx
    rw [minorForm_apply] at this
    simpa [ev] using this
  have h : actLin (uElt a b c 0) x = x + (a * x 1 + b * x 2) • ev 0 := by
    ext i
    fin_cases i <;> simp [actLin_uElt, ev, hx3, add_assoc]
  rw [h]
  exact L.1.add_mem hx (L.1.smul_mem _ e0)

theorem opp_pt_gen {p : Pt F} (h : (Gr F).dist (Sum.inl pt0) (Sum.inl p) = 4) :
    ∃ x : W F, p.1 = Submodule.span F {x} ∧ x 3 ≠ 0 := by
  obtain ⟨x, hx0, hx⟩ := pt_eq_span p
  refine ⟨x, hx, fun hx3 => ?_⟩
  obtain ⟨hne, hno⟩ := (gqAxioms.dist_inl_inl_eq_four (pt0 : Pt F) p).mp h
  apply hno
  have hperp : ∀ u ∈ (pt0 : Pt F).1, ∀ v ∈ p.1, minorForm F u v = 0 :=
    perp_of_gen (u := ev 0) (v := x) (by rw [minorForm_apply]; simpa [ev] using hx3) pt0 p rfl hx
  exact ⟨mkLine pt0 p hne hperp, inc_mkLine_left _ _ _ _, inc_mkLine_right _ _ _ _⟩

theorem exists_radA2_smul_ptStar {p : Pt F} {x : W F} (hx : p.1 = Submodule.span F {x})
    (hx3 : x 3 ≠ 0) : ∃ q ∈ radA2 F, q • (ptStar : Pt F) = p := by
  refine ⟨uElt (x 2 / x 3) (x 1 / x 3) (x 0 / x 3) 0, ⟨_, _, _, rfl⟩, ?_⟩
  refine smul_pt_eq_of_mem (v := ev 3) rfl ?_
  have h : actLin (uElt (x 2 / x 3) (x 1 / x 3) (x 0 / x 3) 0) (ev 3) = (x 3)⁻¹ • x := by
    ext i
    fin_cases i <;> simp [actLin_uElt, ev, hx3, div_eq_inv_mul]
  rw [h, hx]
  exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self x)

theorem radA2_trans {p p' : Pt F} (h : (Gr F).dist (Sum.inl pt0) (Sum.inl p) = 4)
    (h' : (Gr F).dist (Sum.inl pt0) (Sum.inl p') = 4) : ∃ q ∈ radA2 F, q • p = p' := by
  obtain ⟨x, hx, hx3⟩ := opp_pt_gen h
  obtain ⟨x', hx', hx3'⟩ := opp_pt_gen h'
  obtain ⟨q₁, hq₁, e₁⟩ := exists_radA2_smul_ptStar hx hx3
  obtain ⟨q₂, hq₂, e₂⟩ := exists_radA2_smul_ptStar hx' hx3'
  refine ⟨q₂ * q₁⁻¹, (radA2 F).mul_mem hq₂ ((radA2 F).inv_mem hq₁), ?_⟩
  rw [mul_smul, ← e₁, inv_smul_smul, e₂]

theorem radA2_free {q : antiSp F} (hq : q ∈ radA2 F) {p : Pt F}
    (h : (Gr F).dist (Sum.inl pt0) (Sum.inl p) = 4) (hqp : q • p = p) : q = 1 := by
  obtain ⟨x, hx, hx3⟩ := opp_pt_gen h
  obtain ⟨a, b, c, rfl⟩ := hq
  have hmem : actLin (uElt a b c 0) x ∈ Submodule.span F {x} := by
    rw [← hx]
    have hm : mapSub (uElt a b c 0) p.1 = p.1 := congrArg Subtype.val hqp
    rw [← hm]
    exact Submodule.mem_map_of_mem (hx ▸ Submodule.mem_span_singleton_self x)
  obtain ⟨l, hl⟩ := Submodule.mem_span_singleton.mp hmem
  have e0 := congrFun hl 0
  have e1 := congrFun hl 1
  have e2 := congrFun hl 2
  have e3 := congrFun hl 3
  simp [actLin_uElt] at e0 e1 e2 e3
  have hl1 : l = 1 := by
    have : l * x 3 = 1 * x 3 := by rw [e3, one_mul]
    exact mul_right_cancel₀ hx3 this
  subst hl1
  have hb : b = 0 := by
    have : b * x 3 = 0 := by linear_combination (-1 : F) * e1
    exact (mul_eq_zero.mp this).resolve_right hx3
  have ha : a = 0 := by
    have : a * x 3 = 0 := by linear_combination (-1 : F) * e2
    exact (mul_eq_zero.mp this).resolve_right hx3
  subst hb
  subst ha
  have hc : c = 0 := by
    have : c * x 3 = 0 := by linear_combination (-1 : F) * e0
    exact (mul_eq_zero.mp this).resolve_right hx3
  subst hc
  exact uElt_zero_eq_one

end Points

section Levi

open CFSG.RankThree.PartOne.KCRootAxis

omit [CharP F 2] in
theorem sl2_two_trans (w₁ w₂ w₁' w₂' z₁ z₂ z₁' z₂' : F) (hΔ : w₁ * w₂' - w₂ * w₁' ≠ 0)
    (hΔz : z₁ * z₂' - z₂ * z₁' ≠ 0) :
    ∃ (N : Matrix.SpecialLinearGroup (Fin 2) F) (κ : F), κ ≠ 0 ∧
      N 0 0 * w₁ + N 0 1 * w₂ = z₁ ∧ N 1 0 * w₁ + N 1 1 * w₂ = z₂ ∧
      N 0 0 * w₁' + N 0 1 * w₂' = κ * z₁' ∧ N 1 0 * w₁' + N 1 1 * w₂' = κ * z₂' := by
  obtain ⟨Δ, hΔd⟩ : ∃ Δ : F, Δ = w₁ * w₂' - w₂ * w₁' := ⟨_, rfl⟩
  obtain ⟨Δz, hΔzd⟩ : ∃ Δz : F, Δz = z₁ * z₂' - z₂ * z₁' := ⟨_, rfl⟩
  have hΔ' : Δ ≠ 0 := hΔd ▸ hΔ
  have hΔz' : Δz ≠ 0 := hΔzd ▸ hΔz
  obtain ⟨κ, hκ⟩ : ∃ κ : F, κ = Δ / Δz := ⟨_, rfl⟩
  have hκ0 : κ ≠ 0 := by rw [hκ]; exact div_ne_zero hΔ' hΔz'
  have hdet : ((z₁ * w₂' - κ * z₁' * w₂) / Δ) * ((κ * z₂' * w₁ - z₂ * w₁') / Δ) -
      ((κ * z₁' * w₁ - z₁ * w₁') / Δ) * ((z₂ * w₂' - κ * z₂' * w₂) / Δ) = 1 := by
    rw [hκ]
    field_simp
    subst hΔd hΔzd
    ring
  refine ⟨⟨!![(z₁ * w₂' - κ * z₁' * w₂) / Δ, (κ * z₁' * w₁ - z₁ * w₁') / Δ;
      (z₂ * w₂' - κ * z₂' * w₂) / Δ, (κ * z₂' * w₁ - z₂ * w₁') / Δ], by
        rw [Matrix.det_fin_two_of]
        exact hdet⟩, κ, hκ0, ?_, ?_, ?_, ?_⟩
  all_goals
    simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.empty_val', Matrix.cons_val_fin_one]
    field_simp
    subst hΔd
    ring

end Levi

section PointsTwo

open CFSG.RankThree.PartOne.KCRootAxis

@[expose] def vec (s t : F) : W F := ![0, s, t, 0]

omit [CharP F 2] in
theorem vec_ne_zero {s t : F} (h : s ≠ 0 ∨ t ≠ 0) : vec s t ≠ 0 := by
  intro h0
  rcases h with h | h
  · exact h (by simpa [vec] using congrFun h0 1)
  · exact h (by simpa [vec] using congrFun h0 2)

omit [CharP F 2] in
theorem inc_mkPt_iff {v : W F} {hv : v ≠ 0} {L : Ln F} : inc (mkPt v hv) L ↔ v ∈ L.1 := by
  show Submodule.span F {v} ≤ L.1 ↔ v ∈ L.1
  rw [Submodule.span_le]
  simp

omit [CharP F 2] in
theorem exists_dir {L : Ln F} (h : inc (pt0 : Pt F) L) :
    ∃ s t : F, (s ≠ 0 ∨ t ≠ 0) ∧ vec s t ∈ L.1 := by
  have hnle : ¬ L.1 ≤ (pt0 : Pt F).1 := by
    intro hle
    have := Submodule.finrank_mono hle
    rw [L.2.1, (pt0 : Pt F).2] at this
    exact absurd this (by norm_num)
  obtain ⟨v, hvL, hvp⟩ := IsConcreteLE.not_le_iff_exists.mp hnle
  have hv3 : v 3 = 0 := by
    have := L.2.2 (ev 0) (h ev0_mem_pt0) v hvL
    rw [minorForm_apply] at this
    simpa [ev_apply] using this
  have hw : vec (v 1) (v 2) = v - v 0 • ev 0 := by
    ext i
    fin_cases i <;> simp [vec, ev_apply, hv3]
  refine ⟨v 1, v 2, ?_, ?_⟩
  · by_contra hcon
    push Not at hcon
    apply hvp
    have : v = v 0 • ev 0 := by
      ext i
      fin_cases i <;> simp [ev_apply, hv3, hcon.1, hcon.2]
    rw [this]
    exact Submodule.smul_mem _ _ ev0_mem_pt0
  · rw [hw]
    exact L.1.sub_mem hvL (L.1.smul_mem _ (h ev0_mem_pt0))

omit [CharP F 2] in
theorem pt0_ne_mkPt_vec {s t : F} (hd : s ≠ 0 ∨ t ≠ 0) :
    (pt0 : Pt F) ≠ mkPt (vec s t) (vec_ne_zero hd) := by
  intro heq
  have hmem : vec s t ∈ (pt0 : Pt F).1 := by
    rw [heq]
    exact mem_mkPt _
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hmem
  rcases hd with hd | hd
  · exact hd (by simpa [vec, ev_apply] using (congrFun hc 1).symm)
  · exact hd (by simpa [vec, ev_apply] using (congrFun hc 2).symm)

omit [CharP F 2] in
theorem line_eq_pt0_sup {L : Ln F} (h : inc (pt0 : Pt F) L) {s t : F} (hd : s ≠ 0 ∨ t ≠ 0)
    (hv : vec s t ∈ L.1) : L.1 = (pt0 : Pt F).1 ⊔ (mkPt (vec s t) (vec_ne_zero hd)).1 :=
  line_eq_sup (pt0_ne_mkPt_vec hd) h (inc_mkPt_iff.mpr hv)

omit [CharP F 2] in
theorem exists_scalar {s t s' t' : F} (hd : s ≠ 0 ∨ t ≠ 0) (hd' : s' ≠ 0 ∨ t' ≠ 0)
    (h0 : s * t' - t * s' = 0) : ∃ l : F, l ≠ 0 ∧ s = l * s' ∧ t = l * t' := by
  by_cases hs' : s' = 0
  · have ht' : t' ≠ 0 := hd'.resolve_left (not_not.mpr hs')
    subst hs'
    have hs : s = 0 := by
      have : s * t' = 0 := by linear_combination h0
      exact (mul_eq_zero.mp this).resolve_right ht'
    refine ⟨t / t', ?_, by simp [hs], by field_simp⟩
    intro hl
    rw [div_eq_zero_iff] at hl
    rcases hl with hl | hl
    · rcases hd with hd | hd
      · exact hd hs
      · exact hd hl
    · exact ht' hl
  · refine ⟨s / s', ?_, by field_simp, ?_⟩
    · intro hl
      rw [div_eq_zero_iff] at hl
      rcases hl with hl | hl
      · have ht : t = 0 := by
          have : t * s' = 0 := by linear_combination -h0 + t' * hl
          exact (mul_eq_zero.mp this).resolve_right hs'
        rcases hd with hd | hd
        · exact hd hl
        · exact hd ht
      · exact hs' hl
    · field_simp
      linear_combination -h0

omit [CharP F 2] in
theorem vec_smul_eq {s t s' t' l : F} (hs : s = l * s') (ht : t = l * t') :
    vec s t = l • vec s' t' := by
  ext i
  fin_cases i <;> simp [vec, hs, ht]

omit [CharP F 2] in
theorem det_ne_of_ne {L L' : Ln F} (hL : inc (pt0 : Pt F) L) (hL' : inc (pt0 : Pt F) L')
    {s t s' t' : F} (hd : s ≠ 0 ∨ t ≠ 0) (hd' : s' ≠ 0 ∨ t' ≠ 0) (hv : vec s t ∈ L.1)
    (hv' : vec s' t' ∈ L'.1) (hne : L ≠ L') : s * t' - t * s' ≠ 0 := by
  intro h0
  apply hne
  obtain ⟨l, hl0, hs, ht⟩ := exists_scalar hd hd' h0
  have hmem : vec s t ∈ L'.1 := by
    rw [vec_smul_eq hs ht]
    exact L'.1.smul_mem _ hv'
  exact two_pts pt0 (mkPt (vec s t) (vec_ne_zero hd)) L L' hL (inc_mkPt_iff.mpr hv) hL'
    (inc_mkPt_iff.mpr hmem) (pt0_ne_mkPt_vec hd)

theorem actLin_sElt_vec (N : Matrix.SpecialLinearGroup (Fin 2) F) (s t : F) :
    actLin (sElt N) (vec s t) = vec (N 0 0 * s + N 0 1 * t) (N 1 0 * s + N 1 1 * t) := by
  ext i
  fin_cases i <;>
    simp [actLin_apply, mat_sElt, sMat, vec, Matrix.mulVec, dotProduct, Fin.sum_univ_four]

theorem actLin_sElt_ev0 (N : Matrix.SpecialLinearGroup (Fin 2) F) :
    actLin (sElt N) (ev 0) = ev 0 := by
  ext i
  fin_cases i <;>
    simp [actLin_apply, mat_sElt, sMat, ev_apply, Matrix.mulVec, dotProduct]

omit [CharP F 2] in
theorem mapSub_le_of_gens {g : antiSp F} {L M : Ln F} {p₁ p₂ : Pt F} {v₁ v₂ : W F}
    (hL : L.1 = p₁.1 ⊔ p₂.1) (hp₁ : p₁.1 = Submodule.span F {v₁})
    (hp₂ : p₂.1 = Submodule.span F {v₂}) (h₁ : actLin g v₁ ∈ M.1) (h₂ : actLin g v₂ ∈ M.1) :
    mapSub g L.1 ≤ M.1 := by
  show Submodule.map (actLin g) L.1 ≤ M.1
  rw [hL, Submodule.map_sup, hp₁, hp₂, Submodule.map_span, Submodule.map_span, sup_le_iff,
    Submodule.span_le, Submodule.span_le]
  exact ⟨by simpa using h₁, by simpa using h₂⟩

theorem two_trans_pt0 {L L' M M' : Ln F} (hL : inc (pt0 : Pt F) L) (hL' : inc (pt0 : Pt F) L')
    (hM : inc (pt0 : Pt F) M) (hM' : inc (pt0 : Pt F) M') (hne : L ≠ L') (hne' : M ≠ M') :
    ∃ g : antiSp F, g • (pt0 : Pt F) = pt0 ∧ g • L = M ∧ g • L' = M' := by
  obtain ⟨s, t, hd, hv⟩ := exists_dir hL
  obtain ⟨s', t', hd', hv'⟩ := exists_dir hL'
  obtain ⟨u, v, he, hu⟩ := exists_dir hM
  obtain ⟨u', v', he', hu'⟩ := exists_dir hM'
  have hΔ := det_ne_of_ne hL hL' hd hd' hv hv' hne
  have hΔz := det_ne_of_ne hM hM' he he' hu hu' hne'
  obtain ⟨N, κ, hκ, e1, e2, e3, e4⟩ := sl2_two_trans s t s' t' u v u' v' hΔ hΔz
  have h0M : actLin (sElt N) (ev 0) ∈ M.1 := by
    rw [actLin_sElt_ev0]
    exact hM ev0_mem_pt0
  have h0M' : actLin (sElt N) (ev 0) ∈ M'.1 := by
    rw [actLin_sElt_ev0]
    exact hM' ev0_mem_pt0
  refine ⟨sElt N, smul_pt_eq_of_mem (v := ev 0) rfl (by rw [actLin_sElt_ev0]; exact ev0_mem_pt0),
    ?_, ?_⟩
  · refine smul_ln_eq_of_le (mapSub_le_of_gens (line_eq_pt0_sup hL hd hv) rfl rfl h0M ?_)
    rw [actLin_sElt_vec, e1, e2]
    exact hu
  · refine smul_ln_eq_of_le (mapSub_le_of_gens (line_eq_pt0_sup hL' hd' hv') rfl rfl h0M' ?_)
    rw [actLin_sElt_vec, e3, e4]
    have : vec (κ * u') (κ * v') = κ • vec u' v' := by
      ext i
      fin_cases i <;> simp [vec]
    rw [this]
    exact M'.1.smul_mem _ hu'

end PointsTwo

section Lines

omit [CharP F 2] in
theorem actLin_sub (g : antiSp F) (x y : W F) : actLin g (x - y) = actLin g x - actLin g y :=
  map_sub _ x y

omit [CharP F 2] in
theorem eq_one_of_actLin_eq {q : antiSp F} (h : ∀ v, actLin q v = v) : q = 1 := by
  apply mat_ext
  rw [mat_one]
  ext i j
  have := h (ev j)
  have h2 := congrFun this i
  rw [actLin_ev, ev_apply] at h2
  rw [h2]
  simp [Matrix.one_apply]

theorem mem_radA1_iff (x : antiSp F) : x ∈ radA1 F ↔ actLin x (ev 0) = ev 0 ∧
    actLin x (ev 1) = ev 1 ∧ ∀ v, actLin x v - v ∈ (ln0 : Ln F).1 := by
  constructor
  · rintro ⟨b, c, d, rfl⟩
    refine ⟨?_, ?_, fun v => ?_⟩
    · ext i
      fin_cases i <;> simp [actLin_uElt, ev_apply]
    · ext i
      fin_cases i <;> simp [actLin_uElt, ev_apply]
    · rw [mem_ln0_iff]
      constructor <;> simp [actLin_uElt]
  · rintro ⟨h0, h1, h2⟩
    have c0 : ∀ i, mat x i 0 = if i = 0 then 1 else 0 := by
      intro i
      have := congrFun h0 i
      rwa [actLin_ev, ev_apply] at this
    have c1 : ∀ i, mat x i 1 = if i = 1 then 1 else 0 := by
      intro i
      have := congrFun h1 i
      rwa [actLin_ev, ev_apply] at this
    have c2 := (mem_ln0_iff _).mp (h2 (ev 2))
    have c3 := (mem_ln0_iff _).mp (h2 (ev 3))
    simp [actLin_ev, ev_apply] at c2 c3
    have hs := mat_entry_eq x 2 3
    have hcond : ¬ (((2 : Fin 4) : ℕ) + ((3 : Fin 4) : ℕ) = 3) := by decide
    simp only [hcond, ↓reduceIte] at hs
    have h22 : mat x 2 2 = 1 := sub_eq_zero.mp c2.1
    have h33 : mat x 3 3 = 1 := sub_eq_zero.mp c3.2
    have h32 : mat x 3 2 = 0 := c2.2
    have h23 : mat x 2 3 = 0 := c3.1
    have hα : mat x 1 3 = mat x 0 2 := by
      rw [h22, h33, h32, h23] at hs
      have h2' : (2 : F) = 0 := CharTwo.two_eq_zero
      linear_combination hs - mat x 0 2 * h2'
    refine ⟨mat x 0 2, mat x 0 3, mat x 1 2, ?_⟩
    apply mat_ext
    ext i j
    fin_cases i <;> fin_cases j <;> simp [glMat_uElt, uMat, c0, c1, h22, h33, h32, h23, hα]

theorem ev0_mem_ln0 : (ev 0 : W F) ∈ (ln0 : Ln F).1 := inc_pt0_ln0 ev0_mem_pt0

theorem ev1_mem_ln0 : (ev 1 : W F) ∈ (ln0 : Ln F).1 :=
  inc_eline_right (i := 0) (j := 1) _ _ (mem_mkPt (ev_ne_zero 1))

theorem fix_ln0 {h : antiSp F} (hh : h ∈ radA1 F) : ∀ v ∈ (ln0 : Ln F).1, actLin h v = v := by
  obtain ⟨h0, h1, -⟩ := (mem_radA1_iff h).mp hh
  intro v hv
  obtain ⟨hv2, hv3⟩ := (mem_ln0_iff v).mp hv
  have : v = v 0 • ev 0 + v 1 • ev 1 := by
    ext i
    fin_cases i <;> simp [ev_apply, hv2, hv3]
  rw [this, map_add, map_smul, map_smul, h0, h1]

theorem mem_ln0_of_fix {u : W F} (hu : ∀ x ∈ radA1 F, actLin x u = u) : u ∈ (ln0 : Ln F).1 := by
  have h := hu (uElt 0 1 0 0) ⟨1, 0, 0, rfl⟩
  have e0 := congrFun h 0
  have e1 := congrFun h 1
  simp [actLin_uElt] at e0 e1
  exact (mem_ln0_iff u).mpr ⟨e0, e1⟩

theorem conj_mem_radA1 {y : antiSp F} (hy : y • (ln0 : Ln F) = ln0) {h : antiSp F}
    (hh : h ∈ radA1 F) : y * h * y⁻¹ ∈ radA1 F := by
  have hy' : y⁻¹ • (ln0 : Ln F) = ln0 := inv_smul_eq_iff.mpr hy.symm
  have hmy : ∀ v ∈ (ln0 : Ln F).1, actLin y v ∈ (ln0 : Ln F).1 := by
    intro v hv
    have : mapSub y (ln0 : Ln F).1 = (ln0 : Ln F).1 := congrArg Subtype.val hy
    rw [← this]
    exact Submodule.mem_map_of_mem hv
  have hmy' : ∀ v ∈ (ln0 : Ln F).1, actLin y⁻¹ v ∈ (ln0 : Ln F).1 := by
    intro v hv
    have : mapSub y⁻¹ (ln0 : Ln F).1 = (ln0 : Ln F).1 := congrArg Subtype.val hy'
    rw [← this]
    exact Submodule.mem_map_of_mem hv
  have hcancel : ∀ v, actLin y (actLin y⁻¹ v) = v := fun v => by
    rw [← actLin_mul_apply, mul_inv_cancel, actLin_one_apply]
  obtain ⟨h0, h1, h2⟩ := (mem_radA1_iff h).mp hh
  rw [mem_radA1_iff]
  refine ⟨?_, ?_, fun v => ?_⟩
  · rw [actLin_mul_apply, actLin_mul_apply, fix_ln0 hh _ (hmy' _ ev0_mem_ln0), hcancel]
  · rw [actLin_mul_apply, actLin_mul_apply, fix_ln0 hh _ (hmy' _ ev1_mem_ln0), hcancel]
  · have e : actLin (y * h * y⁻¹) v - v =
        actLin y (actLin h (actLin y⁻¹ v) - actLin y⁻¹ v) := by
      rw [actLin_sub, hcancel, actLin_mul_apply, actLin_mul_apply]
    rw [e]
    exact hmy _ (h2 _)

theorem stab_ln0_iff (y : antiSp F) :
    y • (ln0 : Ln F) = ln0 ↔ y ∈ Subgroup.normalizer (radA1 F : Set (antiSp F)) := by
  constructor
  · intro hy
    have hy' : y⁻¹ • (ln0 : Ln F) = ln0 := inv_smul_eq_iff.mpr hy.symm
    refine Subgroup.mem_normalizer_iff.mpr fun h => ⟨fun hh => conj_mem_radA1 hy hh, fun hh => ?_⟩
    have := conj_mem_radA1 hy' hh
    simpa [mul_assoc] using this
  · intro hy
    apply smul_ln_eq_of_le
    intro u hu
    obtain ⟨v, hv, rfl⟩ := mem_mapSub.mp hu
    apply mem_ln0_of_fix
    intro x hx
    have hx' : y⁻¹ * x * y ∈ radA1 F := by
      have := (Subgroup.mem_normalizer_iff.mp hy (y⁻¹ * x * y)).mpr (by
        simpa [mul_assoc] using hx)
      exact this
    have e : actLin x (actLin y v) = actLin y (actLin (y⁻¹ * x * y) v) := by
      rw [actLin_mul_apply, actLin_mul_apply, ← actLin_mul_apply y y⁻¹, mul_inv_cancel,
        actLin_one_apply]
    rw [e, fix_ln0 hx' v hv]

theorem qfix_ln0 {q : antiSp F} (hq : q ∈ radA1 F) {p : Pt F} (hp : inc p (ln0 : Ln F)) :
    q • p = p := by
  obtain ⟨v, hv0, hv⟩ := pt_eq_span p
  have hvL : v ∈ (ln0 : Ln F).1 := hp (by rw [hv]; exact Submodule.mem_span_singleton_self v)
  exact smul_pt_eq_of_mem hv
    (by rw [fix_ln0 hq v hvL, hv]; exact Submodule.mem_span_singleton_self v)

theorem opp_line_inf {L : Ln F} (h : (Gr F).dist (Sum.inr ln0) (Sum.inr L) = 4) :
    L.1 ⊓ (ln0 : Ln F).1 = ⊥ := by
  obtain ⟨-, hno⟩ := (gqAxioms.dist_inr_inr_eq_four (ln0 : Ln F) L).mp h
  by_contra hne
  obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  exact hno ⟨mkPt v hv0, inc_mkPt_iff.mpr hv.2, inc_mkPt_iff.mpr hv.1⟩

theorem opp_line_top {L : Ln F} (hinf : L.1 ⊓ (ln0 : Ln F).1 = ⊥) :
    L.1 ⊔ (ln0 : Ln F).1 = ⊤ := by
  have h := Submodule.finrank_sup_add_finrank_inf_eq L.1 (ln0 : Ln F).1
  rw [hinf, finrank_bot, L.2.1, (ln0 : Ln F).2.1] at h
  apply Submodule.eq_top_of_finrank_eq
  simp only [Module.finrank_fin_fun]
  omega

theorem exists_opp_gen {L : Ln F} (hinf : L.1 ⊓ (ln0 : Ln F).1 = ⊥) :
    ∃ α β γ : F, (![α, β, 1, 0] : W F) ∈ L.1 ∧ (![γ, α, 0, 1] : W F) ∈ L.1 := by
  have htop := opp_line_top hinf
  have h2 : (ev 2 : W F) ∈ L.1 ⊔ (ln0 : Ln F).1 := by rw [htop]; trivial
  have h3 : (ev 3 : W F) ∈ L.1 ⊔ (ln0 : Ln F).1 := by rw [htop]; trivial
  obtain ⟨l, hl, m, hm, hlm⟩ := Submodule.mem_sup.mp h2
  obtain ⟨l', hl', m', hm', hlm'⟩ := Submodule.mem_sup.mp h3
  obtain ⟨hm2, hm3⟩ := (mem_ln0_iff m).mp hm
  obtain ⟨hm2', hm3'⟩ := (mem_ln0_iff m').mp hm'
  have l2 : l 2 = 1 := by
    have := congrFun hlm 2
    simpa [ev_apply, hm2] using this
  have l3 : l 3 = 0 := by
    have := congrFun hlm 3
    simpa [ev_apply, hm3] using this
  have l2' : l' 2 = 0 := by
    have := congrFun hlm' 2
    simpa [ev_apply, hm2'] using this
  have l3' : l' 3 = 1 := by
    have := congrFun hlm' 3
    simpa [ev_apply, hm3'] using this
  have hiso := L.2.2 l hl l' hl'
  rw [minorForm_apply, l2, l3, l2', l3'] at hiso
  have h2' : (2 : F) = 0 := CharTwo.two_eq_zero
  have hδ : l' 1 = l 0 := by linear_combination hiso - l 0 * h2'
  refine ⟨l 0, l 1, l' 0, ?_, ?_⟩
  · have : (![l 0, l 1, 1, 0] : W F) = l := by
      ext i
      fin_cases i <;> simp [l2, l3]
    rw [this]
    exact hl
  · have : (![l' 0, l 0, 0, 1] : W F) = l' := by
      ext i
      fin_cases i <;> simp [l2', l3', hδ]
    rw [this]
    exact hl'

theorem exists_radA1_smul_lnStar {L : Ln F} (hinf : L.1 ⊓ (ln0 : Ln F).1 = ⊥) :
    ∃ q ∈ radA1 F, q • (lnStar : Ln F) = L := by
  obtain ⟨α, β, γ, h2, h3⟩ := exists_opp_gen hinf
  refine ⟨uElt 0 α γ β, ⟨α, γ, β, rfl⟩, ?_⟩
  refine smul_ln_eq_of_le (mapSub_le_of_gens (p₁ := epts 2) (p₂ := epts 3) (v₁ := ev 2)
    (v₂ := ev 3) rfl rfl rfl ?_ ?_)
  · have : actLin (uElt 0 α γ β) (ev 2) = ![α, β, 1, 0] := by
      ext i
      fin_cases i <;> simp [actLin_uElt, ev_apply]
    rw [this]
    exact h2
  · have : actLin (uElt 0 α γ β) (ev 3) = ![γ, α, 0, 1] := by
      ext i
      fin_cases i <;> simp [actLin_uElt, ev_apply]
    rw [this]
    exact h3

theorem radA1_trans {L L' : Ln F} (h : (Gr F).dist (Sum.inr ln0) (Sum.inr L) = 4)
    (h' : (Gr F).dist (Sum.inr ln0) (Sum.inr L') = 4) : ∃ q ∈ radA1 F, q • L = L' := by
  obtain ⟨q₁, hq₁, e₁⟩ := exists_radA1_smul_lnStar (opp_line_inf h)
  obtain ⟨q₂, hq₂, e₂⟩ := exists_radA1_smul_lnStar (opp_line_inf h')
  refine ⟨q₂ * q₁⁻¹, (radA1 F).mul_mem hq₂ ((radA1 F).inv_mem hq₁), ?_⟩
  rw [mul_smul, ← e₁, inv_smul_smul, e₂]

theorem radA1_free {q : antiSp F} (hq : q ∈ radA1 F) {L : Ln F}
    (h : (Gr F).dist (Sum.inr ln0) (Sum.inr L) = 4) (hqL : q • L = L) : q = 1 := by
  have hinf := opp_line_inf h
  have htop := opp_line_top hinf
  obtain ⟨-, -, h2⟩ := (mem_radA1_iff q).mp hq
  have hmL : ∀ x ∈ L.1, actLin q x ∈ L.1 := by
    intro x hx
    have : mapSub q L.1 = L.1 := congrArg Subtype.val hqL
    rw [← this]
    exact Submodule.mem_map_of_mem hx
  apply eq_one_of_actLin_eq
  intro v
  have hv : v ∈ L.1 ⊔ (ln0 : Ln F).1 := by rw [htop]; trivial
  obtain ⟨l, hl, m, hm, rfl⟩ := Submodule.mem_sup.mp hv
  rw [map_add, fix_ln0 hq m hm]
  have : actLin q l = l := by
    have hmem : actLin q l - l ∈ L.1 ⊓ (ln0 : Ln F).1 := ⟨L.1.sub_mem (hmL l hl) hl, h2 l⟩
    rw [hinf, Submodule.mem_bot, sub_eq_zero] at hmem
    exact hmem
  rw [this]

end Lines

section LinesTwo

@[expose] def lMat (M : Matrix (Fin 2) (Fin 2) F) : Matrix (Fin 4) (Fin 4) F :=
  !![M 0 0, M 0 1, 0, 0; M 1 0, M 1 1, 0, 0; 0, 0, M 0 0, M 0 1; 0, 0, M 1 0, M 1 1]

omit [CharP F 2] in
theorem lMat_mul (M N : Matrix (Fin 2) (Fin 2) F) : lMat M * lMat N = lMat (M * N) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [lMat, Matrix.mul_apply, Fin.sum_univ_four, Fin.sum_univ_two]

omit [CharP F 2] in
theorem lMat_one : lMat (1 : Matrix (Fin 2) (Fin 2) F) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [lMat]

theorem lMat_mem {M : Matrix (Fin 2) (Fin 2) F} (hM : M.det = 1) :
    (lMat M)ᵀ * minorJ F * lMat M = minorJ F := by
  rw [Matrix.det_fin_two] at hM
  ext k l
  rw [transpose_mul_minorJ_mul_apply, minorJ_apply]
  fin_cases k <;> fin_cases l <;> simp [lMat] <;> grind

@[expose] def lElt (M : Matrix.SpecialLinearGroup (Fin 2) F) : antiSp F :=
  ⟨⟨lMat (M : Matrix (Fin 2) (Fin 2) F),
    lMat ((M⁻¹ : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F),
    by rw [lMat_mul, ← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel,
      Matrix.SpecialLinearGroup.coe_one, lMat_one],
    by rw [lMat_mul, ← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel,
      Matrix.SpecialLinearGroup.coe_one, lMat_one]⟩, lMat_mem M.2⟩

theorem mat_lElt (M : Matrix.SpecialLinearGroup (Fin 2) F) :
    mat (lElt M) = lMat (M : Matrix (Fin 2) (Fin 2) F) := rfl

theorem actLin_lElt (N : Matrix.SpecialLinearGroup (Fin 2) F) (x : W F) :
    actLin (lElt N) x = ![N 0 0 * x 0 + N 0 1 * x 1, N 1 0 * x 0 + N 1 1 * x 1,
      N 0 0 * x 2 + N 0 1 * x 3, N 1 0 * x 2 + N 1 1 * x 3] := by
  ext i
  fin_cases i <;>
    simp [actLin_apply, mat_lElt, lMat, Matrix.mulVec, dotProduct, Fin.sum_univ_four]

@[expose] def vec' (s t : F) : W F := ![s, t, 0, 0]

omit [CharP F 2] in
theorem vec'_smul_eq {s t s' t' l : F} (hs : s = l * s') (ht : t = l * t') :
    vec' s t = l • vec' s' t' := by
  ext i
  fin_cases i <;> simp [vec', hs, ht]

theorem stab_lElt (N : Matrix.SpecialLinearGroup (Fin 2) F) : lElt N • (ln0 : Ln F) = ln0 := by
  apply smul_ln_eq_of_le
  intro y hy
  obtain ⟨x, hx, rfl⟩ := mem_mapSub.mp hy
  obtain ⟨h2, h3⟩ := (mem_ln0_iff x).mp hx
  rw [mem_ln0_iff]
  simp [actLin_lElt, h2, h3]

theorem exists_dir_pt {p : Pt F} (hp : inc p (ln0 : Ln F)) :
    ∃ s t : F, (s ≠ 0 ∨ t ≠ 0) ∧ p.1 = Submodule.span F {vec' s t} := by
  obtain ⟨v, hv0, hv⟩ := pt_eq_span p
  have hvL : v ∈ (ln0 : Ln F).1 := hp (by rw [hv]; exact Submodule.mem_span_singleton_self v)
  obtain ⟨h2, h3⟩ := (mem_ln0_iff v).mp hvL
  have hv' : v = vec' (v 0) (v 1) := by
    ext i
    fin_cases i <;> simp [vec', h2, h3]
  refine ⟨v 0, v 1, ?_, by rw [hv, ← hv']⟩
  by_contra hcon
  push Not at hcon
  apply hv0
  rw [hv']
  ext i
  fin_cases i <;> simp [vec', hcon.1, hcon.2]

omit [CharP F 2] in
theorem det_ne_pt {p p' : Pt F} {s t s' t' : F} (hd : s ≠ 0 ∨ t ≠ 0) (hd' : s' ≠ 0 ∨ t' ≠ 0)
    (hp : p.1 = Submodule.span F {vec' s t}) (hp' : p'.1 = Submodule.span F {vec' s' t'})
    (hne : p ≠ p') : s * t' - t * s' ≠ 0 := by
  intro h0
  apply hne
  obtain ⟨l, hl0, hs, ht⟩ := exists_scalar hd hd' h0
  have hle : p.1 ≤ p'.1 := by
    rw [hp, Submodule.span_le]
    simp only [Set.singleton_subset_iff, SetLike.mem_coe]
    rw [vec'_smul_eq hs ht, hp']
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)
  exact Subtype.ext (Submodule.eq_of_le_of_finrank_eq hle (by rw [p.2, p'.2]))

theorem two_trans_ln0 {p p' q q' : Pt F} (hp : inc p (ln0 : Ln F)) (hp' : inc p' (ln0 : Ln F))
    (hq : inc q (ln0 : Ln F)) (hq' : inc q' (ln0 : Ln F)) (hne : p ≠ p') (hne' : q ≠ q') :
    ∃ g : antiSp F, g • (ln0 : Ln F) = ln0 ∧ g • p = q ∧ g • p' = q' := by
  obtain ⟨s, t, hd, hpg⟩ := exists_dir_pt hp
  obtain ⟨s', t', hd', hpg'⟩ := exists_dir_pt hp'
  obtain ⟨u, v, he, hqg⟩ := exists_dir_pt hq
  obtain ⟨u', v', he', hqg'⟩ := exists_dir_pt hq'
  have hΔ := det_ne_pt hd hd' hpg hpg' hne
  have hΔz := det_ne_pt he he' hqg hqg' hne'
  obtain ⟨N, κ, hκ, e1, e2, e3, e4⟩ := sl2_two_trans s t s' t' u v u' v' hΔ hΔz
  refine ⟨lElt N, stab_lElt N, ?_, ?_⟩
  · refine smul_pt_eq_of_mem hpg ?_
    have : actLin (lElt N) (vec' s t) = vec' u v := by
      rw [actLin_lElt]
      ext i
      fin_cases i <;> simp [vec', e1, e2]
    rw [this, hqg]
    exact Submodule.mem_span_singleton_self _
  · refine smul_pt_eq_of_mem hpg' ?_
    have : actLin (lElt N) (vec' s' t') = κ • vec' u' v' := by
      rw [actLin_lElt]
      ext i
      fin_cases i <;> simp [vec', e3, e4]
    rw [this, hqg']
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)

end LinesTwo

section Final

instance [Finite F] : Finite (Pt F) := inferInstanceAs (Finite {_U : Submodule F (W F) // _})

instance [Finite F] : Finite (Ln F) := inferInstanceAs (Finite {_U : Submodule F (W F) // _})

omit [CharP F 2] in
theorem mkPt_ne_of {u v : W F} (hu : u ≠ 0) (hv : v ≠ 0) (h : ∀ c : F, c • u ≠ v) :
    mkPt u hu ≠ mkPt v hv := by
  intro heq
  have hmem : v ∈ (mkPt u hu).1 := by
    rw [heq]
    exact mem_mkPt hv
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hmem
  exact h c hc

omit [CharP F 2] in
theorem nbrs_card_inl {r : Pt F → Ln F → Prop} (a : Pt F) :
    Nat.card ((incGraph r).neighborSet (Sum.inl a)) = {b | r a b}.ncard := by
  rw [neighborSet_inl, Nat.card_coe_set_eq, Set.ncard_image_of_injective _ Sum.inr_injective]

omit [CharP F 2] in
theorem nbrs_card_inr {r : Pt F → Ln F → Prop} (b : Ln F) :
    Nat.card ((incGraph r).neighborSet (Sum.inr b)) = {a | r a b}.ncard := by
  rw [neighborSet_inr, Nat.card_coe_set_eq, Set.ncard_image_of_injective _ Sum.inl_injective]

omit [CharP F 2] in
theorem not_both (L : Ln F) (h1 : (ev 1 : W F) ∈ L.1) (h2 : (ev 2 : W F) ∈ L.1) : False := by
  have := L.2.2 _ h1 _ h2
  rw [minorForm_apply] at this
  simp [ev_apply] at this

theorem three_pt0 [Finite F] : 3 ≤ Nat.card ((Gr F).neighborSet (Sum.inl (pt0 : Pt F))) := by
  rw [nbrs_card_inl]
  have e02 : minorForm F (ev 0 : W F) (ev 2) = 0 := by rw [minorForm_apply]; simp [ev_apply]
  have hw : (ev 1 + ev 2 : W F) ≠ 0 := by
    intro h
    have := congrFun h 1
    simp [ev_apply] at this
  have hw0 : minorForm F (ev 0 : W F) (ev 1 + ev 2) = 0 := by
    rw [minorForm_apply]
    simp [ev_apply]
  have d02 : (0 : Fin 4) ≠ 2 := by decide
  let M₁ : Ln F := ln0
  let M₂ : Ln F := eline 0 2 d02 e02
  let P : Pt F := mkPt (ev 1 + ev 2) hw
  have hne : (pt0 : Pt F) ≠ P := by
    refine mkPt_ne_of (ev_ne_zero 0) hw fun c hc => ?_
    have := congrFun hc 1
    simp [ev_apply] at this
  let M₃ : Ln F := mkLine (pt0 : Pt F) P hne (perp_of_gen hw0 _ _ rfl rfl)
  have i1 : inc (pt0 : Pt F) M₁ := inc_pt0_ln0
  have i2 : inc (pt0 : Pt F) M₂ := inc_eline_left _ _
  have i3 : inc (pt0 : Pt F) M₃ := inc_mkLine_left _ _ _ _
  have e1 : (ev 1 : W F) ∈ M₁.1 := ev1_mem_ln0
  have e2 : (ev 2 : W F) ∈ M₂.1 := inc_eline_right (i := 0) (j := 2) _ _ (mem_mkPt (ev_ne_zero 2))
  have ew : (ev 1 + ev 2 : W F) ∈ M₃.1 := inc_mkLine_right _ _ _ _ (mem_mkPt hw)
  have e1' : (ev 1 : W F) ∉ M₂.1 := fun h => not_both M₂ h e2
  have h12 : M₁ ≠ M₂ := fun h => e1' (h ▸ e1)
  have h13 : M₁ ≠ M₃ := by
    intro h
    have h1' : (ev 1 : W F) ∈ M₃.1 := h ▸ e1
    exact not_both M₃ h1' (by simpa using M₃.1.sub_mem ew h1')
  have h23 : M₂ ≠ M₃ := by
    intro h
    have h2' : (ev 2 : W F) ∈ M₃.1 := h ▸ e2
    exact not_both M₃ (by simpa using M₃.1.sub_mem ew h2') h2'
  have hsub : ({M₁, M₂, M₃} : Set (Ln F)) ⊆ {b | inc (pt0 : Pt F) b} := by
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl
    · exact i1
    · exact i2
    · exact i3
  have h3 : ({M₁, M₂, M₃} : Set (Ln F)).ncard = 3 := by
    rw [Set.ncard_eq_three]
    exact ⟨M₁, M₂, M₃, h12, h13, h23, rfl⟩
  rw [← h3]
  exact Set.ncard_le_ncard hsub (Set.toFinite _)

theorem three_ln0 [Finite F] : 3 ≤ Nat.card ((Gr F).neighborSet (Sum.inr (ln0 : Ln F))) := by
  rw [nbrs_card_inr]
  have hw : (ev 0 + ev 1 : W F) ≠ 0 := by
    intro h
    have := congrFun h 0
    simp [ev_apply] at this
  let P₀ : Pt F := mkPt (ev 0) (ev_ne_zero 0)
  let P₁ : Pt F := mkPt (ev 1) (ev_ne_zero 1)
  let P₂ : Pt F := mkPt (ev 0 + ev 1) hw
  have h01 : P₀ ≠ P₁ := mkPt_ne_of _ _ fun c hc => by
    have := congrFun hc 1
    simp [ev_apply] at this
  have h02 : P₀ ≠ P₂ := mkPt_ne_of _ _ fun c hc => by
    have := congrFun hc 1
    simp [ev_apply] at this
  have h12 : P₁ ≠ P₂ := mkPt_ne_of _ _ fun c hc => by
    have := congrFun hc 0
    simp [ev_apply] at this
  have i0 : inc P₀ (ln0 : Ln F) := inc_mkPt_iff.mpr ev0_mem_ln0
  have i1 : inc P₁ (ln0 : Ln F) := inc_mkPt_iff.mpr ev1_mem_ln0
  have i2 : inc P₂ (ln0 : Ln F) := inc_mkPt_iff.mpr (by
    rw [mem_ln0_iff]
    simp [ev_apply])
  have hsub : ({P₀, P₁, P₂} : Set (Pt F)) ⊆ {a | inc a (ln0 : Ln F)} := by
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl
    · exact i0
    · exact i1
    · exact i2
  have h3 : ({P₀, P₁, P₂} : Set (Pt F)).ncard = 3 := by
    rw [Set.ncard_eq_three]
    exact ⟨P₀, P₁, P₂, h01, h02, h12, rfl⟩
  rw [← h3]
  exact Set.ncard_le_ncard hsub (Set.toFinite _)

end Final

section ModelBases

theorem modelBase_pt0 : ModelBase (Gr F) 4 (Sum.inl (pt0 : Pt F)) (radA2 F) where
  Qfix w hw q hq := by
    obtain ⟨L, rfl, hL⟩ := incGraph_adj_inl hw
    rw [Sum.smul_inr, qfix_pt0 hq hL]
  Qtrans b c hb hc := by
    cases b with
    | inl p =>
      cases c with
      | inl p' =>
        obtain ⟨q, hq, h⟩ := radA2_trans hb hc
        exact ⟨q, hq, by rw [Sum.smul_inl, h]⟩
      | inr L' => exact absurd hc (gqAxioms.dist_inl_inr_ne_four _ _)
    | inr L => exact absurd hb (gqAxioms.dist_inl_inr_ne_four _ _)
  Qfree b hb q hq hqb := by
    cases b with
    | inl p =>
      refine radA2_free hq hb ?_
      rw [Sum.smul_inl] at hqb
      exact Sum.inl.inj hqb
    | inr L => exact absurd hb (gqAxioms.dist_inl_inr_ne_four _ _)
  two b c b' c' hb hc hbc hb' hc' hbc' := by
    obtain ⟨L, rfl, hL⟩ := incGraph_adj_inl hb
    obtain ⟨L', rfl, hL'⟩ := incGraph_adj_inl hc
    obtain ⟨M, rfl, hM⟩ := incGraph_adj_inl hb'
    obtain ⟨M', rfl, hM'⟩ := incGraph_adj_inl hc'
    obtain ⟨g, hg1, hg2, hg3⟩ := two_trans_pt0 hL hL' hM hM' (fun h => hbc (by rw [h]))
      (fun h => hbc' (by rw [h]))
    exact ⟨g, by rw [Sum.smul_inl, hg1], by rw [Sum.smul_inr, hg2], by rw [Sum.smul_inr, hg3]⟩

theorem modelBase_ln0 : ModelBase (Gr F) 4 (Sum.inr (ln0 : Ln F)) (radA1 F) where
  Qfix w hw q hq := by
    obtain ⟨p, rfl, hp⟩ := incGraph_adj_inr hw
    rw [Sum.smul_inl, qfix_ln0 hq hp]
  Qtrans b c hb hc := by
    cases b with
    | inl p => exact absurd hb (gqAxioms.dist_inr_inl_ne_four _ _)
    | inr L =>
      cases c with
      | inl p' => exact absurd hc (gqAxioms.dist_inr_inl_ne_four _ _)
      | inr L' =>
        obtain ⟨q, hq, h⟩ := radA1_trans hb hc
        exact ⟨q, hq, by rw [Sum.smul_inr, h]⟩
  Qfree b hb q hq hqb := by
    cases b with
    | inl p => exact absurd hb (gqAxioms.dist_inr_inl_ne_four _ _)
    | inr L =>
      refine radA1_free hq hb ?_
      rw [Sum.smul_inr] at hqb
      exact Sum.inr.inj hqb
  two b c b' c' hb hc hbc hb' hc' hbc' := by
    obtain ⟨p, rfl, hp⟩ := incGraph_adj_inr hb
    obtain ⟨p', rfl, hp'⟩ := incGraph_adj_inr hc
    obtain ⟨q, rfl, hq⟩ := incGraph_adj_inr hb'
    obtain ⟨q', rfl, hq'⟩ := incGraph_adj_inr hc'
    obtain ⟨g, hg1, hg2, hg3⟩ := two_trans_ln0 hp hp' hq hq' (fun h => hbc (by rw [h]))
      (fun h => hbc' (by rw [h]))
    exact ⟨g, by rw [Sum.smul_inr, hg1], by rw [Sum.smul_inl, hg2], by rw [Sum.smul_inl, hg3]⟩

end ModelBases

end SpGeom

end CFSG.Quasithin.H13.F431.F45

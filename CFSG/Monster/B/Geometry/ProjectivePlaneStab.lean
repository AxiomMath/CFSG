module

public import CFSG.Monster.B.Geometry.ProjectivePlaneBasic

public section

namespace CFSG.Monster.B.Geometry

open Module Submodule

variable {k : Type*} [Field k]

namespace ProjPlane

variable {g : Equiv.Perm (PlaneFlag k)} {P P' Q Q' L L' M M' : Submodule k (Fin 3 → k)}

theorem lnMap_eq_of_two (hg : g ∈ planeTypeAut k) (hP : finrank k P = 1) (hQ : finrank k Q = 1)
    (hL : finrank k L = 2) (hL' : finrank k L' = 2) (hne : P' ≠ Q') (hPP : ptMap g P = P')
    (hQQ : ptMap g Q = Q') (hPL : P ≤ L) (hQL : Q ≤ L) (hPL' : P' ≤ L') (hQL' : Q' ≤ L') :
    lnMap g L = L' := by
  subst hPP hQQ
  exact line_eq_of_ne (finrank_ptMap hg hP) (finrank_ptMap hg hQ) (finrank_lnMap hg hL) hL' hne
    ((ptMap_le_lnMap_iff hg hP hL).mpr hPL) ((ptMap_le_lnMap_iff hg hQ hL).mpr hQL) hPL' hQL'

theorem ptMap_eq_of_two (hg : g ∈ planeTypeAut k) (hP : finrank k P = 1)
    (hP' : finrank k P' = 1) (hL : finrank k L = 2) (hM : finrank k M = 2)
    (hne : L' ≠ M') (hLL : lnMap g L = L') (hMM : lnMap g M = M') (hPL : P ≤ L) (hPM : P ≤ M)
    (hPL' : P' ≤ L') (hPM' : P' ≤ M') : ptMap g P = P' := by
  subst hLL hMM
  exact pt_eq_of_ne (finrank_ptMap hg hP) hP' (finrank_lnMap hg hL) (finrank_lnMap hg hM) hne
    ((ptMap_le_lnMap_iff hg hP hL).mpr hPL) ((ptMap_le_lnMap_iff hg hP hM).mpr hPM) hPL' hPM'

theorem ptMap_le (hg : g ∈ planeTypeAut k) (hP : finrank k P = 1) (hL : finrank k L = 2)
    (hLL : lnMap g L = L') (h : P ≤ L) : ptMap g P ≤ L' :=
  hLL ▸ (ptMap_le_lnMap_iff hg hP hL).mpr h

theorem not_ptMap_le (hg : g ∈ planeTypeAut k) (hP : finrank k P = 1) (hL : finrank k L = 2)
    (hLL : lnMap g L = L') (h : ¬ P ≤ L) : ¬ ptMap g P ≤ L' :=
  hLL ▸ fun h' => h ((ptMap_le_lnMap_iff hg hP hL).mp h')

theorem ne_of_not_le_of_le (h₁ : ¬ P ≤ L) (h₂ : Q ≤ L) : P ≠ Q := fun h => h₁ (h ▸ h₂)

theorem ne_of_le_of_not_le' (h₁ : P ≤ L) (h₂ : ¬ P ≤ M) : L ≠ M := fun h => h₂ (h ▸ h₁)

theorem fr_aff (x y : k) : finrank k (k ∙ (![x, y, 1] : Fin 3 → k)) = 1 :=
  finrank_span_singleton (vec_ne_zero_of_two one_ne_zero)

theorem fr_inf (m : k) : finrank k (k ∙ (![1, m, 0] : Fin 3 → k)) = 1 :=
  finrank_span_singleton (vec_ne_zero_of_zero one_ne_zero)

theorem fr_vec0 {x y z : k} (h : x ≠ 0) : finrank k (k ∙ (![x, y, z] : Fin 3 → k)) = 1 :=
  finrank_span_singleton (vec_ne_zero_of_zero h)

theorem fr_vec1 {x y z : k} (h : y ≠ 0) : finrank k (k ∙ (![x, y, z] : Fin 3 → k)) = 1 :=
  finrank_span_singleton (vec_ne_zero_of_one h)

theorem fr_ker0 {α β γ : k} (h : α ≠ 0) : finrank k (kerLine α β γ) = 2 :=
  finrank_kerLine (Or.inl h)

theorem fr_ker1 {α β γ : k} (h : β ≠ 0) : finrank k (kerLine α β γ) = 2 :=
  finrank_kerLine (Or.inr (Or.inl h))

theorem fr_ker2 {α β γ : k} (h : γ ≠ 0) : finrank k (kerLine α β γ) = 2 :=
  finrank_kerLine (Or.inr (Or.inr h))

theorem exists_aff (hQ : finrank k Q = 1) (h : ¬ Q ≤ kerLine 0 0 1) :
    ∃ x y : k, Q = k ∙ ![x, y, 1] := by
  obtain ⟨v, -, rfl⟩ := exists_eq_span hQ
  rw [span_le_kerLine] at h
  have h2 : v 2 ≠ 0 := by simpa using h
  refine ⟨v 0 / v 2, v 1 / v 2, span_eq_span_of_eq_smul h2 ?_⟩
  ext i
  fin_cases i <;> simp [h2, mul_div_cancel₀]

theorem exists_inf (hQ : finrank k Q = 1) (h : Q ≤ kerLine 0 0 1)
    (h' : Q ≠ k ∙ ![0, 1, 0]) : ∃ m : k, Q = k ∙ ![1, m, 0] := by
  obtain ⟨v, hv0, rfl⟩ := exists_eq_span hQ
  rw [span_le_kerLine] at h
  have h2 : v 2 = 0 := by simpa using h
  by_cases h0 : v 0 = 0
  · exfalso
    apply h'
    have h1 : v 1 ≠ 0 := by
      intro h1
      apply hv0
      ext i
      fin_cases i <;> simp [h0, h1, h2]
    refine span_eq_span_of_eq_smul h1 ?_
    ext i
    fin_cases i <;> simp [h0, h2]
  · refine ⟨v 1 / v 0, span_eq_span_of_eq_smul h0 ?_⟩
    ext i
    fin_cases i <;> simp [h0, h2, mul_div_cancel₀]

noncomputable def coordX (g : Equiv.Perm (PlaneFlag k)) (x : k) : k :=
  Classical.epsilon fun s => ptMap g (k ∙ ![x, 0, 1]) = k ∙ ![s, 0, 1]

noncomputable def coordY (g : Equiv.Perm (PlaneFlag k)) (y : k) : k :=
  Classical.epsilon fun t => ptMap g (k ∙ ![0, y, 1]) = k ∙ ![0, t, 1]

noncomputable def semi (g : Equiv.Perm (PlaneFlag k)) (t : k) : k := (coordX g 1)⁻¹ * coordX g t

section Coordinates

variable (hg : g ∈ planeTypeAut k) (hc : g (PlaneFlag.c k) = PlaneFlag.c k)
  (hd : g (PlaneFlag.d k) = PlaneFlag.d k)
include hg hc hd

omit hd in
theorem ptMap_e0 : ptMap g (k ∙ ![1, 0, 0]) = k ∙ ![1, 0, 0] := by
  have h := ptMap_pt hg (PlaneFlag.c k)
  rwa [hc, PlaneFlag.c_pt] at h

omit hd in
theorem lnMap_001 : lnMap g (kerLine 0 0 1) = kerLine 0 0 1 := by
  have h := lnMap_line hg (PlaneFlag.c k)
  rwa [hc, PlaneFlag.c_line] at h

omit hc in
theorem ptMap_e2 : ptMap g (k ∙ ![0, 0, 1]) = k ∙ ![0, 0, 1] := by
  have h := ptMap_pt hg (PlaneFlag.d k)
  rwa [hd, PlaneFlag.d_pt] at h

omit hc in
theorem lnMap_100 : lnMap g (kerLine 1 0 0) = kerLine 1 0 0 := by
  have h := lnMap_line hg (PlaneFlag.d k)
  rwa [hd, PlaneFlag.d_line] at h

theorem ptMap_e1 : ptMap g (k ∙ ![0, 1, 0]) = k ∙ ![0, 1, 0] :=
  ptMap_eq_of_two hg (fr_vec1 one_ne_zero) (fr_vec1 one_ne_zero) (fr_ker2 one_ne_zero)
    (fr_ker0 one_ne_zero)
    (ne_of_le_of_not_le' (P := k ∙ ![1, 0, 0]) (vec_le_kerLine.mpr (by ring))
      (by rw [vec_le_kerLine]; norm_num))
    (lnMap_001 hg hc) (lnMap_100 hg hd) (vec_le_kerLine.mpr (by ring))
    (vec_le_kerLine.mpr (by ring)) (vec_le_kerLine.mpr (by ring)) (vec_le_kerLine.mpr (by ring))

theorem lnMap_010 : lnMap g (kerLine 0 1 0) = kerLine 0 1 0 :=
  lnMap_eq_of_two hg (fr_inf 0) (fr_aff 0 0) (fr_ker1 one_ne_zero) (fr_ker1 one_ne_zero)
    (ne_of_not_le_of_le (L := kerLine 0 0 1) (by rw [vec_le_kerLine]; norm_num)
      (vec_le_kerLine.mpr (by ring))).symm
    (ptMap_e0 hg hc) (ptMap_e2 hg hd) (vec_le_kerLine.mpr (by ring))
    (vec_le_kerLine.mpr (by ring)) (vec_le_kerLine.mpr (by ring)) (vec_le_kerLine.mpr (by ring))

theorem ptMap_x (x : k) : ptMap g (k ∙ ![x, 0, 1]) = k ∙ ![coordX g x, 0, 1] := by
  have hQ := finrank_ptMap hg (fr_aff x 0)
  have h1 : ptMap g (k ∙ ![x, 0, 1]) ≤ kerLine 0 1 0 :=
    ptMap_le hg (fr_aff x 0) (fr_ker1 one_ne_zero) (lnMap_010 hg hc hd)
      (vec_le_kerLine.mpr (by ring))
  have h2 : ¬ ptMap g (k ∙ ![x, 0, 1]) ≤ kerLine 0 0 1 :=
    not_ptMap_le hg (fr_aff x 0) (fr_ker2 one_ne_zero) (lnMap_001 hg hc)
      (by rw [vec_le_kerLine]; norm_num)
  obtain ⟨s, t, hst⟩ := exists_aff hQ h2
  rw [hst, vec_le_kerLine] at h1
  have ht : t = 0 := by simpa using h1
  exact Classical.epsilon_spec (p := fun s => ptMap g (k ∙ ![x, 0, 1]) = k ∙ ![s, 0, 1])
    ⟨s, by rw [hst, ht]⟩

theorem ptMap_y (y : k) : ptMap g (k ∙ ![0, y, 1]) = k ∙ ![0, coordY g y, 1] := by
  have hQ := finrank_ptMap hg (fr_aff 0 y)
  have h1 : ptMap g (k ∙ ![0, y, 1]) ≤ kerLine 1 0 0 :=
    ptMap_le hg (fr_aff 0 y) (fr_ker0 one_ne_zero) (lnMap_100 hg hd)
      (vec_le_kerLine.mpr (by ring))
  have h2 : ¬ ptMap g (k ∙ ![0, y, 1]) ≤ kerLine 0 0 1 :=
    not_ptMap_le hg (fr_aff 0 y) (fr_ker2 one_ne_zero) (lnMap_001 hg hc)
      (by rw [vec_le_kerLine]; norm_num)
  obtain ⟨s, t, hst⟩ := exists_aff hQ h2
  rw [hst, vec_le_kerLine] at h1
  have hs : s = 0 := by simpa using h1
  exact Classical.epsilon_spec (p := fun t => ptMap g (k ∙ ![0, y, 1]) = k ∙ ![0, t, 1])
    ⟨t, by rw [hst, hs]⟩

theorem ptMap_aff (x y : k) :
    ptMap g (k ∙ ![x, y, 1]) = k ∙ ![coordX g x, coordY g y, 1] := by
  have hV : lnMap g (kerLine 1 0 (-x)) = kerLine 1 0 (-coordX g x) :=
    lnMap_eq_of_two hg (fr_aff x 0) (fr_vec1 one_ne_zero) (fr_ker0 one_ne_zero)
      (fr_ker0 one_ne_zero)
      (ne_of_not_le_of_le (L := kerLine 0 0 1) (by rw [vec_le_kerLine]; norm_num)
        (vec_le_kerLine.mpr (by ring)))
      (ptMap_x hg hc hd x) (ptMap_e1 hg hc hd) (vec_le_kerLine.mpr (by ring))
      (vec_le_kerLine.mpr (by ring)) (vec_le_kerLine.mpr (by ring))
      (vec_le_kerLine.mpr (by ring))
  have hH : lnMap g (kerLine 0 1 (-y)) = kerLine 0 1 (-coordY g y) :=
    lnMap_eq_of_two hg (fr_aff 0 y) (fr_inf 0) (fr_ker1 one_ne_zero) (fr_ker1 one_ne_zero)
      (ne_of_not_le_of_le (L := kerLine 0 0 1) (by rw [vec_le_kerLine]; norm_num)
        (vec_le_kerLine.mpr (by ring)))
      (ptMap_y hg hc hd y) (ptMap_e0 hg hc) (vec_le_kerLine.mpr (by ring))
      (vec_le_kerLine.mpr (by ring)) (vec_le_kerLine.mpr (by ring))
      (vec_le_kerLine.mpr (by ring))
  exact ptMap_eq_of_two hg (fr_aff x y) (fr_aff _ _) (fr_ker0 one_ne_zero) (fr_ker1 one_ne_zero)
    (ne_of_le_of_not_le' (P := k ∙ ![0, 1, 0]) (vec_le_kerLine.mpr (by ring))
      (by rw [vec_le_kerLine]; norm_num))
    hV hH (vec_le_kerLine.mpr (by ring)) (vec_le_kerLine.mpr (by ring))
    (vec_le_kerLine.mpr (by ring)) (vec_le_kerLine.mpr (by ring))

theorem coordX_zero : coordX g 0 = 0 := by
  have h := ptMap_x hg hc hd 0
  rw [ptMap_e2 hg hd] at h
  exact ((vec_eq_of_span_eq one_ne_zero h).1).symm

theorem coordY_zero : coordY g 0 = 0 := by
  have h := ptMap_y hg hc hd 0
  rw [ptMap_e2 hg hd] at h
  exact ((vec_eq_of_span_eq one_ne_zero h).2).symm

theorem coordX_inj {x x' : k} (h : coordX g x = coordX g x') : x = x' := by
  have h' : ptMap g (k ∙ ![x, 0, 1]) = ptMap g (k ∙ ![x', 0, 1]) := by
    rw [ptMap_x hg hc hd, ptMap_x hg hc hd, h]
  rw [ptMap_inj hg (fr_aff x 0) (fr_aff x' 0)] at h'
  exact (vec_eq_of_span_eq one_ne_zero h').1

theorem coordY_inj {y y' : k} (h : coordY g y = coordY g y') : y = y' := by
  have h' : ptMap g (k ∙ ![0, y, 1]) = ptMap g (k ∙ ![0, y', 1]) := by
    rw [ptMap_y hg hc hd, ptMap_y hg hc hd, h]
  rw [ptMap_inj hg (fr_aff 0 y) (fr_aff 0 y')] at h'
  exact (vec_eq_of_span_eq one_ne_zero h').2

theorem coordX_one_ne_zero : coordX g 1 ≠ 0 := fun h =>
  one_ne_zero (coordX_inj hg hc hd (h.trans (coordX_zero hg hc hd).symm))

theorem coordY_one_ne_zero : coordY g 1 ≠ 0 := fun h =>
  one_ne_zero (coordY_inj hg hc hd (h.trans (coordY_zero hg hc hd).symm))

theorem lnMap_diag :
    lnMap g (kerLine 1 (-1) 0) = kerLine (coordY g 1) (-coordX g 1) 0 := by
  have ha := coordX_one_ne_zero hg hc hd
  exact lnMap_eq_of_two hg (fr_aff 0 0) (fr_aff 1 1) (fr_ker0 one_ne_zero)
    (fr_ker1 (neg_ne_zero.mpr ha)) (fun h => ha (vec_eq_of_span_eq one_ne_zero h).1.symm)
    (ptMap_e2 hg hd) (ptMap_aff hg hc hd 1 1) (vec_le_kerLine.mpr (by ring))
    (vec_le_kerLine.mpr (by ring)) (vec_le_kerLine.mpr (by ring))
    (vec_le_kerLine.mpr (by ring))

theorem coordX_eq (t : k) : coordX g t = coordX g 1 * semi g t := by
  unfold semi
  rw [← mul_assoc, mul_inv_cancel₀ (coordX_one_ne_zero hg hc hd), one_mul]

theorem coordY_eq (t : k) : coordY g t = coordY g 1 * semi g t := by
  have ha := coordX_one_ne_zero hg hc hd
  have h := ptMap_le hg (fr_aff t t) (fr_ker0 one_ne_zero) (lnMap_diag hg hc hd)
    (vec_le_kerLine.mpr (by ring))
  rw [ptMap_aff hg hc hd, vec_le_kerLine] at h
  unfold semi
  field_simp
  linear_combination -h

theorem semi_one : semi g 1 = 1 := by
  unfold semi
  exact inv_mul_cancel₀ (coordX_one_ne_zero hg hc hd)

theorem semi_zero : semi g 0 = 0 := by
  unfold semi
  rw [coordX_zero hg hc hd, mul_zero]

theorem ptMap_aff' (x y : k) :
    ptMap g (k ∙ ![x, y, 1]) = k ∙ ![coordX g 1 * semi g x, coordY g 1 * semi g y, 1] := by
  rw [ptMap_aff hg hc hd, coordX_eq hg hc hd x, coordY_eq hg hc hd y]

theorem ptMap_inf_one : ptMap g (k ∙ ![1, 1, 0]) = k ∙ ![coordX g 1, coordY g 1, 0] := by
  have ha := coordX_one_ne_zero hg hc hd
  exact ptMap_eq_of_two hg (fr_inf 1) (fr_vec0 ha) (fr_ker0 one_ne_zero) (fr_ker2 one_ne_zero)
    (ne_of_le_of_not_le' (P := k ∙ ![0, 0, 1]) (vec_le_kerLine.mpr (by ring))
      (by rw [vec_le_kerLine]; norm_num))
    (lnMap_diag hg hc hd) (lnMap_001 hg hc) (vec_le_kerLine.mpr (by ring))
    (vec_le_kerLine.mpr (by ring)) (vec_le_kerLine.mpr (by ring))
    (vec_le_kerLine.mpr (by ring))

theorem semi_add (x t : k) : semi g (x + t) = semi g x + semi g t := by
  have ha := coordX_one_ne_zero hg hc hd
  have hb := coordY_one_ne_zero hg hc hd
  have hQ : ptMap g (k ∙ ![0, t, 1]) = k ∙ ![0, coordY g 1 * semi g t, 1] := by
    rw [ptMap_aff' hg hc hd, semi_zero hg hc hd, mul_zero]
  have hS : lnMap g (kerLine 1 (-1) t) =
      kerLine (coordY g 1) (-coordX g 1) (coordX g 1 * coordY g 1 * semi g t) :=
    lnMap_eq_of_two hg (fr_inf 1) (fr_aff 0 t) (fr_ker0 one_ne_zero) (fr_ker0 hb)
      (ne_of_not_le_of_le (L := kerLine 0 0 1) (by rw [vec_le_kerLine]; norm_num)
        (vec_le_kerLine.mpr (by ring))).symm
      (ptMap_inf_one hg hc hd) hQ (vec_le_kerLine.mpr (by ring))
      (vec_le_kerLine.mpr (by ring)) (vec_le_kerLine.mpr (by ring))
      (vec_le_kerLine.mpr (by ring))
  have h := ptMap_le hg (fr_aff x (x + t)) (fr_ker0 one_ne_zero) hS
    (vec_le_kerLine.mpr (by ring))
  rw [ptMap_aff' hg hc hd, vec_le_kerLine] at h
  have hab : coordX g 1 * coordY g 1 ≠ 0 := mul_ne_zero ha hb
  have : coordX g 1 * coordY g 1 * (semi g x + semi g t - semi g (x + t)) = 0 := by
    linear_combination h
  exact (sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_left hab)).symm

theorem lnMap_slope (t : k) :
    lnMap g (kerLine t (-1) 0) = kerLine (coordY g 1 * semi g t) (-coordX g 1) 0 := by
  have ha := coordX_one_ne_zero hg hc hd
  have hQ : ptMap g (k ∙ ![1, t, 1]) = k ∙ ![coordX g 1, coordY g 1 * semi g t, 1] := by
    rw [ptMap_aff' hg hc hd, semi_one hg hc hd, mul_one]
  exact lnMap_eq_of_two hg (fr_aff 0 0) (fr_aff 1 t) (fr_ker1 (neg_ne_zero.mpr one_ne_zero))
    (fr_ker1 (neg_ne_zero.mpr ha)) (fun h => ha (vec_eq_of_span_eq one_ne_zero h).1.symm)
    (ptMap_e2 hg hd) hQ (vec_le_kerLine.mpr (by ring)) (vec_le_kerLine.mpr (by ring))
    (vec_le_kerLine.mpr (by ring)) (vec_le_kerLine.mpr (by ring))

theorem semi_mul (t x : k) : semi g (t * x) = semi g t * semi g x := by
  have ha := coordX_one_ne_zero hg hc hd
  have hb := coordY_one_ne_zero hg hc hd
  have h := ptMap_le hg (fr_aff x (t * x)) (fr_ker1 (neg_ne_zero.mpr one_ne_zero))
    (lnMap_slope hg hc hd t) (vec_le_kerLine.mpr (by ring))
  rw [ptMap_aff' hg hc hd, vec_le_kerLine] at h
  have hab : coordX g 1 * coordY g 1 ≠ 0 := mul_ne_zero ha hb
  have : coordX g 1 * coordY g 1 * (semi g t * semi g x - semi g (t * x)) = 0 := by
    linear_combination h
  exact (sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_left hab)).symm

theorem ptMap_inf (t : k) :
    ptMap g (k ∙ ![1, t, 0]) = k ∙ ![coordX g 1, coordY g 1 * semi g t, 0] := by
  have ha := coordX_one_ne_zero hg hc hd
  exact ptMap_eq_of_two hg (fr_inf t) (fr_vec0 ha) (fr_ker1 (neg_ne_zero.mpr one_ne_zero))
    (fr_ker2 one_ne_zero)
    (ne_of_le_of_not_le' (P := k ∙ ![0, 0, 1]) (vec_le_kerLine.mpr (by ring))
      (by rw [vec_le_kerLine]; norm_num))
    (lnMap_slope hg hc hd t) (lnMap_001 hg hc) (vec_le_kerLine.mpr (by ring))
    (vec_le_kerLine.mpr (by ring)) (vec_le_kerLine.mpr (by ring))
    (vec_le_kerLine.mpr (by ring))

theorem semi_surjective : Function.Surjective (semi g) := by
  intro s
  have ha := coordX_one_ne_zero hg hc hd
  obtain ⟨Q, hQ, hQe⟩ := exists_ptMap_eq hg (fr_aff (coordX g 1 * s) 0)
  have h1 : Q ≤ kerLine 0 1 0 := by
    refine (ptMap_le_lnMap_iff hg hQ (fr_ker1 one_ne_zero)).mp ?_
    rw [hQe, lnMap_010 hg hc hd]
    exact vec_le_kerLine.mpr (by ring)
  have h2 : ¬ Q ≤ kerLine 0 0 1 := by
    intro h
    have := (ptMap_le_lnMap_iff hg hQ (fr_ker2 one_ne_zero)).mpr h
    rw [hQe, lnMap_001 hg hc, vec_le_kerLine] at this
    norm_num at this
  obtain ⟨x, y, rfl⟩ := exists_aff hQ h2
  rw [vec_le_kerLine] at h1
  have hy : y = 0 := by simpa using h1
  subst hy
  refine ⟨x, ?_⟩
  rw [ptMap_x hg hc hd] at hQe
  have hx := (vec_eq_of_span_eq one_ne_zero hQe).1
  unfold semi
  rw [hx, ← mul_assoc, inv_mul_cancel₀ ha, one_mul]

theorem exists_ringEquiv : ∃ σ : k ≃+* k, ∀ t, σ t = semi g t := by
  let f : k →+* k :=
    { toFun := semi g
      map_one' := semi_one hg hc hd
      map_mul' := semi_mul hg hc hd
      map_zero' := semi_zero hg hc hd
      map_add' := semi_add hg hc hd }
  exact ⟨RingEquiv.ofBijective f ⟨f.injective, semi_surjective hg hc hd⟩, fun _ => rfl⟩

theorem exists_ptMap_eq_planeDiagFun : ∃ (a b : kˣ) (σ : k ≃+* k),
    ∀ v : Fin 3 → k, v ≠ 0 → ptMap g (k ∙ v) = k ∙ planeDiagFun a b σ v := by
  have ha := coordX_one_ne_zero hg hc hd
  have hb := coordY_one_ne_zero hg hc hd
  obtain ⟨σ, hσ⟩ := exists_ringEquiv hg hc hd
  refine ⟨Units.mk0 _ ha, Units.mk0 _ hb, σ, fun v hv0 => ?_⟩
  have hdiag : planeDiagFun (Units.mk0 _ ha) (Units.mk0 _ hb) σ v =
      ![coordX g 1 * σ (v 0), coordY g 1 * σ (v 1), σ (v 2)] := rfl
  rw [hdiag]
  by_cases h2 : v 2 = 0
  · by_cases h0 : v 0 = 0
    · have h1 : v 1 ≠ 0 := by
        intro h1
        apply hv0
        ext i
        fin_cases i <;> simp [h0, h1, h2]
      have hv : k ∙ v = k ∙ ![0, 1, 0] := span_eq_span_of_eq_smul h1 (by
        ext i
        fin_cases i <;> simp [h0, h2])
      rw [hv, ptMap_e1 hg hc hd, h0, h2, map_zero, mul_zero]
      refine (span_eq_span_of_eq_smul (c := coordY g 1 * σ (v 1))
        (mul_ne_zero hb ((map_ne_zero σ).mpr h1)) ?_).symm
      ext i
      fin_cases i <;> simp
    · have hv : k ∙ v = k ∙ ![1, v 1 / v 0, 0] := span_eq_span_of_eq_smul h0 (by
        ext i
        fin_cases i <;> simp [h0, h2, mul_div_cancel₀])
      rw [hv, ptMap_inf hg hc hd, ← hσ, h2, map_zero]
      refine (span_eq_span_of_eq_smul (c := σ (v 0)) ((map_ne_zero σ).mpr h0) ?_).symm
      have hv1 : σ (v 1) = σ (v 1 / v 0) * σ (v 0) := by
        rw [← map_mul, div_mul_cancel₀ _ h0]
      ext i
      fin_cases i
      · simp only [Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero, Pi.smul_apply, smul_eq_mul]
        ring
      · simp only [Fin.mk_one, Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_zero,
          Pi.smul_apply, smul_eq_mul]
        rw [hv1]
        ring
      · simp
  · have hv : k ∙ v = k ∙ ![v 0 / v 2, v 1 / v 2, 1] := span_eq_span_of_eq_smul h2 (by
      ext i
      fin_cases i <;> simp [h2, mul_div_cancel₀])
    rw [hv, ptMap_aff' hg hc hd, ← hσ, ← hσ]
    refine (span_eq_span_of_eq_smul (c := σ (v 2)) ((map_ne_zero σ).mpr h2) ?_).symm
    have hv0' : σ (v 0) = σ (v 0 / v 2) * σ (v 2) := by
      rw [← map_mul, div_mul_cancel₀ _ h2]
    have hv1 : σ (v 1) = σ (v 1 / v 2) * σ (v 2) := by
      rw [← map_mul, div_mul_cancel₀ _ h2]
    ext i
    fin_cases i
    · simp only [Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero, Pi.smul_apply, smul_eq_mul]
      rw [hv0']
      ring
    · simp only [Fin.mk_one, Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_zero,
        Pi.smul_apply, smul_eq_mul]
      rw [hv1]
      ring
    · simp

theorem exists_planeDiagPerm_eq : ∃ (a b : kˣ) (σ : k ≃+* k), planeDiagPerm a b σ = g := by
  obtain ⟨a, b, σ, h⟩ := exists_ptMap_eq_planeDiagFun hg hc hd
  refine ⟨a, b, σ, eq_of_ptMap_eq (planeDiagPerm_mem_planeTypeAut a b σ) hg fun P hP => ?_⟩
  obtain ⟨v, hv0, rfl⟩ := exists_eq_span hP
  rw [ptMap_planeDiagPerm a b σ hv0, h v hv0]

end Coordinates

end ProjPlane

end CFSG.Monster.B.Geometry

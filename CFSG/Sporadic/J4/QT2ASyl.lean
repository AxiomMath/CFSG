module

public import CFSG.Sporadic.J4.QT2AMod
public import CFSG.Sporadic.J4.QT2AGen

public section

namespace CFSG.Sporadic.J4.QT2A

open CFSG.Sporadic.J4 CFSG.Sporadic.J4.Native CFSG.Sporadic.J4.QT Matrix

theorem wfR_spec {X : Array V2} (h : wfR X = true) : X.size = 112 ∧ ∀ x ∈ X, x.wf = true := by
  unfold wfR at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  refine ⟨h.1, fun x hx => ?_⟩
  obtain ⟨i, hi, rfl⟩ := Array.mem_iff_getElem.1 hx
  exact Array.all_eq_true.1 h.2 i hi

theorem wfR_of {X : Array V2} (hs : X.size = 112) (hw : ∀ x ∈ X, x.wf = true) :
    wfR X = true := by
  unfold wfR
  simp only [Bool.and_eq_true, beq_iff_eq]
  exact ⟨hs, Array.all_eq_true.2 fun i hi => hw _ (Array.getElem_mem hi)⟩

theorem wfR_mulRows {X Y : Array V2} (hX : wfR X = true) (hY : wfR Y = true) :
    wfR (mulRows X Y) = true := by
  obtain ⟨hXs, -⟩ := wfR_spec hX
  obtain ⟨-, hYw⟩ := wfR_spec hY
  exact wfR_of (by rw [mulRows_size, hXs]) (mulRows_wf X hYw)

theorem wfR_idRows : wfR idRows = true := wfR_of idRows_size idRows_wf

theorem wfR_powRows {X : Array V2} (hX : wfR X = true) (e : ℕ) : wfR (powRows X e) = true := by
  induction e with
  | zero => exact wfR_idRows
  | succ e ih => exact wfR_mulRows ih hX

theorem ne_of_eqRows_false {X Y : Array V2} (hX : wfR X = true) (hY : wfR Y = true)
    (h : eqRows X Y = false) : rowsMatrix X ≠ rowsMatrix Y := by
  obtain ⟨hXs, hXw⟩ := wfR_spec hX
  obtain ⟨hYs, hYw⟩ := wfR_spec hY
  exact rowsMatrix_ne_of_eqRows_false hXs hYs hXw hYw h

theorem allDistinct_spec : ∀ {l : List (Array V2)}, allDistinct l = true →
    ∀ (i j : ℕ) (hi : i < l.length) (hj : j < l.length), i ≠ j →
      eqRows l[i] l[j] = false
  | [], _, i, j, hi, _, _ => absurd hi (by simp)
  | x :: xs, h, i, j, hi, hj, hij => by
    unfold allDistinct at h
    rw [Bool.and_eq_true] at h
    obtain ⟨h1, h2⟩ := h
    rw [List.all_eq_true] at h1
    cases i with
    | zero =>
      cases j with
      | zero => exact absurd rfl hij
      | succ j =>
        have hj' : j < xs.length := by simpa using hj
        have := h1 (xs[j]'hj') (List.getElem_mem hj')
        simpa using this
    | succ i =>
      cases j with
      | zero =>
        have hi' : i < xs.length := by simpa using hi
        have := h1 (xs[i]'hi') (List.getElem_mem hi')
        simp only [Bool.not_eq_true'] at this
        simp only [List.getElem_cons_succ, List.getElem_cons_zero]
        rw [Bool.eq_false_iff] at this ⊢
        intro hh
        apply this
        rw [eqRows_iff] at hh ⊢
        exact hh.symm
      | succ j =>
        have := allDistinct_spec h2 i j (by simpa using hi) (by simpa using hj)
          (fun e => hij (by omega))
        simpa using this

theorem w5_ne_zero (s : String) : ∀ l ∈ w5 s, l ≠ 0 := by
  intro l hl
  unfold w5 at hl
  rw [List.mem_filterMap] at hl
  obtain ⟨ch, -, hch⟩ := hl
  split_ifs at hch with h1 h2
  · cases hch
    have : 'a'.toNat ≤ ch.toNat := h1.1
    omega
  · cases hch
    have : 'A'.toNat ≤ ch.toNat := h2.1
    omega

theorem invW_eq (w : List ℤ) : invW w = invWord w := rfl

theorem ne_zero_invW {w : List ℤ} (h : ∀ l ∈ w, l ≠ 0) : ∀ l ∈ invW w, l ≠ 0 := by
  intro l hl
  unfold invW at hl
  rw [List.mem_map] at hl
  obtain ⟨l', hl', rfl⟩ := hl
  have := h l' (List.mem_reverse.1 hl')
  omega

@[expose] noncomputable def aY : J := el5 aDw

@[expose] noncomputable def bY : J := el5 bDw

@[expose] noncomputable def cY : J := el5 cDw

@[expose] noncomputable def yJ (n : ℕ) : J := aY ^ (n / 9) * bY ^ ((n / 3) % 3) * cY ^ (n % 3)

theorem aDw_ne : ∀ l ∈ aDw, l ≠ 0 := by
  unfold aDw
  exact w5_ne_zero _

theorem bDw_ne : ∀ l ∈ bDw, l ≠ 0 := by
  unfold bDw
  exact w5_ne_zero _

theorem cY_eq : cY = aY⁻¹ * bY⁻¹ * aY * bY := by
  unfold cY aY bY el5 cDw
  rw [invW_eq, invW_eq, wordProd_append, wordProd_append, wordProd_append,
    wordProd_invWord _ _ aDw_ne, wordProd_invWord _ _ bDw_ne]

section Y

variable (hM : MatFacts)
include hM

theorem Mx_aY : Mx aY = rowsMatrix (wR aDw) := Mx_el5 hM aDw

theorem Mx_bY : Mx bY = rowsMatrix (wR bDw) := Mx_el5 hM bDw

theorem Mx_cY : Mx cY = rowsMatrix (wR cDw) := Mx_el5 hM cDw

theorem Mx_yJ (n : ℕ) : Mx (yJ n) = rowsMatrix (yEl n) := by
  simp only [yJ, yEl, map_mul, map_pow, Mx_aY hM, Mx_bY hM, Mx_cY hM, rowsMatrix_mulRows,
    rowsMatrix_powRows]

theorem mem_Cz_of_cmz {g : J} {R : Array V2} (hR : Mx g = rowsMatrix R) (h : cmz R = true) :
    g ∈ Cz := by
  unfold cmz at h
  have h1 := congrArg rowsMatrix (eqRows_iff.1 h)
  rw [rowsMatrix_mulRows, rowsMatrix_mulRows, ← hR, ← Mx_zJ hM, ← map_mul, ← map_mul] at h1
  exact mem_Cz.2 (Mx_injective h1).symm

omit hM in
theorem chkY_parts :
    cmz (wR aDw) = true ∧ cmz (wR bDw) = true ∧ wfR (wR aDw) = true ∧ wfR (wR bDw) = true ∧
    eqRows (yEl 0) idRows = true ∧ (∀ n < 27, wfR (yEl n) = true) ∧
    allDistinct ((List.range 27).map yEl) = true ∧
    (∀ n < 27, (∃ m < 27, eqRows (mulRows (yEl n) (wR aDw)) (yEl m) = true) ∧
      ∃ m < 27, eqRows (mulRows (yEl n) (wR bDw)) (yEl m) = true) := by
  have h := chkY_true
  unfold chkY at h
  simp only [Bool.and_eq_true, List.all_eq_true, List.mem_range, List.any_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩

omit hM in
theorem yJ_zero : yJ 0 = 1 := by simp [yJ]

theorem yJ_inj {n m : ℕ} (hn : n < 27) (hm : m < 27) (h : yJ n = yJ m) : n = m := by
  by_contra hne
  obtain ⟨-, -, -, -, -, hw, hd, -⟩ := chkY_parts
  have hd' := allDistinct_spec hd n m (by simpa using hn) (by simpa using hm) hne
  simp only [List.getElem_map, List.getElem_range] at hd'
  apply ne_of_eqRows_false (hw n hn) (hw m hm) hd'
  rw [← Mx_yJ hM, ← Mx_yJ hM, h]

theorem yJ_mul_gen {n : ℕ} (hn : n < 27) :
    (∃ m < 27, yJ n * aY = yJ m) ∧ ∃ m < 27, yJ n * bY = yJ m := by
  obtain ⟨-, -, -, -, -, -, -, hc⟩ := chkY_parts
  obtain ⟨⟨m, hm, hma⟩, ⟨m', hm', hmb⟩⟩ := hc n hn
  refine ⟨⟨m, hm, ?_⟩, ⟨m', hm', ?_⟩⟩
  · apply Mx_injective
    rw [map_mul, Mx_yJ hM, Mx_aY hM, ← rowsMatrix_mulRows, eqRows_iff.1 hma, Mx_yJ hM]
  · apply Mx_injective
    rw [map_mul, Mx_yJ hM, Mx_bY hM, ← rowsMatrix_mulRows, eqRows_iff.1 hmb, Mx_yJ hM]

@[expose] noncomputable def Ycl : Subgroup J := Subgroup.closure {aY, bY}

theorem Ycl_subset : (Ycl : Set J) ⊆ yJ '' Set.Iio 27 := by
  refine closure_subset_of_closed {aY, bY} _ ⟨0, by norm_num, yJ_zero⟩ ?_
  rintro _ ⟨n, hn, rfl⟩ g hg
  rcases hg with rfl | rfl
  · obtain ⟨m, hm, e⟩ := (yJ_mul_gen hM hn).1
    exact ⟨m, hm, e.symm⟩
  · obtain ⟨m, hm, e⟩ := (yJ_mul_gen hM hn).2
    exact ⟨m, hm, e.symm⟩

omit hM in
theorem aY_mem : aY ∈ Ycl := Subgroup.subset_closure (Set.mem_insert _ _)

omit hM in
theorem bY_mem : bY ∈ Ycl := Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)

omit hM in
theorem yJ_mem (n : ℕ) : yJ n ∈ Ycl := by
  have hc : cY ∈ Ycl := by
    rw [cY_eq]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _
      (Subgroup.inv_mem _ aY_mem) (Subgroup.inv_mem _ bY_mem)) aY_mem) bY_mem
  exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.pow_mem _ aY_mem _)
    (Subgroup.pow_mem _ bY_mem _)) (Subgroup.pow_mem _ hc _)

theorem card_Ycl :
    Nat.card Ycl = 27 := by
  have hset : (Ycl : Set J) = ↑((Finset.range 27).image yJ) := by
    ext x
    constructor
    · intro hx
      obtain ⟨n, hn, rfl⟩ := Ycl_subset hM hx
      exact Finset.mem_coe.2 (Finset.mem_image.2 ⟨n, Finset.mem_range.2 hn, rfl⟩)
    · intro hx
      obtain ⟨n, -, rfl⟩ := Finset.mem_image.1 (Finset.mem_coe.1 hx)
      exact yJ_mem n
  have h1 : Nat.card Ycl = ((Finset.range 27).image yJ).card := by
    rw [← Set.ncard_coe_finset, ← hset]
    exact Nat.card_coe_set_eq _
  rw [h1, Finset.card_image_of_injOn, Finset.card_range]
  intro n hn m hm h
  exact yJ_inj hM (Finset.mem_range.1 hn) (Finset.mem_range.1 hm) h

theorem aY_mem_Cz : aY ∈ Cz := by
  obtain ⟨h1, -⟩ := chkY_parts
  exact mem_Cz_of_cmz hM (Mx_aY hM) h1

theorem bY_mem_Cz : bY ∈ Cz := by
  obtain ⟨-, h2, -⟩ := chkY_parts
  exact mem_Cz_of_cmz hM (Mx_bY hM) h2

theorem Ycl_le_Cz : Ycl ≤ Cz := by
  rw [Ycl, Subgroup.closure_le]
  rintro _ (rfl | rfl)
  · exact aY_mem_Cz hM
  · exact bY_mem_Cz hM

end Y

@[expose] noncomputable def y5J : J := el5 y5w ^ y5e

@[expose] noncomputable def y7J : J := el5 y7w ^ y7e

@[expose] noncomputable def y11J : J := el5 y11w ^ y11e

@[expose] noncomputable def qJ (k : ℕ) : J := el5 (qGenW.getD k [])

section Yr

variable (hM : MatFacts)
include hM

omit hM in
theorem chkYr_parts {R : Array V2} {r : ℕ} (h : chkYr R r = true) :
    cmz R = true ∧ wfR R = true ∧ eqRows (powRows R r) idRows = true ∧
      eqRows R idRows = false := by
  unfold chkYr at h
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  exact ⟨h1, h2, h3, h4⟩

theorem Mx_y5J : Mx y5J = rowsMatrix (y5R ()) := by
  simp only [y5J, y5R, map_pow, Mx_el5 hM y5w, rowsMatrix_powRows]

theorem Mx_y7J : Mx y7J = rowsMatrix (y7R ()) := by
  simp only [y7J, y7R, map_pow, Mx_el5 hM y7w, rowsMatrix_powRows]

theorem Mx_y11J : Mx y11J = rowsMatrix (y11R ()) := by
  simp only [y11J, y11R, map_pow, Mx_el5 hM y11w, rowsMatrix_powRows]

theorem Mx_qJ (k : ℕ) : Mx (qJ k) = rowsMatrix (qR k) := Mx_el5 hM (qGenW.getD k [])

theorem y_prime_facts {y : J} {R : Array V2} {r : ℕ} [Fact r.Prime] (hR : Mx y = rowsMatrix R)
    (h : chkYr R r = true) : y ∈ Cz ∧ orderOf y = r := by
  obtain ⟨h1, h2, h3, h4⟩ := chkYr_parts h
  refine ⟨mem_Cz_of_cmz hM hR h1, orderOf_eq_prime ?_ ?_⟩
  · apply Mx_injective
    rw [map_pow, hR, ← rowsMatrix_powRows, eqRows_iff.1 h3, rowsMatrix_idRows, map_one]
  · intro hy1
    apply ne_of_eqRows_false h2 wfR_idRows h4
    rw [← hR, hy1, map_one, rowsMatrix_idRows]

theorem pow_notMem_Qz {y : J} {R : Array V2} {r : ℕ} (hR : Mx y = rowsMatrix R)
    (h : chkNotQzPow R r = true) {k : ℕ} (hk1 : 1 ≤ k) (hk : k < r) : y ^ k ∉ Qz := by
  unfold chkNotQzPow at h
  have h1 := List.all_eq_true.1 h (k - 1) (List.mem_range.2 (by omega))
  refine not_mem_Qz_of_notQz hM (R := powRows R (k - 1 + 1)) ?_ h1
  rw [Nat.sub_add_cancel hk1, map_pow, hR, rowsMatrix_powRows]

omit hM in
theorem nocomm_ne {g y : J} {X Y : Array V2} (hg : Mx g = rowsMatrix X)
    (hy : Mx y = rowsMatrix Y) (hX : wfR X = true) (hY : wfR Y = true) (h : nocomm X Y = true) :
    g * y ≠ y * g := by
  intro e
  have h1 := congrArg Mx e
  rw [map_mul, map_mul, hg, hy, ← rowsMatrix_mulRows, ← rowsMatrix_mulRows] at h1
  refine ne_of_eqRows_false (wfR_mulRows hX hY) (wfR_mulRows hY hX) ?_ h1
  unfold nocomm at h
  simpa using h

theorem qJ_mem_Qz {k : ℕ} (hk : k < 12) : qJ k ∈ Qz := by
  have h := chkQgens_true
  unfold chkQgens at h
  rw [Bool.and_eq_true, List.all_eq_true] at h
  exact mem_Qz_of_inQz hM (Mx_qJ hM k) (h.2 k (List.mem_range.2 hk))

end Yr

end CFSG.Sporadic.J4.QT2A

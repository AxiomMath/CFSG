module

public import CFSG.Quasithin.AppendixH.H15.CocodeTwoKData
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Milestones.ASVolI.H13
public import CFSG.Quasithin.Background.HMathieuFacts22Base

public section

namespace CFSG.ASVolI.AppH

open CFSG.Quasithin CFSG.Quasithin.H.Mathieu CFSG.ASVolI.ChH

variable {V : Type*} [CommGroup V]

@[expose] def ActsByMats {n : ℕ} (c : MaskCoords V n) (A : Subgroup (MulAut V))
    (cols : List (List ℕ)) : Prop :=
  (∀ g ∈ A, ∃ t < cols.length, ∀ m, g (c.vm m) = c.vm (actM (cols.getD t []) m)) ∧
  (∀ t < cols.length, ∃ g ∈ A, ∀ m, g (c.vm m) = c.vm (actM (cols.getD t []) m))

section Engine

variable {D : KData} {c : MaskCoords V D.n} {A : Subgroup (MulAut V)}

private def idCols (n : ℕ) : List ℕ := (List.range n).map fun j => 2 ^ j

private theorem idCols_getD {n j : ℕ} (hj : j < n) : (idCols n).getD j 0 = 2 ^ j := by
  rw [List.getD_eq_getElem (l := idCols n) (d := 0) (n := j) (by simpa [idCols] using hj)]
  simp only [idCols, List.getElem_map, List.getElem_range]

private theorem eq_idCols_of_getD {n : ℕ} {cs : List ℕ} (hlen : cs.length = n)
    (h : ∀ j < n, cs.getD j 0 = 2 ^ j) : cs = idCols n := by
  refine List.ext_getElem ?_ ?_
  · rw [hlen]; simp [idCols]
  · intro j h1 h2
    rw [← List.getD_eq_getElem (l := cs) (d := 0) (n := j) h1, h j (hlen ▸ h1),
      ← List.getD_eq_getElem (l := idCols n) (d := 0) (n := j) h2,
      idCols_getD (by simpa [idCols] using h2)]

private theorem actM_zero (cs : List ℕ) : actM cs 0 = 0 := (actM_xor cs).map_zero

private theorem actM_two_pow : ∀ (cs : List ℕ) (j : ℕ), actM cs (2 ^ j) = cs.getD j 0
  | [], j => by cases j <;> simp [actM, List.getD]
  | c :: cs, j => by
    cases j with
    | zero =>
      rw [pow_zero, actM]
      rw [if_pos (by decide : (1 : ℕ) % 2 = 1), (by decide : (1 : ℕ) / 2 = 0),
        actM_zero, Nat.xor_zero]
      simp [List.getD]
    | succ j =>
      rw [pow_succ, actM]
      rw [Nat.mul_mod_left, if_neg (by decide : ¬ ((0 : ℕ) = 1)), Nat.zero_xor,
        Nat.mul_div_cancel (2 ^ j) (by norm_num : 0 < 2), actM_two_pow cs j,
        List.getD_cons_succ]

private theorem actM_idCols (m : ℕ) : actM (idCols D.n) m = m % 2 ^ D.n := by
  have hid : idCols D.n = matOf D.n (id : ℕ → ℕ) := rfl
  rw [hid, ← actM_mod, length_matOf]
  exact actM_matOf (f := (id : ℕ → ℕ)) (fun a b => rfl) D.n (m % 2 ^ D.n)
    (Nat.mod_lt _ (Nat.two_pow_pos D.n))

private theorem good_parts (hD : D.good = true) :
    D.chkCols = true ∧ D.chkAb = true ∧ D.chkLU = true ∧ D.chkCard = true ∧
      D.chkCnt = true ∧ D.chkEx = true ∧ D.chkXi = true ∧ D.chkXb = true ∧
      D.chkTV = true ∧ D.chkCt = true := by
  have h := hD
  simp only [KData.good, Bool.and_eq_true] at h
  tauto

private theorem chkCols_of_good (hD : D.good = true) : D.chkCols = true := (good_parts hD).1
private theorem chkAb_of_good (hD : D.good = true) : D.chkAb = true := (good_parts hD).2.1
private theorem chkLU_of_good (hD : D.good = true) : D.chkLU = true := (good_parts hD).2.2.1
private theorem chkCard_of_good (hD : D.good = true) : D.chkCard = true := (good_parts hD).2.2.2.1
private theorem chkEx_of_good (hD : D.good = true) : D.chkEx = true :=
  (good_parts hD).2.2.2.2.2.1

private theorem good_cols_len16 (hD : D.good = true) : D.cols.length = 16 := by
  have h := chkCols_of_good hD
  simp only [KData.chkCols, Bool.and_eq_true, decide_eq_true_eq] at h
  exact h.1.1.1

private theorem good_cols_nodup (hD : D.good = true) : D.cols.Nodup := by
  have h := chkCols_of_good hD
  simp only [KData.chkCols, Bool.and_eq_true, decide_eq_true_eq] at h
  exact h.1.1.2

private theorem good_cols_zero (hD : D.good = true) : D.cols.getD 0 [] = idCols D.n := by
  have h := chkCols_of_good hD
  simp only [KData.chkCols, Bool.and_eq_true, decide_eq_true_eq] at h
  exact h.1.2

private theorem good_cols_all (hD : D.good = true) {c' : List ℕ} (hc : c' ∈ D.cols) :
    c'.length = D.n ∧ ∀ x ∈ c', x < 2 ^ D.n := by
  have h := chkCols_of_good hD
  simp only [KData.chkCols, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
  exact h.2 c' hc

private theorem good_cols_getD_mem (hD : D.good = true) {t : ℕ} (ht : t < 16) :
    D.cols.getD t [] ∈ D.cols := by
  have hlen : D.cols.length = 16 := good_cols_len16 hD
  rw [List.getD_eq_getElem (l := D.cols) (d := []) (n := t) (by rw [hlen]; exact ht)]
  exact List.getElem_mem _

private theorem good_cols_getD_len (hD : D.good = true) {t : ℕ} (ht : t < 16) :
    (D.cols.getD t []).length = D.n :=
  (good_cols_all hD (good_cols_getD_mem hD ht)).1

private theorem good_cols_getD_lt (hD : D.good = true) {t : ℕ} (ht : t < 16) :
    ∀ x ∈ D.cols.getD t [], x < 2 ^ D.n :=
  (good_cols_all hD (good_cols_getD_mem hD ht)).2

private theorem good_ab_comm (hD : D.good = true) :
    ∀ s < 16, ∀ t < 16,
      (D.cols.getD s []).map (actM (D.cols.getD t [])) =
        (D.cols.getD t []).map (actM (D.cols.getD s [])) := by
  have h := chkAb_of_good hD
  simp only [KData.chkAb, Bool.and_eq_true, List.all_eq_true, List.mem_range,
    beq_iff_eq] at h
  exact fun s hs t ht => (h s hs t ht).1

private theorem good_ab_sq (hD : D.good = true) :
    ∀ t < 16, (D.cols.getD t []).map (actM (D.cols.getD t [])) = idCols D.n := by
  have h := chkAb_of_good hD
  simp only [KData.chkAb, Bool.and_eq_true, List.all_eq_true, List.mem_range,
    beq_iff_eq] at h
  exact fun t ht => (h t ht t ht).2

private theorem good_lu_spec (hD : D.good = true) {m : ℕ} (hm : m < 2 ^ D.n) :
    D.inU m = true ↔ ∀ t < 16, D.fixes t m = true := by
  have h := chkLU_of_good hD
  simp only [KData.chkLU, List.all_eq_true, List.mem_range, beq_iff_eq] at h
  rw [h m hm]
  simp only [List.all_eq_true, List.mem_range]

private theorem good_card_fst (hD : D.good = true) :
    ((List.range (2 ^ D.n)).filter D.inU).length = 2 ^ D.dU := by
  have h := chkCard_of_good hD
  simp only [KData.chkCard, Bool.and_eq_true, decide_eq_true_eq] at h
  exact h.1

private theorem good_ex_spec (hD : D.good = true) :
    ∀ i < 15, ∃ m < 2 ^ D.n, D.fixes (i + 1) m = true ∧ D.inU m = false := by
  have h := chkEx_of_good hD
  simp only [KData.chkEx, List.all_eq_true, List.mem_range, List.any_eq_true,
    Bool.and_eq_true] at h
  intro i hi
  obtain ⟨m, hm, hfix, hnot⟩ := h i hi
  exact ⟨m, hm, hfix, Bool.eq_false_of_not_eq_true' hnot⟩

theorem engine_cols_length (hD : D.good = true) : D.cols.length = 16 :=
  good_cols_len16 hD

theorem engine_index (hD : D.good = true) (hA : ActsByMats c A D.cols) {g : MulAut V} (hg : g ∈ A) :
    ∃ t < 16, ∀ m, g (c.vm m) = c.vm (actM (D.cols.getD t []) m) := by
  obtain ⟨t, ht, h⟩ := hA.1 g hg
  exact ⟨t, by rwa [engine_cols_length hD] at ht, h⟩

theorem engine_exists_elem (hD : D.good = true) (hA : ActsByMats c A D.cols) {t : ℕ} (ht : t < 16) :
    ∃ g ∈ A, ∀ m, g (c.vm m) = c.vm (actM (D.cols.getD t []) m) :=
  hA.2 t (by rwa [engine_cols_length hD])

theorem engine_index_unique (hD : D.good = true) {g : MulAut V} {s t : ℕ} (hs : s < 16)
    (ht : t < 16) (hgs : ∀ m, g (c.vm m) = c.vm (actM (D.cols.getD s []) m))
    (hgt : ∀ m, g (c.vm m) = c.vm (actM (D.cols.getD t []) m)) : s = t := by
  have hlen_s : (D.cols.getD s []).length = D.n := good_cols_getD_len hD hs
  have hlen_t : (D.cols.getD t []).length = D.n := good_cols_getD_len hD ht
  have hfun : ∀ j < D.n,
      (D.cols.getD s []).getD j 0 = (D.cols.getD t []).getD j 0 := by
    intro j hj
    rw [← actM_two_pow, ← actM_two_pow]
    exact c.vm_inj _ _ (actM_lt (good_cols_getD_lt hD hs) _) (actM_lt (good_cols_getD_lt hD ht) _)
      ((hgs (2 ^ j)).symm.trans (hgt (2 ^ j)))
  have hcols : D.cols.getD s [] = D.cols.getD t [] := by
    refine List.ext_getElem ?_ ?_
    · rw [hlen_s, hlen_t]
    · intro j h1 h2
      rw [← List.getD_eq_getElem (l := D.cols.getD s []) (d := 0) (n := j) h1,
        ← List.getD_eq_getElem (l := D.cols.getD t []) (d := 0) (n := j) h2]
      exact hfun j (hlen_s ▸ h1)
  have hs' : s < D.cols.length := by rw [engine_cols_length hD]; exact hs
  have ht' : t < D.cols.length := by rw [engine_cols_length hD]; exact ht
  rw [List.getD_eq_getElem (l := D.cols) (d := []) (n := s) hs',
    List.getD_eq_getElem (l := D.cols) (d := []) (n := t) ht'] at hcols
  exact (good_cols_nodup hD).getElem_inj_iff.1 hcols

theorem engine_one_iff (hD : D.good = true) {g : MulAut V} {t : ℕ} (ht : t < 16)
    (hg : ∀ m, g (c.vm m) = c.vm (actM (D.cols.getD t []) m)) : g = 1 ↔ t = 0 := by
  constructor
  · intro hg1
    have hval : ∀ j < D.n, (D.cols.getD t []).getD j 0 = 2 ^ j := by
      intro j hj
      rw [← actM_two_pow]
      have h := hg (2 ^ j)
      rw [hg1, MulAut.one_apply] at h
      exact c.vm_inj _ _ (actM_lt (good_cols_getD_lt hD ht) _)
        (Nat.pow_lt_pow_right (by norm_num) hj) h.symm
    have ht_id : D.cols.getD t [] = idCols D.n :=
      eq_idCols_of_getD (good_cols_getD_len hD ht) hval
    have hcols : D.cols.getD t [] = D.cols.getD 0 [] := by
      rw [ht_id, good_cols_zero hD]
    have ht' : t < D.cols.length := by rw [engine_cols_length hD]; exact ht
    have h0' : 0 < D.cols.length := by rw [engine_cols_length hD]; norm_num
    rw [List.getD_eq_getElem (l := D.cols) (d := []) (n := t) ht',
      List.getD_eq_getElem (l := D.cols) (d := []) (n := 0) h0'] at hcols
    exact (good_cols_nodup hD).getElem_inj_iff.1 hcols
  · intro ht0
    rw [ht0] at hg
    apply MulEquiv.ext
    intro v
    obtain ⟨m, hm, rfl⟩ := c.vm_surj v
    rw [hg m, MulAut.one_apply, good_cols_zero hD, actM_idCols, c.vm_mod]

theorem engine_fixes_iff (hD : D.good = true) {g : MulAut V} {t : ℕ} (ht : t < 16)
    (hg : ∀ m, g (c.vm m) = c.vm (actM (D.cols.getD t []) m)) {m : ℕ} (hm : m < 2 ^ D.n) :
    g (c.vm m) = c.vm m ↔ D.fixes t m = true := by
  rw [KData.fixes, beq_iff_eq]
  constructor
  · intro h
    exact c.vm_inj _ _ (actM_lt (good_cols_getD_lt hD ht) m) hm ((hg m).symm.trans h)
  · intro h
    rw [hg m, h]

theorem engine_card (hD : D.good = true) (hA : ActsByMats c A D.cols) : Nat.card A = 16 := by
  classical
  let f : ↥A → Fin 16 := fun g =>
    ⟨(engine_index hD hA g.2).choose, (engine_index hD hA g.2).choose_spec.1⟩
  have hf_spec : ∀ g : ↥A, ∀ m, (g : MulAut V) (c.vm m) =
      c.vm (actM (D.cols.getD (f g).val []) m) :=
    fun g => (engine_index hD hA g.2).choose_spec.2
  have hf_inj : Function.Injective f := by
    intro g h hgh
    apply Subtype.ext
    apply MulEquiv.ext
    intro v
    obtain ⟨m, hm, rfl⟩ := c.vm_surj v
    rw [hf_spec g m, hf_spec h m, hgh]
  have hf_surj : Function.Surjective f := by
    intro t
    obtain ⟨g, hg, hgs⟩ := engine_exists_elem hD hA t.2
    refine ⟨⟨g, hg⟩, ?_⟩
    apply Fin.ext
    exact engine_index_unique hD (f ⟨g, hg⟩).2 t.2 (hf_spec ⟨g, hg⟩) hgs
  have hcard := Nat.card_eq_of_bijective f ⟨hf_inj, hf_surj⟩
  rw [Nat.card_fin] at hcard
  exact hcard

theorem engine_rk (hD : D.good = true) (hA : ActsByMats c A D.cols) : rk ↥A = 4 := by
  refine rk_eq_of_natCard 4 ?_
  rw [engine_card hD hA]
  norm_num

theorem engine_isElemAbelian2 (hD : D.good = true) (hA : ActsByMats c A D.cols) :
    IsElemAbelian2 A := by
  constructor
  · intro a ha b hb
    obtain ⟨s, hs, hsa⟩ := engine_index hD hA ha
    obtain ⟨t, ht, htb⟩ := engine_index hD hA hb
    apply MulEquiv.ext
    intro v
    obtain ⟨m, hm, rfl⟩ := c.vm_surj v
    rw [MulAut.mul_apply, MulAut.mul_apply]
    rw [htb m, hsa (actM (D.cols.getD t []) m), hsa m,
      htb (actM (D.cols.getD s []) m)]
    rw [← actM_map (actM_xor (D.cols.getD s [])) (D.cols.getD t []) m,
      ← actM_map (actM_xor (D.cols.getD t [])) (D.cols.getD s []) m,
      good_ab_comm hD s hs t ht]
  · intro a ha
    obtain ⟨s, hs, hsa⟩ := engine_index hD hA ha
    apply MulEquiv.ext
    intro v
    obtain ⟨m, hm, rfl⟩ := c.vm_surj v
    rw [pow_two, MulAut.mul_apply, MulAut.one_apply, hsa m,
      hsa (actM (D.cols.getD s []) m)]
    rw [← actM_map (actM_xor (D.cols.getD s [])) (D.cols.getD s []) m,
      good_ab_sq hD s hs, actM_idCols, c.vm_mod]

theorem engine_ne_bot (hD : D.good = true) (hA : ActsByMats c A D.cols) : A ≠ ⊥ := by
  intro hbot
  obtain ⟨g, hg, hgs⟩ := engine_exists_elem hD hA (t := 1) (by norm_num)
  have hg1 : g = 1 := by rw [hbot] at hg; simpa using hg
  have h10 : (1 : ℕ) = 0 := (engine_one_iff hD (by norm_num) hgs).1 hg1
  exact one_ne_zero h10

private theorem mem_fixV_iff (hD : D.good = true) (hA : ActsByMats c A D.cols) {m : ℕ}
    (hm : m < 2 ^ D.n) : c.vm m ∈ fixV A ↔ D.inU m = true := by
  rw [mem_fixV]
  constructor
  · intro hv
    rw [good_lu_spec hD hm]
    intro t ht
    obtain ⟨g, hg, hgs⟩ := engine_exists_elem hD hA ht
    have h1 : c.vm (actM (D.cols.getD t []) m) = c.vm m := (hgs m).symm.trans (hv g hg)
    have h2 : actM (D.cols.getD t []) m = m :=
      c.vm_inj _ _ (actM_lt (good_cols_getD_lt hD ht) m) hm h1
    rwa [KData.fixes, beq_iff_eq]
  · intro hu x hx
    obtain ⟨t, ht, htx⟩ := engine_index hD hA hx
    have hfix : actM (D.cols.getD t []) m = m := by
      have := (good_lu_spec hD hm).1 hu t ht
      rwa [KData.fixes, beq_iff_eq] at this
    rw [htx m, hfix]

theorem engine_mem_fixV (hD : D.good = true) (hA : ActsByMats c A D.cols) (v : V) :
    v ∈ fixV A ↔ ∃ m < 2 ^ D.n, v = c.vm m ∧ D.inU m = true := by
  constructor
  · intro hv
    obtain ⟨m, hm, hmv⟩ := c.vm_surj v
    exact ⟨m, hm, hmv.symm, (mem_fixV_iff hD hA hm).1 (hmv ▸ hv)⟩
  · rintro ⟨m, hm, rfl, hu⟩
    exact (mem_fixV_iff hD hA hm).2 hu

theorem engine_rk_fixV (hD : D.good = true) (hA : ActsByMats c A D.cols) :
    rk ↥(fixV A) = D.dU := by
  have hcard := c.card_eq (fixV A) D.inU (fun m hm => mem_fixV_iff hD hA hm)
  have hnat : Nat.card ↥(fixV A) = 2 ^ D.dU := by rw [hcard, good_card_fst hD]
  exact rk_eq_of_natCard D.dU hnat

theorem engine_rkIdx_fixV (hD : D.good = true) (hA : ActsByMats c A D.cols) :
    rkIdx (fixV A) = D.n - D.dU := by
  haveI : Finite V := c.finite
  have h1 := rk_add_rkIdx (fixV A)
  rw [engine_rk_fixV hD hA, c.rk_eq] at h1
  omega

theorem engine_exists_fix_not_mem (hD : D.good = true) (hA : ActsByMats c A D.cols) {g : MulAut V}
    (hg : g ∈ A) (hg1 : g ≠ 1) : ∃ v : V, g v = v ∧ v ∉ fixV A := by
  obtain ⟨t, ht, hgt⟩ := engine_index hD hA hg
  have ht0 : t ≠ 0 := fun h0 => hg1 ((engine_one_iff hD ht hgt).2 h0)
  obtain ⟨i, rfl⟩ : ∃ i, t = i + 1 := ⟨t - 1, by omega⟩
  have hi : i < 15 := by omega
  obtain ⟨m, hm, hfix, hu⟩ := good_ex_spec hD i hi
  refine ⟨c.vm m, ?_, ?_⟩
  · exact (engine_fixes_iff hD ht hgt hm).2 hfix
  · intro hv
    have hmem : D.inU m = true := (mem_fixV_iff hD hA hm).1 hv
    rw [hu] at hmem
    exact Bool.false_ne_true hmem

end Engine

end CFSG.ASVolI.AppH

module

public import CFSG.Quasithin.AppendixH.H15.CocodeTwoEngine
public import CFSG.Quasithin.AppendixH.H15.Vocab
public import CFSG.Quasithin.Background.D2Coprime

public section

namespace CFSG.ASVolI.AppH

open CFSG.Quasithin CFSG.Quasithin.H.Mathieu CFSG.ASVolI.ChH

variable {V : Type*} [CommGroup V]

section EngineXi

variable {D : KData} {c : MaskCoords V D.n} {A : Subgroup (MulAut V)}

private theorem par_zero : par 0 = 0 := by simp [par, parF]

private theorem xor_mod_two (a b : ℕ) : (a ^^^ b) % 2 = a % 2 ^^^ b % 2 := by
  rw [Nat.xor_mod_two_eq, Nat.add_mod]
  rcases Nat.mod_two_eq_zero_or_one a with ha | ha <;>
    rcases Nat.mod_two_eq_zero_or_one b with hb | hb <;> simp [ha, hb]

private theorem parF_xor : ∀ k (a b : ℕ), parF k (a ^^^ b) = parF k a ^^^ parF k b
  | 0, a, b => by simp [parF]
  | k + 1, a, b => by
      rw [parF, parF, parF, Nat.xor_div_two, parF_xor k, xor_mod_two]
      ac_rfl

private theorem par_xor (a b : ℕ) : par (a ^^^ b) = par a ^^^ par b := parF_xor 16 a b

private theorem inX_xor (D : KData) {a b : ℕ} (ha : D.inX a = true) (hb : D.inX b = true) :
    D.inX (a ^^^ b) = true := by
  simp only [KData.inX, beq_iff_eq, Nat.and_xor_distrib_left, par_xor] at *
  rw [ha, hb, Nat.xor_self]

private theorem inX_zero (D : KData) : D.inX 0 = true := by
  simp [KData.inX, par_zero]

private theorem actM_zero (cs : List ℕ) : actM cs 0 = 0 := by
  induction cs with
  | nil => rfl
  | cons c cs ih => simp [actM, ih]

private theorem testBit_one_shiftLeft (m k : ℕ) : (1 <<< m).testBit k = decide (k = m) := by
  rw [Nat.shiftLeft_eq, one_mul, Nat.testBit_two_pow]
  exact decide_eq_decide.mpr eq_comm

private theorem testBit_foldl_or (l : List ℕ) (a k : ℕ) :
    (l.foldl (fun acc m => acc ||| (1 <<< m)) a).testBit k =
      (a.testBit k || decide (k ∈ l)) := by
  induction l generalizing a with
  | nil => simp
  | cons m l ih =>
      rw [List.foldl_cons, ih, Nat.testBit_lor, testBit_one_shiftLeft]
      simp only [List.mem_cons, Bool.decide_or]
      cases a.testBit k <;> cases decide (k = m) <;> cases decide (k ∈ l) <;> rfl

private theorem two_le_countP : ∀ {l : List ℕ} {p : ℕ → Bool} {a b : ℕ},
    a ∈ l → b ∈ l → a ≠ b → p a = true → p b = true → 2 ≤ l.countP p
  | [], _, _, _, ha, _, _, _, _ => absurd ha (List.not_mem_nil)
  | x :: l, p, a, b, ha, hb, hab, hpa, hpb => by
      rw [List.mem_cons] at ha hb
      rw [List.countP_cons]
      rcases ha with rfl | ha
      · rcases hb with rfl | hb
        · exact absurd rfl hab
        · rw [hpa, if_pos rfl]
          have h1 : 1 ≤ l.countP p := List.one_le_countP_iff.mpr ⟨b, hb, hpb⟩
          omega
      · rcases hb with rfl | hb
        · rw [hpb, if_pos rfl]
          have h1 : 1 ≤ l.countP p := List.one_le_countP_iff.mpr ⟨a, ha, hpa⟩
          omega
        · have ih := two_le_countP ha hb hab hpa hpb
          split <;> omega

private theorem vm_inv' {n : ℕ} (c : MaskCoords V n) (m : ℕ) : (c.vm m)⁻¹ = c.vm m := by
  have h : c.vm m * c.vm m = 1 := by
    simpa [pow_two] using c.sq_eq_one (c.vm m)
  exact inv_eq_of_mul_eq_one_left h

private def xiSetSub (D : KData) (c : MaskCoords V D.n) : Subgroup V where
  carrier := {v | ∃ m < 2 ^ D.n, v = c.vm m ∧ D.inX m = true}
  one_mem' := ⟨0, Nat.two_pow_pos D.n, c.vm_zero.symm, inX_zero D⟩
  mul_mem' := by
    rintro v w ⟨a, ha, rfl, hxa⟩ ⟨b, hb, rfl, hxb⟩
    exact ⟨a ^^^ b, Nat.xor_lt_two_pow ha hb, (c.vm_xor a b).symm, inX_xor D hxa hxb⟩
  inv_mem' := by
    rintro v ⟨a, ha, rfl, hxa⟩
    exact ⟨a, ha, vm_inv' c a, hxa⟩

private theorem good_chkCols {D : KData} (hD : D.good = true) : D.chkCols = true := by
  unfold KData.good at hD; simp only [Bool.and_eq_true] at hD; exact hD.1.1.1.1.1.1.1.1.1

private theorem good_chkLU {D : KData} (hD : D.good = true) {m : ℕ} (hm : m < 2 ^ D.n) :
    D.inU m = true ↔ ∀ t < 16, D.fixes t m = true := by
  have hlu : D.chkLU = true := by
    unfold KData.good at hD; simp only [Bool.and_eq_true] at hD; exact hD.1.1.1.1.1.1.1.2
  rw [KData.chkLU] at hlu
  rw [List.all_eq_true] at hlu
  have h := hlu m (List.mem_range.mpr hm)
  rw [beq_iff_eq] at h
  rw [h, List.all_eq_true]
  simp [List.mem_range]

private theorem good_chkCard_inX {D : KData} (hD : D.good = true) :
    ((List.range (2 ^ D.n)).filter D.inX).length = 2 ^ (D.n - 1) := by
  have hcard : D.chkCard = true := by
    unfold KData.good at hD; simp only [Bool.and_eq_true] at hD; exact hD.1.1.1.1.1.1.2
  rw [KData.chkCard] at hcard
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hcard
  exact hcard.2

private theorem good_chkCnt {D : KData} (hD : D.good = true) {m : ℕ} (hm : m < 2 ^ D.n)
    (hU : D.inU m = false) :
    (List.range 15).countP (fun i => D.fixes (i + 1) m) ≤ 1 := by
  have hcnt : D.chkCnt = true := by
    unfold KData.good at hD; simp only [Bool.and_eq_true] at hD; exact hD.1.1.1.1.1.2
  rw [KData.chkCnt] at hcnt
  rw [List.all_eq_true] at hcnt
  have h := hcnt m (List.mem_range.mpr hm)
  rw [hU] at h
  simpa using h

private theorem good_chkEx {D : KData} (hD : D.good = true) {i : ℕ} (hi : i < 15) :
    ∃ m < 2 ^ D.n, D.fixes (i + 1) m = true ∧ D.inU m = false := by
  have hex : D.chkEx = true := by
    unfold KData.good at hD; simp only [Bool.and_eq_true] at hD; exact hD.1.1.1.1.2
  rw [KData.chkEx] at hex
  rw [List.all_eq_true] at hex
  have h := hex i (List.mem_range.mpr hi)
  rw [List.any_eq_true] at h
  obtain ⟨m, hm, hm'⟩ := h
  rw [Bool.and_eq_true, Bool.not_eq_true_eq_eq_false] at hm'
  exact ⟨m, List.mem_range.mp hm, hm'.1, hm'.2⟩

private theorem good_chkXi {D : KData} (hD : D.good = true) {m : ℕ} (hm : m < 2 ^ D.n)
    {t : ℕ} (ht1 : 1 ≤ t) (ht16 : t < 16) (hfix : D.fixes t m = true) :
    D.inX m = true := by
  have hxi : D.chkXi = true := by
    unfold KData.good at hD; simp only [Bool.and_eq_true] at hD; exact hD.1.1.1.2
  rw [KData.chkXi] at hxi
  rw [List.all_eq_true] at hxi
  have h := hxi m (List.mem_range.mpr hm)
  have hany : ((List.range 15).any fun i => D.fixes (i + 1) m) = true := by
    rw [List.any_eq_true]
    refine ⟨t - 1, List.mem_range.mpr (by omega), ?_⟩
    have hsub : t - 1 + 1 = t := by omega
    rw [hsub, hfix]
  rw [hany] at h
  simpa using h

private theorem good_chkXb₁ {D : KData} (hD : D.good = true) :
    ∀ p ∈ D.xb, 1 ≤ p.2 ∧ p.2 < 16 ∧ p.1 < 2 ^ D.n ∧
      D.fixes p.2 p.1 = true ∧ D.inX p.1 = true := by
  have hxb : D.chkXb = true := by
    unfold KData.good at hD; simp only [Bool.and_eq_true] at hD; exact hD.1.1.2
  rw [KData.chkXb] at hxb
  simp only [Bool.and_eq_true] at hxb
  intro p hp
  have hp' := (List.all_eq_true.mp hxb.1) p hp
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hp'
  exact ⟨hp'.1.1.1, hp'.1.1.2.1, hp'.1.1.2.2, hp'.1.2, hp'.2⟩

private theorem good_chkXb₂ {D : KData} (hD : D.good = true) {m : ℕ} (hm : m < 2 ^ D.n)
    (hinX : D.inX m = true) :
    (((combos (D.xb.map Prod.fst)).foldl (fun acc m => acc ||| (1 <<< m)) 0).testBit m) =
      true := by
  have hxb : D.chkXb = true := by
    unfold KData.good at hD; simp only [Bool.and_eq_true] at hD; exact hD.1.1.2
  rw [KData.chkXb] at hxb
  simp only [Bool.and_eq_true] at hxb
  have h := (List.all_eq_true.mp hxb.2) m (List.mem_range.mpr hm)
  rw [hinX] at h
  simpa using h

private theorem good_chkCt_inX {D : KData} (hD : D.good = true) {t : ℕ} (ht : t < 16) :
    D.inX (D.ct t) = true := by
  have hct : D.chkCt = true := by
    unfold KData.good at hD; simp only [Bool.and_eq_true] at hD; exact hD.2
  rw [KData.chkCt] at hct
  simp only [Bool.and_eq_true] at hct
  have hA : (List.range 16).all (fun t => D.inX (D.ct t)) = true := hct.1.1.1
  rw [List.all_eq_true] at hA
  exact hA t (List.mem_range.mpr ht)

private theorem good_chkCt_cover {D : KData} (hD : D.good = true) {m : ℕ} (hm : m < 2 ^ D.n)
    (hinX : D.inX m = true) : ∃ t < 16, D.inU (m ^^^ D.ct t) = true := by
  have hct : D.chkCt = true := by
    unfold KData.good at hD; simp only [Bool.and_eq_true] at hD; exact hD.2
  rw [KData.chkCt] at hct
  simp only [Bool.and_eq_true] at hct
  have hB : (List.range (2 ^ D.n)).all
      (fun m => !D.inX m || (List.range 16).any fun t => D.inU (m ^^^ D.ct t)) = true :=
    hct.1.1.2
  rw [List.all_eq_true] at hB
  have h := hB m (List.mem_range.mpr hm)
  rw [hinX] at h
  simp only [Bool.not_true, Bool.false_or] at h
  rw [List.any_eq_true] at h
  obtain ⟨t, ht, ht'⟩ := h
  exact ⟨t, List.mem_range.mp ht, ht'⟩

private theorem good_chkCt_ne {D : KData} (hD : D.good = true) {i : ℕ} (hi : i < 15) :
    D.inU (D.ct (i + 1)) = false := by
  have hct : D.chkCt = true := by
    unfold KData.good at hD; simp only [Bool.and_eq_true] at hD; exact hD.2
  rw [KData.chkCt] at hct
  simp only [Bool.and_eq_true] at hct
  have hC : (List.range 15).all (fun i => !D.inU (D.ct (i + 1))) = true := hct.1.2
  rw [List.all_eq_true] at hC
  have h := hC i (List.mem_range.mpr hi)
  simpa only [Bool.not_eq_true_eq_eq_false] using h

private theorem good_chkCt_one {D : KData} (hD : D.good = true) : D.inX 1 = false := by
  have hct : D.chkCt = true := by
    unfold KData.good at hD; simp only [Bool.and_eq_true] at hD; exact hD.2
  rw [KData.chkCt] at hct
  simp only [Bool.and_eq_true] at hct
  simpa only [Bool.not_eq_true_eq_eq_false] using hct.2

private theorem good_chkTV {D : KData} (hD : D.good = true) {t m : ℕ} (ht : t < 16)
    (hm : m < 2 ^ D.n) :
    D.inU (if D.inX m then actM (D.cols.getD t []) m ^^^ m
      else actM (D.cols.getD t []) m ^^^ m ^^^ D.ct t) = true := by
  have htv : D.chkTV = true := by
    unfold KData.good at hD; simp only [Bool.and_eq_true] at hD; exact hD.1.2
  rw [KData.chkTV] at htv
  rw [List.all_eq_true] at htv
  have h1 := htv t (List.mem_range.mpr ht)
  rw [List.all_eq_true] at h1
  exact h1 m (List.mem_range.mpr hm)

private theorem good_cols_spec {D : KData} (hD : D.good = true) {t : ℕ} (ht : t < 16) :
    ∀ x ∈ D.cols.getD t [], x < 2 ^ D.n := by
  have hcols := good_chkCols hD
  rw [KData.chkCols] at hcols
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hcols
  have hlen : D.cols.length = 16 := hcols.1.1.1
  have hall : D.cols.all (fun c => decide (c.length = D.n) && c.all fun x => decide (x < 2 ^ D.n)) =
      true := hcols.2
  have ht' : t < D.cols.length := by rw [hlen]; exact ht
  have hc : D.cols.getD t [] ∈ D.cols := by
    rw [List.getD_eq_getElem (l := D.cols) (d := []) (hn := ht')]
    exact List.getElem_mem ht'
  have hc' := (List.all_eq_true.mp hall) _ hc
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at hc'
  exact hc'.2

private theorem good_actM_lt {D : KData} (hD : D.good = true) {t : ℕ} (ht : t < 16) (m : ℕ) :
    actM (D.cols.getD t []) m < 2 ^ D.n :=
  actM_lt (good_cols_spec hD ht) m

private theorem good_n_pos {D : KData} (hD : D.good = true) : 0 < D.n := by
  by_contra hn
  have hn0 : D.n = 0 := Nat.eq_zero_of_not_pos hn
  obtain ⟨m, hm, _, hnotU⟩ := good_chkEx hD (i := 0) (by norm_num)
  have hm0 : m = 0 := by
    rw [hn0] at hm
    exact Nat.lt_one_iff.mp hm
  have hU0 : D.inU 0 = true :=
    (good_chkLU hD (m := 0) (Nat.two_pow_pos D.n)).2
      (by intro t _; simp [KData.fixes, actM_zero])
  rw [hm0] at hnotU
  rw [hU0] at hnotU
  exact Bool.false_ne_true hnotU.symm

private theorem good_ct_lt {D : KData} (hD : D.good = true) {t : ℕ} (ht : t < 16) :
    D.ct t < 2 ^ D.n := by
  have hn := good_n_pos hD
  have hspec := good_cols_spec hD ht
  have hlt : (D.cols.getD t []).headD 0 < 2 ^ D.n := by
    cases hc : D.cols.getD t [] with
    | nil =>
        simp only [hc, List.headD_nil]
        exact Nat.two_pow_pos D.n
    | cons x xs =>
        simp only [hc, List.headD_cons]
        exact hspec x (by rw [hc]; exact List.mem_cons_self)
  have h1 : 1 < 2 ^ D.n := Nat.one_lt_two_pow_iff.mpr (by omega)
  unfold KData.ct
  exact Nat.xor_lt_two_pow hlt h1

private theorem vm_mem_xiSub_of (hD : D.good = true) (hA : ActsByMats c A D.cols)
    {g : MulAut V} (hg : g ∈ A) (hg1 : g ≠ 1) {m : ℕ} (hm : m < 2 ^ D.n)
    (hgv : g (c.vm m) = c.vm m) : c.vm m ∈ xiSub A := by
  have hfx : c.vm m ∈ fixV (Subgroup.zpowers g) := CFSG.Quasithin.mem_fixV_zpowers_iff.mpr hgv
  rw [xiSub]
  exact (le_iSup₂_of_le g hg (le_iSup_of_le
    (f := fun _ : g ≠ 1 => fixV (Subgroup.zpowers g)) hg1 le_rfl) :
    fixV (Subgroup.zpowers g) ≤ _) hfx

theorem engine_mem_xiSub (hD : D.good = true) (hA : ActsByMats c A D.cols) (v : V) :
    v ∈ xiSub A ↔ ∃ m < 2 ^ D.n, v = c.vm m ∧ D.inX m = true := by
  constructor
  · intro hv
    have hle : xiSub A ≤ xiSetSub D c := by
      rw [xiSub]
      refine iSup_le fun a => iSup_le fun ha => iSup_le fun ha1 => ?_
      intro y hy
      have hay : a y = y := (mem_fixV.mp hy) a (Subgroup.mem_zpowers a)
      obtain ⟨m, hm, hmv⟩ := c.vm_surj y
      obtain ⟨t, ht16, hgt⟩ := engine_index hD hA ha
      have htne : t ≠ 0 := fun h0 => ha1 ((engine_one_iff hD ht16 hgt).mpr h0)
      have hfix : D.fixes t m = true := by
        apply (engine_fixes_iff hD ht16 hgt hm).mp
        rw [← hmv] at hay
        exact hay
      exact ⟨m, hm, hmv.symm, good_chkXi hD hm (Nat.one_le_iff_ne_zero.mpr htne) ht16 hfix⟩
    exact hle hv
  · rintro ⟨m, hm, rfl, hx⟩
    have hbit : (((combos (D.xb.map Prod.fst)).foldl
        (fun acc m => acc ||| (1 <<< m)) 0).testBit m) = true := good_chkXb₂ hD hm hx
    have hfold := testBit_foldl_or (combos (D.xb.map Prod.fst)) 0 m
    rw [hbit] at hfold
    have hmem : m ∈ combos (D.xb.map Prod.fst) := by simpa using hfold.symm
    have hco : ∀ a ∈ D.xb.map Prod.fst, c.vm a ∈ xiSub A := by
      intro a ha
      obtain ⟨p, hp, rfl⟩ := List.mem_map.mp ha
      obtain ⟨hp1, hp2, hp3, hfixp, _⟩ := good_chkXb₁ hD p hp
      obtain ⟨g, hgA, hgm⟩ := engine_exists_elem hD hA hp2
      have hg1 : g ≠ 1 := fun h1 => by
        have := (engine_one_iff hD hp2 hgm).mp h1
        omega
      have hfix : g (c.vm p.1) = c.vm p.1 :=
        (engine_fixes_iff hD hp2 hgm hp3).mpr hfixp
      exact vm_mem_xiSub_of hD hA hgA hg1 hp3 hfix
    exact MaskCoords.vm_mem_of_combos c (xiSub A) hco m hmem

private theorem mem_xiSub_iff_inX (hD : D.good = true) (hA : ActsByMats c A D.cols) {m : ℕ}
    (hm : m < 2 ^ D.n) : c.vm m ∈ xiSub A ↔ D.inX m = true := by
  rw [engine_mem_xiSub hD hA]
  constructor
  · rintro ⟨m', hm', heq, hx⟩
    have hmm := c.vm_inj m m' hm hm' heq
    rwa [← hmm] at hx
  · intro hx; exact ⟨m, hm, rfl, hx⟩

private theorem mem_fixV_iff_inU (hD : D.good = true) (hA : ActsByMats c A D.cols) {m : ℕ}
    (hm : m < 2 ^ D.n) : c.vm m ∈ fixV A ↔ D.inU m = true := by
  rw [engine_mem_fixV hD hA]
  constructor
  · rintro ⟨m', hm', heq, hx⟩
    have hmm := c.vm_inj m m' hm hm' heq
    rwa [← hmm] at hx
  · intro hx; exact ⟨m, hm, rfl, hx⟩

private theorem transpAxis_mul_left_mem {g : MulAut V} {U W : Subgroup V} {c0 u : V}
    (hu : u ∈ U) (h : IsTranspAxis g U W c0) : IsTranspAxis g U W (u * c0) := by
  refine ⟨h.1, fun x hx => ?_⟩
  have h2 := h.2 x hx
  rw [mul_inv_rev]
  rw [← mul_assoc]
  exact U.mul_mem h2 (U.inv_mem hu)

private theorem IsTranspAxis_of_index (hD : D.good = true) (hA : ActsByMats c A D.cols)
    {g : MulAut V} {t : ℕ} (ht : t < 16)
    (hgt : ∀ m, g (c.vm m) = c.vm (actM (D.cols.getD t []) m)) :
    IsTranspAxis g (fixV A) (xiSub A) (c.vm (D.ct t)) := by
  constructor
  · intro x hx
    obtain ⟨m, hm, rfl⟩ := c.vm_surj x
    have hinX : D.inX m = true := (mem_xiSub_iff_inX hD hA hm).mp hx
    have halt : actM (D.cols.getD t []) m ^^^ m < 2 ^ D.n :=
      Nat.xor_lt_two_pow (good_actM_lt hD ht m) hm
    have hmem : c.vm (actM (D.cols.getD t []) m ^^^ m) ∈ fixV A :=
      (mem_fixV_iff_inU hD hA halt).mpr (by
        have htv := good_chkTV hD ht hm
        rw [hinX] at htv
        simpa using htv)
    have hgoal : g (c.vm m) * (c.vm m)⁻¹ = c.vm (actM (D.cols.getD t []) m ^^^ m) := by
      simp only [hgt m, vm_inv' c, ← c.vm_xor]
    rwa [hgoal]
  · intro x hx
    obtain ⟨m, hm, rfl⟩ := c.vm_surj x
    have hnotX : D.inX m = false := by
      cases h : D.inX m with
      | false => rfl
      | true => exact absurd ((mem_xiSub_iff_inX hD hA hm).mpr h) hx
    have halt : actM (D.cols.getD t []) m ^^^ m < 2 ^ D.n :=
      Nat.xor_lt_two_pow (good_actM_lt hD ht m) hm
    have hab : actM (D.cols.getD t []) m ^^^ m ^^^ D.ct t < 2 ^ D.n :=
      Nat.xor_lt_two_pow halt (good_ct_lt hD ht)
    have hmem : c.vm (actM (D.cols.getD t []) m ^^^ m ^^^ D.ct t) ∈ fixV A :=
      (mem_fixV_iff_inU hD hA hab).mpr (by
        have htv := good_chkTV hD ht hm
        rw [hnotX] at htv
        simpa using htv)
    have hgoal : g (c.vm m) * (c.vm m)⁻¹ * (c.vm (D.ct t))⁻¹
        = c.vm (actM (D.cols.getD t []) m ^^^ m ^^^ D.ct t) := by
      simp only [hgt m, vm_inv' c, ← c.vm_xor]
    rwa [hgoal]

theorem engine_rkIdx_xiSub (hD : D.good = true) (hA : ActsByMats c A D.cols) :
    rkIdx (xiSub A) = 1 := by
  have hn := good_n_pos hD
  have hcard : Nat.card (xiSub A) = 2 ^ (D.n - 1) := by
    rw [c.card_eq (xiSub A) D.inX (fun m hm => mem_xiSub_iff_inX hD hA hm)]
    exact good_chkCard_inX hD
  have hlog := c.rkIdx_of_card (U := xiSub A) (F := List.replicate (2 ^ (D.n - 1)) 0)
    (by rw [hcard]; simp)
  rw [hlog, List.length_replicate, Nat.log_pow (by norm_num : 1 < 2)]
  omega

theorem engine_fixV_noncyclic (hD : D.good = true) (hA : ActsByMats c A D.cols) :
    ∀ g ∈ A, ∀ h ∈ A, g ≠ 1 → h ≠ 1 → g ≠ h → ∀ v : V, g v = v → h v = v → v ∈ fixV A := by
  intro g hgA h hhA hg1 hh1 hgh v hgv hhv
  obtain ⟨s, hs16, hgs⟩ := engine_index hD hA hgA
  obtain ⟨t, ht16, hht⟩ := engine_index hD hA hhA
  have hs0 : s ≠ 0 := fun h0 => hg1 ((engine_one_iff hD hs16 hgs).mpr h0)
  have ht0 : t ≠ 0 := fun h0 => hh1 ((engine_one_iff hD ht16 hht).mpr h0)
  have hst : s ≠ t := by
    intro hst
    exact hgh (by
      ext w
      obtain ⟨m, hm, rfl⟩ := c.vm_surj w
      rw [hgs m, hht m, hst])
  obtain ⟨m, hm, rfl⟩ := c.vm_surj v
  have hfixs : D.fixes s m = true := (engine_fixes_iff hD hs16 hgs hm).mp hgv
  have hfixt : D.fixes t m = true := (engine_fixes_iff hD ht16 hht hm).mp hhv
  have hUm : D.inU m = true := by
    by_contra hU
    have hUf : D.inU m = false := by
      cases h : D.inU m with
      | false => rfl
      | true => exact absurd h hU
    have hcnt := good_chkCnt hD hm hUf
    have h2 : 2 ≤ (List.range 15).countP (fun i => D.fixes (i + 1) m) := by
      refine two_le_countP (a := s - 1) (b := t - 1) (p := fun i => D.fixes (i + 1) m)
        ?_ ?_ ?_ ?_ ?_
      · rw [List.mem_range]; omega
      · rw [List.mem_range]; omega
      · intro hab; exact hst (by omega)
      · have hsub : s - 1 + 1 = s := by omega
        rw [hsub]; exact hfixs
      · have hsub : t - 1 + 1 = t := by omega
        rw [hsub]; exact hfixt
    omega
  exact (engine_mem_fixV hD hA (c.vm m)).mpr ⟨m, hm, rfl, hUm⟩

theorem engine_centralizes (hD : D.good = true) (hA : ActsByMats c A D.cols) {g h : MulAut V}
    (hg : g ∈ A) (hh : h ∈ A) (hg1 : g ≠ 1) (hfix : ∀ v : V, g v = v → h v = v) :
    h = 1 ∨ h = g := by
  by_cases h1 : h = 1
  · exact Or.inl h1
  by_cases hg_eq : h = g
  · exact Or.inr hg_eq
  exfalso
  obtain ⟨v, hgv, hv⟩ := engine_exists_fix_not_mem hD hA hg hg1
  exact hv (engine_fixV_noncyclic hD hA g hg h hh hg1 h1 (fun hgh => hg_eq hgh.symm)
    v hgv (hfix v hgv))

theorem engine_transv (hD : D.good = true) (hA : ActsByMats c A D.cols) :
    (∀ g ∈ A, ∃ w ∈ xiSub A, IsTranspAxis g (fixV A) (xiSub A) w) ∧
    (∀ w ∈ xiSub A, ∃ g ∈ A, IsTranspAxis g (fixV A) (xiSub A) w) ∧
    (∀ g ∈ A, (∀ x : V, g x * x⁻¹ ∈ fixV A) → g = 1) := by
  refine ⟨?_, ?_, ?_⟩
  · intro g hgA
    obtain ⟨t, ht16, hgt⟩ := engine_index hD hA hgA
    exact ⟨c.vm (D.ct t),
      (mem_xiSub_iff_inX hD hA (good_ct_lt hD ht16)).mpr (good_chkCt_inX hD ht16),
      IsTranspAxis_of_index hD hA ht16 hgt⟩
  · intro w hw
    obtain ⟨m, hm, hwm, hinX⟩ := (engine_mem_xiSub hD hA w).mp hw
    obtain ⟨t, ht16, hUt⟩ := good_chkCt_cover hD hm hinX
    obtain ⟨g, hgA, hgt⟩ := engine_exists_elem hD hA ht16
    refine ⟨g, hgA, ?_⟩
    have hu_mem : c.vm (m ^^^ D.ct t) ∈ fixV A :=
      (mem_fixV_iff_inU hD hA (Nat.xor_lt_two_pow hm (good_ct_lt hD ht16))).mpr hUt
    have hbase := IsTranspAxis_of_index hD hA ht16 hgt
    have hmoved : IsTranspAxis g (fixV A) (xiSub A) (c.vm (m ^^^ D.ct t) * c.vm (D.ct t)) :=
      transpAxis_mul_left_mem hu_mem hbase
    have heq : c.vm (m ^^^ D.ct t) * c.vm (D.ct t) = w := by
      rw [hwm]
      simp only [← c.vm_xor]
      congr 1
      rw [Nat.xor_assoc, Nat.xor_self, Nat.xor_zero]
    rwa [heq] at hmoved
  · intro g hgA hmod
    obtain ⟨t, ht16, hgt⟩ := engine_index hD hA hgA
    have ht0 : t = 0 := by
      by_contra ht0
      have ht1 : 1 ≤ t := Nat.one_le_iff_ne_zero.mpr ht0
      have hsub : t - 1 + 1 = t := by omega
      have hct_false : D.inU (D.ct t) = false := by
        have h := good_chkCt_ne hD (i := t - 1) (by omega)
        rwa [hsub] at h
      have hn := good_n_pos hD
      have h1lt : 1 < 2 ^ D.n := Nat.one_lt_two_pow_iff.mpr (by omega)
      have ha_lt : actM (D.cols.getD t []) 1 ^^^ 1 < 2 ^ D.n :=
        Nat.xor_lt_two_pow (good_actM_lt hD ht16 1) h1lt
      have hx1 : D.inX 1 = false := good_chkCt_one hD
      have hgx : g (c.vm 1) * (c.vm 1)⁻¹ = c.vm (actM (D.cols.getD t []) 1 ^^^ 1) := by
        simp only [hgt 1, vm_inv' c, ← c.vm_xor]
      have hUA : c.vm (actM (D.cols.getD t []) 1 ^^^ 1) ∈ fixV A := hgx ▸ hmod (c.vm 1)
      have hUa : D.inU (actM (D.cols.getD t []) 1 ^^^ 1) = true :=
        (mem_fixV_iff_inU hD hA ha_lt).mp hUA
      have htv := good_chkTV hD ht16 h1lt
      rw [hx1] at htv
      have hUat : D.inU (actM (D.cols.getD t []) 1 ^^^ 1 ^^^ D.ct t) = true := by
        simpa using htv
      have hat_lt : actM (D.cols.getD t []) 1 ^^^ 1 ^^^ D.ct t < 2 ^ D.n :=
        Nat.xor_lt_two_pow ha_lt (good_ct_lt hD ht16)
      have hUAt : c.vm (actM (D.cols.getD t []) 1 ^^^ 1 ^^^ D.ct t) ∈ fixV A :=
        (mem_fixV_iff_inU hD hA hat_lt).mpr hUat
      have hctU : c.vm (D.ct t) ∈ fixV A := by
        have hprod : c.vm (actM (D.cols.getD t []) 1 ^^^ 1)
            * c.vm (actM (D.cols.getD t []) 1 ^^^ 1 ^^^ D.ct t) ∈ fixV A :=
          (fixV A).mul_mem hUA hUAt
        have heq : c.vm (actM (D.cols.getD t []) 1 ^^^ 1)
            * c.vm (actM (D.cols.getD t []) 1 ^^^ 1 ^^^ D.ct t) = c.vm (D.ct t) := by
          rw [← c.vm_xor]
          congr 1
          rw [← Nat.xor_assoc, Nat.xor_self, Nat.zero_xor]
        rwa [heq] at hprod
      have hct_true : D.inU (D.ct t) = true :=
        (mem_fixV_iff_inU hD hA (good_ct_lt hD ht16)).mp hctU
      rw [hct_true] at hct_false
      exact Bool.false_ne_true hct_false.symm
    exact (engine_one_iff hD ht16 hgt).mpr ht0

end EngineXi

private theorem map_fixV_zpowers {a h : MulAut V} {y : V}
    (hy : y ∈ fixV (Subgroup.zpowers a)) :
    h y ∈ fixV (Subgroup.zpowers (h * a * h⁻¹)) := by
  rw [CFSG.Quasithin.mem_fixV_zpowers_iff] at hy ⊢
  simpa [MulAut.mul_apply] using congrArg h hy

private theorem mem_xiSub_conj {X : Subgroup (MulAut V)} {h : MulAut V}
    (hn : ∀ g ∈ X, h * g * h⁻¹ ∈ X) :
    ∀ x, x ∈ xiSub X → h x ∈ xiSub X := by
  intro x hx
  have hle : xiSub X ≤ (xiSub X).comap (h : V →* V) := by
    rw [xiSub]
    refine iSup_le fun a => iSup_le fun ha => iSup_le fun ha1 => ?_
    intro y hy
    have hne : h * a * h⁻¹ ≠ 1 := by
      intro hh
      apply ha1
      have h2 := congrArg (fun k : MulAut V => h⁻¹ * k * h) hh
      simpa [mul_assoc] using h2
    have hyfix := map_fixV_zpowers (a := a) (h := h) hy
    exact (le_iSup₂_of_le (h * a * h⁻¹) (hn a ha)
      (le_iSup_of_le (f := fun _ : h * a * h⁻¹ ≠ 1 =>
        fixV (Subgroup.zpowers (h * a * h⁻¹))) hne le_rfl) :
        fixV (Subgroup.zpowers (h * a * h⁻¹)) ≤ _) hyfix
  exact (Subgroup.mem_comap).mp (hle hx)

theorem fixV_conj_iff {X : Subgroup (MulAut V)} {h : MulAut V}
    (hn : ∀ g ∈ X, h * g * h⁻¹ ∈ X) (hn' : ∀ g ∈ X, h⁻¹ * g * h ∈ X) (x : V) :
    h x ∈ fixV X ↔ x ∈ fixV X := by
  constructor
  · intro hx
    rw [mem_fixV] at hx ⊢
    intro g hg
    have h1 := hx (h * g * h⁻¹) (hn g hg)
    have h1' : h (g x) = h x := by simpa [MulAut.mul_apply] using h1
    exact h.injective h1'
  · intro hx
    rw [mem_fixV] at hx ⊢
    intro g hg
    have h1 := hx (h⁻¹ * g * h) (hn' g hg)
    have h1' : h⁻¹ (g (h x)) = x := by simpa [MulAut.mul_apply] using h1
    have h2 := congrArg h h1'
    simpa using h2

theorem xiSub_conj_iff {X : Subgroup (MulAut V)} {h : MulAut V}
    (hn : ∀ g ∈ X, h * g * h⁻¹ ∈ X) (hn' : ∀ g ∈ X, h⁻¹ * g * h ∈ X) (x : V) :
    h x ∈ xiSub X ↔ x ∈ xiSub X := by
  constructor
  · intro hx
    have hn'' : ∀ g ∈ X, h⁻¹ * g * (h⁻¹)⁻¹ ∈ X := by
      intro g hg
      simpa using hn' g hg
    have := mem_xiSub_conj (X := X) (h := h⁻¹) hn'' (h x) hx
    simpa using this
  · intro hx
    exact mem_xiSub_conj (X := X) (h := h) hn x hx

theorem fullTranspAxis_of_engine {D : KData} {c : MaskCoords V D.n} {A : Subgroup (MulAut V)}
    (hD : D.good = true) (hA : ActsByMats c A D.cols) {G : Subgroup (MulAut V)}
    (hn : ∀ h ∈ G, ∀ g ∈ A, h * g * h⁻¹ ∈ A) :
    FullTranspAxis G A (fixV A) (xiSub A) := by
  obtain ⟨h1, h2, h3⟩ := engine_transv hD hA
  refine ⟨h1, h2, h3, ?_⟩
  intro h hhG g hgA c0 hc
  have hn1 : ∀ g ∈ A, h * g * h⁻¹ ∈ A := fun g hg => hn h hhG g hg
  have hn2 : ∀ g ∈ A, h⁻¹ * g * h ∈ A := by
    intro g hg
    have := hn h⁻¹ (G.inv_mem hhG) g hg
    simpa using this
  constructor
  · intro x hx
    have hx' : h⁻¹ x ∈ xiSub A := by
      have hh := (xiSub_conj_iff (X := A) (h := h) hn1 hn2 (h⁻¹ x)).mp (by simpa using hx)
      simpa using hh
    have hfix := hc.1 (h⁻¹ x) hx'
    have hxc : h ((h⁻¹ x)⁻¹) = x⁻¹ := by simp
    have hgoal : (h * g * h⁻¹) x * x⁻¹ = h (g (h⁻¹ x) * (h⁻¹ x)⁻¹) := by
      simp only [MulAut.mul_apply, ← hxc, ← map_mul]
    rw [hgoal]
    exact (fixV_conj_iff (X := A) (h := h) hn1 hn2 _).mpr hfix
  · intro x hx
    have hx' : h⁻¹ x ∉ xiSub A := fun hmem =>
      hx (by simpa using (xiSub_conj_iff (X := A) (h := h) hn1 hn2 (h⁻¹ x)).mpr hmem)
    have hfix := hc.2 (h⁻¹ x) hx'
    have hxc : h ((h⁻¹ x)⁻¹) = x⁻¹ := by simp
    have hcinv : (h c0)⁻¹ = h (c0⁻¹) := by simp
    have hgoal : (h * g * h⁻¹) x * x⁻¹ * (h c0)⁻¹
        = h (g (h⁻¹ x) * (h⁻¹ x)⁻¹ * c0⁻¹) := by
      simp only [MulAut.mul_apply, ← hxc, hcinv, ← map_mul]
    rw [hgoal]
    exact (fixV_conj_iff (X := A) (h := h) hn1 hn2 _).mpr hfix

end CFSG.ASVolI.AppH

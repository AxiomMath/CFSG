module

public import CFSG.LocalAnalysis.StandardType.GGQ2ExcCensusChecks
public import CFSG.LocalAnalysis.StandardType.GGQ2ExcCensusLabel

public section

namespace CFSG.StandardType.GGQ2Frame.ExcRaw

open CFSG.Assembly Module
open CFSG.StandardType (GGLabelIso GGLabQTwo)

variable {m : Fin 6} {T : Chk.Tabs}

@[expose] def LineHyp (m : Fin 6) (ext q2 : Bool) (vx : V m) (ℓ : Finset (Root m)) : Prop :=
  vx ≠ 0 ∧ admissible m ℓ ∧
    (q2 = true → ∃ lab : LargeEvenLabel, GGLabQTwo 3 lab ∧ GGLabelIso lab (label m ℓ)) ∧
    occurs m (Submodule.span (ZMod 3) {vx}) ℓ ∧ cent m ℓ = Submodule.span (ZMod 3) {vx} ∧
    (vx ∈ inside m ℓ ↔ ext = false)

@[expose] def PlaneHyp (m : Fin 6) (U : Submodule (ZMod 3) (V m)) (j : Finset (Root m)) : Prop :=
  admissible m j ∧ occurs m U j ∧ cent m j = U

@[expose] def CandHyp (m : Fin 6) (vx z : V m) (k : Finset (Root m)) : Prop :=
  admissible m k ∧ occurs m (Submodule.span (ZMod 3) {z}) k ∧
    cent m k = Submodule.span (ZMod 3) {z} ∧ vx ∉ cent m k

theorem candHyp_of_candidate {vx z : V m} {j k : Finset (Root m)}
    (h : Candidate (excRaw m) vx j z k) : CandHyp m vx z k :=
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.2⟩

private theorem chk_all_iff {n : ℕ} {f : (i : ℕ) → i < n → Bool} :
    Nat.all n f = true ↔ ∀ i (h : i < n), f i h = true := by
  rw [Nat.all_eq_finRange_all, List.all_eq_true]
  exact ⟨fun h i hi => h ⟨i, hi⟩ (List.mem_finRange ⟨i, hi⟩),
    fun h i _ => h i i.isLt⟩

private theorem dig_lt_three (c k : ℕ) : Chk.dig c k < 3 :=
  Nat.mod_lt _ (by norm_num)

private theorem chk_dig_code (m : Fin 6) (v : V m) (k : Fin (dim m)) :
    Chk.dig (code m v) k = (v k).val := by
  have h : ((Chk.dig (code m v) (k : ℕ) : ℕ) : ZMod 3) = v k := by
    have h1 := congrFun (vec_code m v) k
    simpa [vec] using h1
  have hv : (Chk.dig (code m v) (k : ℕ) : ZMod 3).val = (v k).val := congrArg ZMod.val h
  rw [ZMod.val_natCast, Nat.mod_eq_of_lt (dig_lt_three _ _)] at hv
  exact hv

private theorem natCast_ne_zero_three {n : ℕ} (hn : n < 3) (h : n ≠ 0) : (n : ZMod 3) ≠ 0 := by
  intro h0
  rw [ZMod.natCast_eq_zero_iff n 3] at h0
  have := Nat.le_of_dvd (by omega) h0
  omega

private theorem pivN_le (d c : ℕ) : Chk.pivN d c ≤ d := by
  unfold Chk.pivN
  cases h : (List.range d).find? (fun k => Chk.dig c k != 0) with
  | none => simp
  | some q =>
    have hq : q < d := by
      have := List.mem_of_find?_eq_some h
      rwa [List.mem_range] at this
    simp only [Option.getD_some]
    omega

private theorem findIdx_pivN (d c : ℕ) :
    (List.range d).findIdx (fun k => Chk.dig c k != 0) = Chk.pivN d c := by
  unfold Chk.pivN
  cases hf : (List.range d).find? (fun k => Chk.dig c k != 0) with
  | none =>
    have hlen : (List.range d).findIdx (fun k => Chk.dig c k != 0) = (List.range d).length := by
      rw [List.findIdx_eq_length]
      intro x hx
      by_contra hxne
      have hp : (fun k => Chk.dig c k != 0) x = true := by simpa [bne_iff_ne] using hxne
      have his : ((List.range d).find? (fun k => Chk.dig c k != 0)).isSome = true :=
        List.find?_isSome.mpr ⟨x, hx, hp⟩
      rw [hf] at his
      simp at his
    rw [hlen, List.length_range]
    simp
  | some q =>
    have h2 := List.find?_eq_getElem?_findIdx (xs := List.range d)
      (p := fun k => Chk.dig c k != 0)
    rw [hf] at h2
    obtain ⟨hlt, hget⟩ := List.getElem?_eq_some_iff.mp h2.symm
    have h3 : (List.range d)[(List.range d).findIdx (fun k => Chk.dig c k != 0)] =
        (List.range d).findIdx (fun k => Chk.dig c k != 0) := List.getElem_range hlt
    have : (List.range d).findIdx (fun k => Chk.dig c k != 0) = q := by omega
    rw [this]
    simp

private theorem dig_eq_zero_of_lt_pivN {d c k : ℕ} (h : k < Chk.pivN d c) :
    Chk.dig c k = 0 := by
  have hfi := findIdx_pivN d c
  rcases eq_or_lt_of_le (pivN_le d c) with hd | hlt
  · by_contra hk
    have hk' : (fun k => Chk.dig c k != 0) k = true := by simpa [bne_iff_ne] using hk
    have hmem : k ∈ List.range d := List.mem_range.mpr (by omega)
    have his : ((List.range d).find? (fun k => Chk.dig c k != 0)).isSome = true :=
      List.find?_isSome.mpr ⟨k, hmem, hk'⟩
    cases hf : (List.range d).find? (fun k => Chk.dig c k != 0) with
    | none => rw [hf] at his; simp at his
    | some q =>
      have hpiv : Chk.pivN d c = q := by simp [Chk.pivN, hf]
      have hq : q < d := by
        have := List.mem_of_find?_eq_some hf
        rwa [List.mem_range] at this
      omega
  · have hlen : Chk.pivN d c < (List.range d).length := by simpa using hlt
    have hmin := (List.findIdx_eq hlen).mp hfi
    have := hmin.2 k h
    simpa [List.getElem_range, bne_iff_ne] using this

private theorem dig_pivN_ne_zero {d c : ℕ} (h : Chk.pivN d c < d) :
    Chk.dig c (Chk.pivN d c) ≠ 0 := by
  have hfi := findIdx_pivN d c
  have hlen : Chk.pivN d c < (List.range d).length := by simpa using h
  have hpos := (List.findIdx_eq hlen).mp hfi
  have := hpos.1
  simpa [List.getElem_range, bne_iff_ne] using this

private theorem pivN_eq_of {d c q : ℕ} (hq : q < d) (hq0 : Chk.dig c q ≠ 0)
    (hmin : ∀ k, k < q → Chk.dig c k = 0) : Chk.pivN d c = q := by
  unfold Chk.pivN
  have hlen : q < (List.range d).length := by simpa using hq
  have hfi : (List.range d).findIdx (fun k => Chk.dig c k != 0) = q := by
    rw [List.findIdx_eq hlen]
    refine ⟨?_, ?_⟩
    · simpa [List.getElem_range, bne_iff_ne] using hq0
    · intro k hk
      simp [List.getElem_range, hmin k hk]
  have hsome : (List.range d).find? (fun k => Chk.dig c k != 0) = some q := by
    rw [List.find?_eq_getElem?_findIdx, hfi]
    exact List.getElem?_range hq
  rw [hsome, Option.getD_some]

private theorem eq_zero_of_dig_eq_zero {v : V m} (h : ∀ k : Fin (dim m), Chk.dig (code m v) k = 0) :
    v = 0 := by
  funext k
  have h1 : v k = (Chk.dig (code m v) (k : ℕ) : ZMod 3) := by
    rw [← congrFun (vec_code m v) k]
    rfl
  rw [h1, h k]
  simp

private theorem eq_ofMask_zm_of_occurs (hT : Chk.tabsOK m T = true) {cv : ℕ}
    (hcv : cv < 3 ^ dim m) {ℓ : Finset (Root m)}
    (hocc : occurs m (Submodule.span (ZMod 3) {vec m cv}) ℓ)
    (hcent : cent m ℓ = Submodule.span (ZMod 3) {vec m cv}) :
    ℓ = ofMask m (T.zm[cv]!) := by
  refine Finset.ext fun t => ?_
  rw [mem_iff_vanish_of_occurs hocc hcent t, vanish_span_singleton_iff, mem_ofMask_zm hT hcv]

private theorem eq_ofMask_land_zm_of_occurs (hT : Chk.tabsOK m T = true) {cv cy : ℕ}
    (hcv : cv < 3 ^ dim m) (hcy : cy < 3 ^ dim m) {j : Finset (Root m)}
    (hocc : occurs m (Submodule.span (ZMod 3) {vec m cv, vec m cy}) j)
    (hcent : cent m j = Submodule.span (ZMod 3) {vec m cv, vec m cy}) :
    j = ofMask m (T.zm[cv]! &&& T.zm[cy]!) := by
  refine Finset.ext fun t => ?_
  rw [mem_iff_vanish_of_occurs hocc hcent t, vanish_span_pair, mem_ofMask_land,
    mem_ofMask_zm hT hcv, mem_ofMask_zm hT hcy]

private theorem testBit_of_subN_trunc {r c c' t : ℕ} (h : Chk.subN (Chk.trunc r c) c' = true)
    (ht : t < r) (hc : c.testBit t = true) : c'.testBit t = true := by
  have h' : Chk.trunc r c &&& c' = Chk.trunc r c := by
    simpa [Chk.subN, beq_iff_eq] using h
  have h1 : (Chk.trunc r c).testBit t = true := by
    rw [Chk.trunc, Nat.testBit_land, Nat.testBit_two_pow_sub_one]
    simp [hc, ht]
  have h2 : (Chk.trunc r c &&& c').testBit t = true := by rw [h']; exact h1
  rw [Nat.testBit_land] at h2
  exact (Bool.and_eq_true_iff.mp h2).2

private theorem mem_cent_code_iff {c : Finset (Root m)} {v : V m} :
    v ∈ cent m c ↔ ∀ t ∈ c, root m t v = 0 := by
  simp [cent, Submodule.mem_iInf, LinearMap.mem_ker]

private theorem mem_cent_of_subN_zm (hT : Chk.tabsOK m T = true) {c w : ℕ}
    (hw : w < 3 ^ dim m)
    (hsub : Chk.subN (Chk.trunc (nroots m) c) (T.zm[w]!) = true) :
    vec m w ∈ cent m (ofMask m c) := by
  rw [mem_cent_code_iff]
  intro t ht
  have h1 : (T.zm[w]!).testBit t.val = true := by
    refine testBit_of_subN_trunc hsub t.isLt ?_
    rwa [mem_ofMask] at ht
  exact (mem_ofMask_zm hT hw t).mp ((mem_ofMask (m := m) (n := T.zm[w]!) (t := t)).mpr h1)

private theorem not_mem_cent_of_not_subN (hT : Chk.tabsOK m T = true) {c w : ℕ}
    (hw : w < 3 ^ dim m) (hsub : Chk.subN (Chk.trunc (nroots m) c) (T.zm[w]!) = false) :
    vec m w ∉ cent m (ofMask m c) := by
  intro hmem
  have heq : Chk.trunc (nroots m) c &&& T.zm[w]! = Chk.trunc (nroots m) c := by
    refine Nat.eq_of_testBit_eq fun t => ?_
    rw [Nat.testBit_land]
    by_cases h1 : (Chk.trunc (nroots m) c).testBit t = true
    · have ht : t < nroots m := by
        have hh := h1
        rw [Chk.trunc, Nat.testBit_land, Nat.testBit_two_pow_sub_one] at hh
        have hh' : c.testBit t = true ∧ decide (t < nroots m) = true :=
          Bool.and_eq_true_iff.mp hh
        simpa using hh'.2
      have hc : c.testBit t = true := by
        have hh := h1
        rw [Chk.trunc, Nat.testBit_land, Nat.testBit_two_pow_sub_one] at hh
        exact (Bool.and_eq_true_iff.mp hh).1
      have hroot : root m ⟨t, ht⟩ (vec m w) = 0 := by
        have hc' : (⟨t, ht⟩ : Root m) ∈ ofMask m c := by rwa [mem_ofMask]
        exact (mem_cent_code_iff.mp hmem) ⟨t, ht⟩ hc'
      have hz : (T.zm[w]!).testBit t = true :=
        (mem_ofMask (m := m) (n := T.zm[w]!) (t := ⟨t, ht⟩)).mp
          ((mem_ofMask_zm hT hw ⟨t, ht⟩).mpr hroot)
      rw [h1, hz]
      rfl
    · have h1' : (Chk.trunc (nroots m) c).testBit t = false := by
        simpa using h1
      rw [h1']
      rfl
  have htrue : Chk.subN (Chk.trunc (nroots m) c) (T.zm[w]!) = true := by
    simp [Chk.subN, heq]
  rw [hsub] at htrue
  exact absurd htrue (by simp)

private theorem not_mem_span_pair_of_offPlane {cv cy w : ℕ} (hw : w < 3 ^ dim m)
    (h : Chk.offPlane (dim m) cv cy w = true) :
    vec m w ∉ Submodule.span (ZMod 3) ({vec m cv, vec m cy} : Set (V m)) := by
  intro hmem
  rw [Submodule.mem_span_pair] at hmem
  obtain ⟨a, b, hab⟩ := hmem
  have hcomb : vec m (Chk.combN (dim m) cv cy a.val b.val) = vec m w := by
    rw [vec_combN, ZMod.natCast_zmod_val, ZMod.natCast_zmod_val, hab]
  have hcode : Chk.combN (dim m) cv cy a.val b.val = w := by
    have := congrArg (code m) hcomb
    rwa [code_vec m (combN_lt m cv cy a.val b.val), code_vec m hw] at this
  have hoff := (chk_all_iff.mp h) a.val (ZMod.val_lt a)
  have hoff2 := (chk_all_iff.mp hoff) b.val (ZMod.val_lt b)
  rw [hcode] at hoff2
  simp at hoff2

private theorem not_mem_span_singleton_of_offPlane {cv w : ℕ} (hw : w < 3 ^ dim m)
    (h : Chk.offPlane (dim m) cv 0 w = true) :
    vec m w ∉ Submodule.span (ZMod 3) ({vec m cv} : Set (V m)) := by
  intro hmem
  rw [Submodule.mem_span_singleton] at hmem
  obtain ⟨a, ha⟩ := hmem
  have hcomb : vec m (Chk.combN (dim m) cv 0 a.val 0) = vec m w := by
    rw [vec_combN, vec_zero, ZMod.natCast_zmod_val, ha]
    simp
  have hcode : Chk.combN (dim m) cv 0 a.val 0 = w := by
    have := congrArg (code m) hcomb
    rwa [code_vec m (combN_lt m cv 0 a.val 0), code_vec m hw] at this
  have hoff := (chk_all_iff.mp h) a.val (ZMod.val_lt a)
  have hoff2 := (chk_all_iff.mp hoff) 0 (by norm_num)
  rw [hcode] at hoff2
  simp at hoff2

private theorem refLOK_zero_false {ext q2 : Bool} {cv : ℕ}
    (hvx : vec m cv ≠ 0) : Chk.refLOK T m ext q2 cv .zero = false := by
  simp only [Chk.refLOK]
  have hcvne : cv ≠ 0 := fun h0 => hvx (by rw [h0]; exact vec_zero m)
  simpa using hcvne

private theorem refLOK_disc_false (hT : Chk.tabsOK m T = true) {ext q2 : Bool} {cv : ℕ}
    {ℓ : Finset (Root m)} (hℓeq : ℓ = ofMask m (T.zm[cv]!))
    (hocc : occurs m (Submodule.span (ZMod 3) {vec m cv}) ℓ) (S : ℕ) :
    Chk.refLOK T m ext q2 cv (.disc S) = false := by
  simp only [Chk.refLOK]
  cases hb : Chk.discOK T (nroots m) (T.zm[cv]!) S with
  | false => rfl
  | true =>
    exfalso
    exact not_isComp_of_discOK hT hb (Vanish m (Submodule.span (ZMod 3) {vec m cv}))
      (hℓeq ▸ hocc)

private theorem refLOK_cent_false (hT : Chk.tabsOK m T = true) {ext q2 : Bool} {cv : ℕ}
    {ℓ : Finset (Root m)} (hℓeq : ℓ = ofMask m (T.zm[cv]!))
    (hcent : cent m ℓ = Submodule.span (ZMod 3) {vec m cv}) (w : ℕ) :
    Chk.refLOK T m ext q2 cv (.cent w) = false := by
  simp only [Chk.refLOK]
  by_cases hb : (decide (w < 3 ^ dim m) &&
      Chk.subN (Chk.trunc (nroots m) (T.zm[cv]!)) (T.zm[w]!) &&
      Chk.offPlane (dim m) cv 0 w) = true
  · exfalso
    simp only [Bool.and_eq_true_iff, decide_eq_true_eq] at hb
    obtain ⟨⟨hw, hsub⟩, hoff⟩ := hb
    have hmem : vec m w ∈ cent m ℓ := by
      rw [hℓeq]
      exact mem_cent_of_subN_zm hT hw hsub
    rw [hcent] at hmem
    exact not_mem_span_singleton_of_offPlane hw hoff hmem
  · simpa using hb

private theorem refLOK_label_false (hT : Chk.tabsOK m T = true) {ext q2 : Bool} {cv : ℕ}
    {ℓ : Finset (Root m)} (hℓeq : ℓ = ofMask m (T.zm[cv]!))
    (hlam : LargeEvenInLambda2 (label m ℓ)) :
    Chk.refLOK T m ext q2 cv .label = false := by
  simp only [Chk.refLOK]
  have hL : Chk.lam2N (Chk.labelOf T m (T.zm[cv]!)) = true := by
    rw [labelOf_eq hT, ← hℓeq]
    exact (lam2N_encL (label m ℓ)).mpr hlam
  rw [hL]
  rfl

private theorem refLOK_q2_false (hT : Chk.tabsOK m T = true) {ext q2 : Bool} {cv : ℕ}
    {ℓ : Finset (Root m)} (hℓeq : ℓ = ofMask m (T.zm[cv]!))
    (hq2 : q2 = true → ∃ lab : LargeEvenLabel, GGLabQTwo 3 lab ∧ GGLabelIso lab (label m ℓ)) :
    Chk.refLOK T m ext q2 cv .q2 = false := by
  simp only [Chk.refLOK]
  by_cases hb : (q2 && !Chk.q2N (Chk.labelOf T m (T.zm[cv]!))) = true
  · exfalso
    obtain ⟨hq2t, hq2n⟩ := Bool.and_eq_true_iff.mp hb
    have hQ : Chk.q2N (Chk.labelOf T m (T.zm[cv]!)) = true := by
      rw [labelOf_eq hT, ← hℓeq]
      exact (q2N_encL (label m ℓ)).mpr (hq2 hq2t)
    rw [hQ] at hq2n
    simp at hq2n
  · simpa using hb

private theorem refLOK_ins_false (hT : Chk.tabsOK m T = true) {ext q2 : Bool} {cv : ℕ}
    {ℓ : Finset (Root m)} (hℓeq : ℓ = ofMask m (T.zm[cv]!))
    (hins : vec m cv ∈ inside m ℓ ↔ ext = false) (coef : List (ℕ × ℕ)) :
    Chk.refLOK T m ext q2 cv (.ins coef) = false := by
  simp only [Chk.refLOK]
  cases hb : (ext && Chk.inOK T (dim m) (nroots m) (T.zm[cv]!) coef cv) with
  | false => rfl
  | true =>
    exfalso
    obtain ⟨hext, hin⟩ := Bool.and_eq_true_iff.mp hb
    have hmem : vec m cv ∈ inside m ℓ := by
      rw [hℓeq]
      exact inOK_sound hT hin
    rw [hins] at hmem
    rw [hext] at hmem
    simp at hmem

private theorem refLOK_outs_false (hT : Chk.tabsOK m T = true) {ext q2 : Bool} {cv : ℕ}
    {ℓ : Finset (Root m)} (hℓeq : ℓ = ofMask m (T.zm[cv]!))
    (hins : vec m cv ∈ inside m ℓ ↔ ext = false) (φ : ℕ) :
    Chk.refLOK T m ext q2 cv (.outs φ) = false := by
  simp only [Chk.refLOK]
  cases hb : (!ext && Chk.outOK T (dim m) (nroots m) (T.zm[cv]!) φ cv) with
  | false => rfl
  | true =>
    exfalso
    obtain ⟨hext, hout⟩ := Bool.and_eq_true_iff.mp hb
    have hext' : ext = false := by simpa using hext
    have hmem : vec m cv ∉ inside m ℓ := by
      rw [hℓeq]
      exact outOK_sound hT hout
    rw [hins] at hmem
    rw [hext'] at hmem
    simp at hmem

theorem refLOK_false (hT : Chk.tabsOK m T = true) {ext q2 : Bool} {cv : ℕ}
    (hcv : cv < 3 ^ dim m) {ℓ : Finset (Root m)} (hℓ : LineHyp m ext q2 (vec m cv) ℓ)
    (e : Chk.RefL) : Chk.refLOK T m ext q2 cv e = false := by
  have hℓeq : ℓ = ofMask m (T.zm[cv]!) :=
    eq_ofMask_zm_of_occurs hT hcv hℓ.2.2.2.1 hℓ.2.2.2.2.1
  cases e with
  | zero => exact refLOK_zero_false hℓ.1
  | disc S => exact refLOK_disc_false hT hℓeq hℓ.2.2.2.1 S
  | cent w => exact refLOK_cent_false hT hℓeq hℓ.2.2.2.2.1 w
  | label => exact refLOK_label_false hT hℓeq hℓ.2.1.2
  | q2 => exact refLOK_q2_false hT hℓeq hℓ.2.2.1
  | ins coef => exact refLOK_ins_false hT hℓeq hℓ.2.2.2.2.2 coef
  | outs φ => exact refLOK_outs_false hT hℓeq hℓ.2.2.2.2.2 φ

theorem refPOK_false (hT : Chk.tabsOK m T = true) {cv cy : ℕ} (hcv : cv < 3 ^ dim m)
    (hcy : cy < 3 ^ dim m) {j : Finset (Root m)}
    (hj : PlaneHyp m (Submodule.span (ZMod 3) {vec m cv, vec m cy}) j) (e : Chk.RefP) :
    Chk.refPOK T m cv cy e = false := by
  obtain ⟨hadm, hocc, hcent⟩ := hj
  have hjeq : j = ofMask m (T.zm[cv]! &&& T.zm[cy]!) :=
    eq_ofMask_land_zm_of_occurs hT hcv hcy hocc hcent
  cases e with
  | disc S =>
    simp only [Chk.refPOK]
    cases hb : Chk.discOK T (nroots m) (T.zm[cv]! &&& T.zm[cy]!) S with
    | false => rfl
    | true =>
      exfalso
      exact not_isComp_of_discOK hT hb
        (Vanish m (Submodule.span (ZMod 3) {vec m cv, vec m cy})) (hjeq ▸ hocc)
  | cent w =>
    simp only [Chk.refPOK]
    by_cases hb : (decide (w < 3 ^ dim m) &&
        Chk.subN (Chk.trunc (nroots m) (T.zm[cv]! &&& T.zm[cy]!)) (T.zm[w]!) &&
        Chk.offPlane (dim m) cv cy w) = true
    ·
      exfalso
      simp only [Bool.and_eq_true_iff, decide_eq_true_eq] at hb
      obtain ⟨⟨hw, hsub⟩, hoff⟩ := hb
      have hmem : vec m w ∈ cent m j := by
        rw [hjeq]
        exact mem_cent_of_subN_zm hT hw hsub
      rw [hcent] at hmem
      exact not_mem_span_pair_of_offPlane hw hoff hmem
    · simpa using hb
  | label =>
    simp only [Chk.refPOK]
    have hL : Chk.lam2N (Chk.labelOf T m (T.zm[cv]! &&& T.zm[cy]!)) = true := by
      rw [labelOf_eq hT, ← hjeq]
      exact (lam2N_encL (label m j)).mpr hadm.2
    rw [hL]
    rfl

theorem refCOK_false (hT : Chk.tabsOK m T = true) {cv cz : ℕ} (hcv : cv < 3 ^ dim m)
    (hcz : cz < 3 ^ dim m) {k : Finset (Root m)} (hk : CandHyp m (vec m cv) (vec m cz) k)
    (e : Chk.RefC) : Chk.refCOK T m cv cz e = false := by
  obtain ⟨hadm, hocc, hcent, hvx⟩ := hk
  have hkeq : k = ofMask m (T.zm[cz]!) := eq_ofMask_zm_of_occurs hT hcz hocc hcent
  cases e with
  | disc S =>
    simp only [Chk.refCOK]
    cases hb : Chk.discOK T (nroots m) (T.zm[cz]!) S with
    | false => rfl
    | true =>
      exfalso
      exact not_isComp_of_discOK hT hb (Vanish m (Submodule.span (ZMod 3) {vec m cz}))
        (hkeq ▸ hocc)
  | cent w =>
    simp only [Chk.refCOK]
    by_cases hb : (decide (w < 3 ^ dim m) &&
        Chk.subN (Chk.trunc (nroots m) (T.zm[cz]!)) (T.zm[w]!) &&
        Chk.offPlane (dim m) cz 0 w) = true
    ·
      exfalso
      simp only [Bool.and_eq_true_iff, decide_eq_true_eq] at hb
      obtain ⟨⟨hw, hsub⟩, hoff⟩ := hb
      have hmem : vec m w ∈ cent m k := by
        rw [hkeq]
        exact mem_cent_of_subN_zm hT hw hsub
      rw [hcent] at hmem
      exact not_mem_span_singleton_of_offPlane hw hoff hmem
    · simpa using hb
  | label =>
    simp only [Chk.refCOK]
    have hL : Chk.lam2N (Chk.labelOf T m (T.zm[cz]!)) = true := by
      rw [labelOf_eq hT, ← hkeq]
      exact (lam2N_encL (label m k)).mpr hadm.2
    rw [hL]
    rfl
  | inCent =>
    simp only [Chk.refCOK]
    cases hb : Chk.subN (Chk.trunc (nroots m) (T.zm[cz]!)) (T.zm[cv]!) with
    | false => rfl
    | true =>
      exfalso
      have hmem : vec m cv ∈ cent m k := by
        rw [hkeq]
        exact mem_cent_of_subN_zm hT hcv hb
      exact hvx hmem

private theorem pivN_lt_of_ne_zero {v : V m} (hv : v ≠ 0) :
    Chk.pivN (dim m) (code m v) < dim m := by
  by_contra hcon
  have hp_eq : Chk.pivN (dim m) (code m v) = dim m := by
    have := pivN_le (dim m) (code m v); omega
  exact hv (eq_zero_of_dig_eq_zero fun k =>
    dig_eq_zero_of_lt_pivN (by rw [hp_eq]; exact k.isLt))

private theorem apply_pivN_ne_zero {v : V m} (h : Chk.pivN (dim m) (code m v) < dim m) :
    v ⟨Chk.pivN (dim m) (code m v), h⟩ ≠ 0 := by
  have hd := dig_pivN_ne_zero h
  have hv : v ⟨Chk.pivN (dim m) (code m v), h⟩ =
      (Chk.dig (code m v) (Chk.pivN (dim m) (code m v)) : ZMod 3) := by
    rw [← congrFun (vec_code m v) ⟨_, h⟩]; rfl
  rw [hv]
  exact natCast_ne_zero_three (dig_lt_three _ _) hd

private theorem exists_mem_notMem_span {U : Submodule (ZMod 3) (V m)} {vx : V m}
    (hvx : vx ≠ 0) (hU : finrank (ZMod 3) U = 2) :
    ∃ y ∈ U, y ∉ Submodule.span (ZMod 3) {vx} := by
  have hnotle : ¬ U ≤ Submodule.span (ZMod 3) {vx} := by
    intro hle
    have h1 : finrank (ZMod 3) U ≤ finrank (ZMod 3) (Submodule.span (ZMod 3) {vx}) :=
      Submodule.finrank_mono hle
    have h2 : finrank (ZMod 3) (Submodule.span (ZMod 3) {vx}) = 1 := by
      rw [show Submodule.span (ZMod 3) {vx} = ZMod 3 ∙ vx from rfl]
      exact finrank_span_singleton hvx
    omega
  obtain ⟨y, hyU, hyW⟩ := Set.nonempty_of_not_subset hnotle
  exact ⟨y, hyU, hyW⟩

private theorem exists_pivot_step {U : Submodule (ZMod 3) (V m)} {vx y : V m}
    (hyU : y ∈ U) (hxU : vx ∈ U) (hy : y ∉ Submodule.span (ZMod 3) {vx})
    {p : ℕ} (hp : p < dim m) (hvp : vx ⟨p, hp⟩ ≠ 0) :
    ∃ y₁ : V m, y₁ ∈ U ∧ y₁ ∉ Submodule.span (ZMod 3) {vx} ∧ y₁ ⟨p, hp⟩ = 0 := by
  refine ⟨y - (y ⟨p, hp⟩ * (vx ⟨p, hp⟩)⁻¹) • vx, ?_, ?_, ?_⟩
  · exact U.sub_mem hyU (U.smul_mem _ hxU)
  · intro hmem
    apply hy
    have h1 : y = (y - (y ⟨p, hp⟩ * (vx ⟨p, hp⟩)⁻¹) • vx) +
        (y ⟨p, hp⟩ * (vx ⟨p, hp⟩)⁻¹) • vx := by abel
    rw [h1]
    exact Submodule.add_mem _ hmem (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
  · show y ⟨p, hp⟩ - (y ⟨p, hp⟩ * (vx ⟨p, hp⟩)⁻¹) * vx ⟨p, hp⟩ = 0
    rw [mul_assoc, inv_mul_cancel₀ hvp, mul_one, sub_self]

private theorem apply_eq_zero_of_dig_eq_zero {v : V m} {k : Fin (dim m)}
    (h : Chk.dig (code m v) k = 0) : v k = 0 := by
  have hv : v k = (Chk.dig (code m v) k : ZMod 3) := by
    rw [← congrFun (vec_code m v) k]; rfl
  rw [hv, h]; rfl

private theorem dig_smul_zero {c : ZMod 3} {v : V m} {k : Fin (dim m)} (h : v k = 0) :
    Chk.dig (code m (c • v)) k = 0 := by
  rw [chk_dig_code m (c • v) k]
  show (c * v k).val = 0
  rw [h, mul_zero]
  exact (ZMod.val_eq_zero (0 : ZMod 3)).mpr rfl

private theorem dig_eq_one_of_apply_eq_one {v : V m} {k : Fin (dim m)} (h : v k = 1) :
    Chk.dig (code m v) k = 1 := by
  rw [chk_dig_code m v k, h]
  exact ZMod.val_one 3

private theorem exists_scale_step {U : Submodule (ZMod 3) (V m)} {vx y₁ : V m}
    (hy₁U : y₁ ∈ U) (hy₁ : y₁ ∉ Submodule.span (ZMod 3) {vx})
    {p : ℕ} (hp : p < dim m) (hy₁p : y₁ ⟨p, hp⟩ = 0) :
    ∃ y₂ : V m, y₂ ∈ U ∧ y₂ ∉ Submodule.span (ZMod 3) {vx} ∧
      Chk.dig (code m y₂) p = 0 ∧
      Chk.pivN (dim m) (code m y₂) < dim m ∧
      Chk.dig (code m y₂) (Chk.pivN (dim m) (code m y₂)) = 1 := by
  have hy₁ne : y₁ ≠ 0 := fun h0 => hy₁ (by rw [h0]; exact Submodule.zero_mem _)
  have hq_lt : Chk.pivN (dim m) (code m y₁) < dim m := pivN_lt_of_ne_zero hy₁ne
  have hq_ne : y₁ ⟨Chk.pivN (dim m) (code m y₁), hq_lt⟩ ≠ 0 := apply_pivN_ne_zero hq_lt
  set c : ZMod 3 := (y₁ ⟨Chk.pivN (dim m) (code m y₁), hq_lt⟩)⁻¹ with hc
  set y₂ : V m := c • y₁ with hy₂
  have hy₂q : y₂ ⟨Chk.pivN (dim m) (code m y₁), hq_lt⟩ = 1 := by
    show c * y₁ ⟨Chk.pivN (dim m) (code m y₁), hq_lt⟩ = 1
    rw [hc]
    exact inv_mul_cancel₀ hq_ne
  have hy₂p : y₂ ⟨p, hp⟩ = 0 := by
    show c * y₁ ⟨p, hp⟩ = 0
    rw [hy₁p, mul_zero]
  have hmin : ∀ k, k < Chk.pivN (dim m) (code m y₁) → Chk.dig (code m y₂) k = 0 := by
    intro k hk
    have hk' : k < dim m := by have := pivN_le (dim m) (code m y₁); omega
    have h1 : y₁ ⟨k, hk'⟩ = 0 := apply_eq_zero_of_dig_eq_zero (dig_eq_zero_of_lt_pivN hk)
    exact dig_smul_zero h1
  have hpiv : Chk.pivN (dim m) (code m y₂) = Chk.pivN (dim m) (code m y₁) := by
    refine pivN_eq_of hq_lt ?_ hmin
    rw [dig_eq_one_of_apply_eq_one hy₂q]
    norm_num
  refine ⟨y₂, ?_, ?_, ?_, by rw [hpiv]; exact hq_lt, ?_⟩
  · rw [hy₂]; exact U.smul_mem _ hy₁U
  · intro hmem
    apply hy₁
    have h1 : y₁ = y₁ ⟨Chk.pivN (dim m) (code m y₁), hq_lt⟩ • y₂ := by
      rw [hy₂, hc, smul_smul, mul_inv_cancel₀ hq_ne, one_smul]
    rw [h1]
    exact Submodule.smul_mem _ _ hmem
  · exact dig_smul_zero hy₁p
  · rw [hpiv]
    exact dig_eq_one_of_apply_eq_one hy₂q

private theorem exists_canon_vec {U : Submodule (ZMod 3) (V m)} {vx : V m}
    (hvx : vx ≠ 0) (hU : finrank (ZMod 3) U = 2) (hxU : vx ∈ U) :
    ∃ y₂ : V m, y₂ ∈ U ∧ y₂ ∉ Submodule.span (ZMod 3) {vx} ∧
      Chk.canonN (dim m) (code m vx) (code m y₂) = true := by
  obtain ⟨y, hyU, hyW⟩ := exists_mem_notMem_span hvx hU
  have hp_lt := pivN_lt_of_ne_zero hvx
  have hvp := apply_pivN_ne_zero hp_lt
  obtain ⟨y₁, hy₁U, hy₁, hy₁p⟩ := exists_pivot_step hyU hxU hyW hp_lt hvp
  obtain ⟨y₂, hy₂U, hy₂, hd0, hpiv, hd1⟩ := exists_scale_step hy₁U hy₁ hp_lt hy₁p
  refine ⟨y₂, hy₂U, hy₂, ?_⟩
  simp only [Chk.canonN, Bool.and_eq_true_iff, decide_eq_true_eq, beq_iff_eq]
  exact ⟨⟨⟨code_lt m y₂, hd0⟩, hpiv⟩, hd1⟩

private theorem eq_span_pair_of_finrank {U : Submodule (ZMod 3) (V m)} {vx y : V m}
    (hvx : vx ≠ 0) (hU : finrank (ZMod 3) U = 2) (hxU : vx ∈ U) (hyU : y ∈ U)
    (hy : y ∉ Submodule.span (ZMod 3) {vx}) :
    U = Submodule.span (ZMod 3) ({vx, y} : Set (V m)) := by
  have hle : Submodule.span (ZMod 3) ({vx, y} : Set (V m)) ≤ U := by
    rw [Submodule.span_le]
    rintro z (rfl | rfl)
    · exact hxU
    · exact hyU
  have hmono : Submodule.span (ZMod 3) ({vx} : Set (V m)) ≤
      Submodule.span (ZMod 3) ({vx, y} : Set (V m)) := by
    rw [Submodule.span_le]
    intro z hz
    rw [Set.mem_singleton_iff] at hz
    subst hz
    exact Submodule.subset_span (Or.inl rfl)
  have hne : Submodule.span (ZMod 3) ({vx} : Set (V m)) ≠
      Submodule.span (ZMod 3) ({vx, y} : Set (V m)) := by
    intro heq
    apply hy
    rw [heq]
    exact Submodule.subset_span (Or.inr rfl)
  have hlt : Submodule.span (ZMod 3) ({vx} : Set (V m)) <
      Submodule.span (ZMod 3) ({vx, y} : Set (V m)) := lt_of_le_of_ne hmono hne
  have hspan1 : finrank (ZMod 3) (Submodule.span (ZMod 3) ({vx} : Set (V m))) = 1 := by
    rw [show Submodule.span (ZMod 3) ({vx} : Set (V m)) = ZMod 3 ∙ vx from rfl]
    exact finrank_span_singleton hvx
  have hlt2 : finrank (ZMod 3) (Submodule.span (ZMod 3) ({vx} : Set (V m))) <
      finrank (ZMod 3) (Submodule.span (ZMod 3) ({vx, y} : Set (V m))) :=
    Submodule.finrank_lt_finrank_of_lt hlt
  have hle2 : finrank (ZMod 3) (Submodule.span (ZMod 3) ({vx, y} : Set (V m))) ≤
      finrank (ZMod 3) U := Submodule.finrank_mono hle
  have h2 : finrank (ZMod 3) (Submodule.span (ZMod 3) ({vx, y} : Set (V m))) = 2 := by omega
  have hfin_eq : finrank (ZMod 3) (Submodule.span (ZMod 3) ({vx, y} : Set (V m))) =
      finrank (ZMod 3) U := by rw [h2]; exact hU.symm
  exact (Submodule.eq_of_le_of_finrank_eq hle hfin_eq).symm

private theorem exists_canon_second {U : Submodule (ZMod 3) (V m)} {vx : V m}
    (hvx : vx ≠ 0) (hU : finrank (ZMod 3) U = 2) (hxU : vx ∈ U) :
    ∃ cy : ℕ, cy < 3 ^ dim m ∧ vec m cy ∈ U ∧
      vec m cy ∉ Submodule.span (ZMod 3) {vx} ∧
      U = Submodule.span (ZMod 3) ({vx, vec m cy} : Set (V m)) ∧
      Chk.canonN (dim m) (code m vx) cy = true := by
  obtain ⟨y₂, hy₂U, hy₂, hcanon⟩ := exists_canon_vec hvx hU hxU
  have hUeq : U = Submodule.span (ZMod 3) ({vx, y₂} : Set (V m)) :=
    eq_span_pair_of_finrank hvx hU hxU hy₂U hy₂
  refine ⟨code m y₂, code_lt m y₂, ?_, ?_, ?_, ?_⟩
  · rw [vec_code m y₂]; exact hy₂U
  · rw [vec_code m y₂]; exact hy₂
  · rw [hUeq, vec_code m y₂]
  · exact hcanon

theorem scanN_sound (hT : Chk.tabsOK m T = true) {ext q2 : Bool} {S : Chk.Search}
    {body : ℕ → ℕ → Bool} (h : Chk.scanN T m ext q2 S body = true) {vx : V m}
    {ℓ : Finset (Root m)} (hℓ : LineHyp m ext q2 vx ℓ) {U : Submodule (ZMod 3) (V m)}
    (hU : finrank (ZMod 3) U = 2) (hxU : vx ∈ U) {j : Finset (Root m)} (hj : PlaneHyp m U j) :
    ∃ cv cy : ℕ, cv < 3 ^ dim m ∧ cy < 3 ^ dim m ∧ vx = vec m cv ∧
      vec m cy ∉ Submodule.span (ZMod 3) {vec m cv} ∧
      U = Submodule.span (ZMod 3) {vec m cv, vec m cy} ∧ ℓ = ofMask m (T.zm[cv]!) ∧
      j = ofMask m (T.zm[cv]! &&& T.zm[cy]!) ∧ body cv cy = true := by
  have hvx : vx ≠ 0 := hℓ.1
  have hscan := h
  simp only [Chk.scanN] at hscan
  have hcv : code m vx < 3 ^ dim m := code_lt m vx
  have hrow := (chk_all_iff.mp hscan) (code m vx) hcv
  obtain ⟨cy, hcy_lt, -, hcy_notmem, hUeq, hcanon⟩ := exists_canon_second hvx hU hxU
  have hbody : body (code m vx) cy = true := by
    have hrr : (!Chk.canonN (dim m) (code m vx) cy ||
        (match S.plane (code m vx) cy with
          | some e => Chk.refPOK T m (code m vx) cy e
          | none => false) || body (code m vx) cy) = true := by
      cases hl : S.line (code m vx) with
      | none =>
        simp only [hl, Bool.false_or] at hrow
        exact (chk_all_iff.mp hrow) cy hcy_lt
      | some e =>
        have he := refLOK_false hT hcv (by rwa [vec_code m vx]) e
        simp only [hl, he, Bool.false_or] at hrow
        exact (chk_all_iff.mp hrow) cy hcy_lt
    have hplane : (match S.plane (code m vx) cy with
        | some e => Chk.refPOK T m (code m vx) cy e
        | none => false) = false := by
      cases hp : S.plane (code m vx) cy with
      | none => rfl
      | some e =>
        refine refPOK_false (j := j) hT hcv hcy_lt ?_ e
        rw [vec_code m vx, ← hUeq]
        exact hj
    simpa [hcanon, hplane] using hrr
  have hℓeq : ℓ = ofMask m (T.zm[code m vx]!) := by
    refine eq_ofMask_zm_of_occurs hT hcv ?_ ?_
    · rw [vec_code m vx]; exact hℓ.2.2.2.1
    · rw [vec_code m vx]; exact hℓ.2.2.2.2.1
  have hjeq : j = ofMask m (T.zm[code m vx]! &&& T.zm[cy]!) := by
    refine eq_ofMask_land_zm_of_occurs hT hcv hcy_lt ?_ ?_
    · rw [vec_code m vx, ← hUeq]; exact hj.2.1
    · rw [vec_code m vx, ← hUeq]; exact hj.2.2
  rw [← vec_code m vx] at hcy_notmem hUeq
  exact ⟨code m vx, cy, hcv, hcy_lt, (vec_code m vx).symm, hcy_notmem, hUeq, hℓeq, hjeq, hbody⟩

theorem candScanN_sound (hT : Chk.tabsOK m T = true) {S : Chk.Search} {cv cy : ℕ}
    {body : ℕ → ℕ → Bool} (h : Chk.candScanN T m S cv cy body = true) (hcv : cv < 3 ^ dim m)
    (hcy : cy < 3 ^ dim m) {z : V m} (hz : z ∈ Submodule.span (ZMod 3) {vec m cv, vec m cy})
    (hzx : z ∉ Submodule.span (ZMod 3) {vec m cv}) {k : Finset (Root m)}
    (hk : CandHyp m (vec m cv) z k) :
    ∃ a b : ℕ, a < 3 ∧ (b = 1 ∨ b = 2) ∧ z = vec m (Chk.combN (dim m) cv cy a b) ∧
      k = ofMask m (T.zm[Chk.combN (dim m) cv cy a b]!) ∧ body a b = true := by
  have hcy' : cy < 3 ^ dim m := hcy
  obtain ⟨α, β, hαβ⟩ := Submodule.mem_span_pair.mp hz
  have hβ : β ≠ 0 := by
    intro h0
    apply hzx
    rw [← hαβ, h0, zero_smul, add_zero]
    exact Submodule.smul_mem _ _ (Submodule.subset_span (by simp))
  have hb1 : β.val = 1 ∨ β.val = 2 := by
    have hlt : β.val < 3 := ZMod.val_lt β
    have hne : β.val ≠ 0 := fun h0 => hβ ((ZMod.val_eq_zero β).mp h0)
    omega
  have hzvec : z = vec m (Chk.combN (dim m) cv cy α.val β.val) := by
    rw [← hαβ, vec_combN, ZMod.natCast_zmod_val, ZMod.natCast_zmod_val]
  have hcz_lt : Chk.combN (dim m) cv cy α.val β.val < 3 ^ dim m :=
    combN_lt m cv cy α.val β.val
  have hscan := h
  simp only [Chk.candScanN] at hscan
  have h1 := (chk_all_iff.mp hscan) α.val (ZMod.val_lt α)
  have hb' : β.val - 1 < 2 := by omega
  have hbs : β.val - 1 + 1 = β.val := by omega
  have h2 := (chk_all_iff.mp h1) (β.val - 1) hb'
  rw [hbs] at h2
  have hbody : body α.val β.val = true := by
    cases hc : S.cand cv (Chk.combN (dim m) cv cy α.val β.val) with
    | none =>
      simp only [hc, Bool.false_or] at h2
      exact h2
    | some e =>
      have hk' : CandHyp m (vec m cv) (vec m (Chk.combN (dim m) cv cy α.val β.val)) k := by
        rw [← hzvec]; exact hk
      have hfalse := refCOK_false hT hcv hcz_lt hk' e
      simp only [hc, hfalse, Bool.false_or] at h2
      exact h2
  refine ⟨α.val, β.val, ZMod.val_lt α, hb1, hzvec, ?_, hbody⟩
  have hk' : CandHyp m (vec m cv) (vec m (Chk.combN (dim m) cv cy α.val β.val)) k := by
    rw [← hzvec]; exact hk
  exact eq_ofMask_zm_of_occurs hT hcz_lt hk'.2.1 hk'.2.2.1

private theorem cent_eq_span_of_lineOK (hT : Chk.tabsOK m T = true) {cz : ℕ}
    (hcz : cz < 3 ^ dim m) {rows : List ℕ} {B : Array (Array ℤ)}
    (hline : Chk.lineOK T (dim m) (nroots m) rows cz B = true) :
    cent m (ofMask m (T.zm[cz]!)) = Submodule.span (ZMod 3) {vec m cz} := by
  have hmemk : ∀ t : Root m, t ∈ ofMask m (T.zm[cz]!) ↔ root m t (vec m cz) = 0 :=
    fun t => mem_ofMask_zm hT hcz t
  have hle : cent m (ofMask m (T.zm[cz]!)) ≤ Submodule.span (ZMod 3) {vec m cz} := by
    intro v hv
    have hv' : v ∈ cent m (ofMask m (T.zm[cz]!)) := hv
    refine (lineOK_sound hT hline v).mp ?_
    intro t ht
    obtain ⟨hlt, hroot⟩ := lineOK_rows hT hline ht
    have ht' : t ∈ ofMask m (T.zm[cz]!) := by
      have := (hmemk ⟨t, hlt⟩).mpr hroot
      simpa using this
    exact (mem_cent_code_iff.mp hv') t ht'
  have hcz_mem : vec m cz ∈ cent m (ofMask m (T.zm[cz]!)) := by
    rw [mem_cent_code_iff]
    intro t ht
    exact (hmemk t).mp ht
  refine le_antisymm hle ?_
  rw [Submodule.span_le]
  intro v hv
  rw [Set.mem_singleton_iff] at hv
  subst hv
  exact hcz_mem

private theorem normalizerGroup_le_of_plane (hT : Chk.tabsOK m T = true) {cz : ℕ}
    (hcz : cz < 3 ^ dim m) {U : Submodule (ZMod 3) (V m)} {j : Finset (Root m)}
    (hj : PlaneHyp m U j) (hzU : vec m cz ∈ U) (hnotB2 : Chk.notB2 m (T.zm[cz]!) = true) :
    normalizerGroup m j ≤ normalizerGroup m (ofMask m (T.zm[cz]!)) := by
  have hsub : j ≤ ofMask m (T.zm[cz]!) := by
    intro t ht
    exact (mem_ofMask_zm hT hcz t).mpr (hj.2.1.2.1 t ht (vec m cz) hzU)
  have hweyl : weyl m j ≤ weyl m (ofMask m (T.zm[cz]!)) := by
    rw [weyl, weyl]
    exact Subgroup.closure_mono (Set.image_mono (Finset.coe_subset.mpr hsub))
  calc normalizerGroup m j ≤ weyl m j := normalizerGroup_le_weyl j
    _ ≤ weyl m (ofMask m (T.zm[cz]!)) := hweyl
    _ = normalizerGroup m (ofMask m (T.zm[cz]!)) := (normalizerGroup_ofMask hnotB2).symm

theorem candidate_of_candOK (hT : Chk.tabsOK m T = true) {cv cz : ℕ} (hcv : cv < 3 ^ dim m)
    {rows : List ℕ} {B : Array (Array ℤ)} (h : Chk.candOK T m cv cz rows B = true)
    {U : Submodule (ZMod 3) (V m)} {j : Finset (Root m)} (hj : PlaneHyp m U j)
    (hzU : vec m cz ∈ U) :
    Candidate (excRaw m) (vec m cv) j (vec m cz) (ofMask m (T.zm[cz]!)) := by
  have hcan := h
  simp only [Chk.candOK, Bool.and_eq_true_iff, decide_eq_true_eq] at hcan
  obtain ⟨⟨⟨⟨⟨hcz, hconn⟩, hline⟩, hlam⟩, hnotsub⟩, hnotB2⟩ := hcan
  have hnotsub' : Chk.subN (Chk.trunc (nroots m) (T.zm[cz]!)) (T.zm[cv]!) = false := by
    simpa using hnotsub
  have hmemk : ∀ t : Root m, t ∈ ofMask m (T.zm[cz]!) ↔ root m t (vec m cz) = 0 :=
    fun t => mem_ofMask_zm hT hcz t
  have hconn' := connN_sound hT hconn
  have hcomp : occurs m (Submodule.span (ZMod 3) {vec m cz}) (ofMask m (T.zm[cz]!)) := by
    refine ⟨hconn'.1, ?_, ?_, hconn'.2⟩
    · intro i hi
      rw [vanish_span_singleton_iff]
      exact (hmemk i).mp hi
    · intro i hi j hj hadj
      exact (hmemk j).mpr (vanish_span_singleton_iff.mp hj)
  have hlam' : LargeEvenInLambda2 (label m (ofMask m (T.zm[cz]!))) := by
    refine (lam2N_encL (label m (ofMask m (T.zm[cz]!)))).mp ?_
    rw [← labelOf_eq hT]
    exact hlam
  have hnotcent : vec m cv ∉ cent m (ofMask m (T.zm[cz]!)) :=
    not_mem_cent_of_not_subN hT hcv hnotsub'
  exact ⟨⟨⟨Submodule.span (ZMod 3) {vec m cz}, hcomp⟩, hlam'⟩, hcomp,
    cent_eq_span_of_lineOK hT hcz hline,
    normalizerGroup_le_of_plane hT hcz hj hzU hnotB2, hnotcent⟩


end CFSG.StandardType.GGQ2Frame.ExcRaw

end

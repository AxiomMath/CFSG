module

public import CFSG.Monster.Existence.TwoPoint.Fi23Sp8Cert
public import CFSG.Sporadic.Bridge.Fi23Surj
public import CFSG.Sporadic.Fi23.Centralizer

public section

namespace CFSG.Monster.Existence.Fi23Sp8

open CFSG.Sporadic.Fi23 CFSG.Sporadic.Bridge.Fi23 CFSG.Sporadic.Th CFSG.Sporadic.Th.Native
open CFSG.Monster.Existence.Fi23Sp8.Native CFSG.Sporadic.Fi23.Native
  CFSG.Sporadic.Bridge.Fi23GPL.Native

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

noncomputable abbrev sp8G4 : Array Table := #[orb.alpha, orb.alpha, orb.beta, invT 31671 orb.beta]

noncomputable abbrev sp8S : Search := search sp8G4 imgT imgTv

theorem sp8_checks :
    sp8Checks sp8G4 imgT imgTv (dTable orb) sp8S = true := by
  have h := sp8Entry_eq_true
  have e : sp8Entry () = sp8Checks sp8G4 (imgWords.map (wordT 31671 (seedLetter sp8G4)))
      ((imgWords.map (wordT 31671 (seedLetter sp8G4))).map (invT 31671)) (dTable orb)
      (search sp8G4 (imgWords.map (wordT 31671 (seedLetter sp8G4)))
        ((imgWords.map (wordT 31671 (seedLetter sp8G4))).map (invT 31671))) := rfl
  rw [e, seedLetter_eq] at h
  exact h

noncomputable def sp8F : Search := frozen sp8S

theorem sp8_checksF :
    sp8Checks sp8G4 imgT imgTv (dTable orb) sp8F = true := by
  rw [sp8F, frozen_eq]
  exact sp8_checks

theorem sp8_parts :
    imgConjOK = true ∧ rootCheck sp8G4 sp8F = true ∧ labCheck sp8G4 imgT sp8F = true ∧
      pathCheck imgT imgTv sp8F = true ∧ vecCheck sp8F = true ∧
      transCheck imgT imgTv sp8F = true ∧ sepCheck imgT imgTv sp8F = true ∧
      genCheck (dTable orb) sp8F = true ∧ countCheck sp8F = true := by
  have h := sp8_checksF
  unfold sp8Checks at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩

theorem rootCheck_parts :
    sp8F.roots = #[piPt sp8G4 0, piPt sp8G4 8, 0] ∧
    sp8F.lab.size = 31671 ∧ sp8F.par.size = 31671 ∧ sp8F.gen.size = 31671 ∧
    ∀ c < 3, sp8F.lab[sp8F.roots[c]!]! = c := by
  have h := sp8_parts.2.1
  unfold rootCheck at h
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range] at h
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := h
  exact ⟨h1, h2, h3, h4, h5⟩

theorem imgG_neg {z : ℤ} (hz : z ≠ 0) : imgG (-z) = (imgG z)⁻¹ := by
  unfold imgG
  rcases lt_or_gt_of_ne hz with h | h
  · have h1 : ¬ (0 < z) := by omega
    have h2 : 0 < -z := by omega
    rw [ite_eq_right h1, ite_eq_left h2, inv_inv]
  · have h1 : ¬ (0 < -z) := by omega
    rw [ite_eq_right h1, ite_eq_left h, neg_neg]

theorem wordG_append {G : Type*} [Group G] (g : ℤ → G) (u v : List ℤ) :
    wordG g (u ++ v) = wordG g u * wordG g v := by
  simp [wordG]

theorem wordG_invWord {w : List ℤ} (hw : ∀ z ∈ w, z ≠ 0) :
    wordG imgG (invWord w) = (wordG imgG w)⁻¹ := by
  unfold wordG invWord
  have h1 : List.map imgG (List.map (fun z => -z) w.reverse) =
      ((List.map imgG w).map fun x => x⁻¹).reverse := by
    rw [List.map_map, List.map_map, ← List.map_reverse]
    apply List.map_congr_left
    intro z hz
    simp [Function.comp, imgG_neg (hw z (List.mem_reverse.1 hz))]
  rw [h1, ← List.prod_inv_reverse]

theorem evalWord_eq
    (w : List ℤ) (hw : ∀ z ∈ w, z ≠ 0 ∧ z.natAbs ≤ 10) {q : ℕ} (hq : q < 31671) :
    evalWord imgT imgTv w q = idx 31671 (wordG imgG w) q := by
  induction w with
  | nil => simp [evalWord, wordG, idx_one]
  | cons z w ih =>
    have hw' : ∀ z' ∈ w, z' ≠ 0 ∧ z'.natAbs ≤ 10 := fun z' h => hw z' (List.mem_cons_of_mem _ h)
    have h1 : evalWord imgT imgTv (z :: w) q =
        ap (imgLetter imgT imgTv z) (evalWord imgT imgTv w q) :=
      rfl
    have h2 : wordG imgG (z :: w) = imgG z * wordG imgG w := by simp [wordG]
    rw [h1, h2, idx_mul, ih hw']
    exact rep_imgLetter (hw z List.mem_cons_self).2 _ (idx_lt _ hq)

@[expose] noncomputable def gensL :
    Set J := {x | ∃ k ∈ gIdx, x = img k}

@[expose] noncomputable def spL :
    Subgroup J := Subgroup.closure gensL

theorem img_mem_spL
    {k : ℕ} (hk : k ∈ gIdx) : img k ∈ spL := Subgroup.subset_closure ⟨k, hk, rfl⟩

theorem toNat_mem_gIdx {z : ℤ} (hz : letterOK z = true) : (z - 1).toNat ∈ gIdx := by
  simp only [letterOK, Bool.and_eq_true, decide_eq_true_eq, bne_iff_ne, ne_eq] at hz
  simp only [gIdx, List.mem_cons, List.not_mem_nil, or_false]
  omega

theorem imgG_mem_spL
    {z : ℤ} (hz : sLetterOK z = true) : imgG z ∈ spL := by
  simp only [sLetterOK, Bool.or_eq_true] at hz
  unfold imgG
  rcases hz with h | h
  · have h1 : 0 < z := by simp only [letterOK, Bool.and_eq_true, decide_eq_true_eq] at h; omega
    rw [ite_eq_left h1]
    exact img_mem_spL (toNat_mem_gIdx h)
  · have h1 : ¬ 0 < z := by simp only [letterOK, Bool.and_eq_true, decide_eq_true_eq] at h; omega
    rw [ite_eq_right h1]
    have := toNat_mem_gIdx h
    exact Subgroup.inv_mem _ (img_mem_spL this)

theorem wordG_mem_spL
    {w : List ℤ} (hw : ∀ z ∈ w, sLetterOK z = true) : wordG imgG w ∈ spL := by
  induction w with
  | nil => exact Subgroup.one_mem _
  | cons z w ih =>
    have h2 : wordG imgG (z :: w) = imgG z * wordG imgG w := by simp [wordG]
    rw [h2]
    exact Subgroup.mul_mem _ (imgG_mem_spL (hw z List.mem_cons_self))
      (ih fun z' h => hw z' (List.mem_cons_of_mem _ h))

theorem letterOK_of_sLetterOK_pos {z : ℤ} (h : letterOK z = true) : sLetterOK z = true := by
  simp [sLetterOK, h]

theorem ne_zero_natAbs_of_letterOK {z : ℤ} (h : letterOK z = true) : z ≠ 0 ∧ z.natAbs ≤ 10 := by
  simp only [letterOK, Bool.and_eq_true, decide_eq_true_eq] at h
  omega

theorem ne_zero_natAbs_of_sLetterOK {z : ℤ} (h : sLetterOK z = true) : z ≠ 0 ∧ z.natAbs ≤ 10 := by
  simp only [sLetterOK, Bool.or_eq_true, letterOK, Bool.and_eq_true, decide_eq_true_eq] at h
  omega

theorem imgConj_parts
    {k : ℕ} (hk : k < 10) :
    imgWords[k]! = prefWord k ++ dPow ++ invWord (prefWord k) ∧
      ∀ z ∈ prefWord k, z = 1 ∨ z = -1 ∨ z = 2 ∨ z = -2 := by
  have h := sp8_parts.1
  unfold imgConjOK at h
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range,
    Bool.or_eq_true] at h
  obtain ⟨-, h2⟩ := h
  obtain ⟨h3, h4⟩ := h2 k hk
  exact ⟨h3, fun z hz => by simpa [or_assoc] using h4 z hz⟩

theorem genG_neg
    {z : ℤ} (hz : z = 1 ∨ z = -1 ∨ z = 2 ∨ z = -2) : genG (-z) = (genG z)⁻¹ := by
  rcases hz with rfl | rfl | rfl | rfl <;> simp [genG]

theorem wordG_invWord_gen
    {u : List ℤ} (hu : ∀ z ∈ u, z = 1 ∨ z = -1 ∨ z = 2 ∨ z = -2) :
    wordG genG (invWord u) = (wordG genG u)⁻¹ := by
  unfold wordG invWord
  have h1 : List.map genG (List.map (fun z => -z) u.reverse) =
      ((List.map genG u).map fun x => x⁻¹).reverse := by
    rw [List.map_map, List.map_map, ← List.map_reverse]
    apply List.map_congr_left
    intro z hz
    have hz' := hu z (List.mem_reverse.1 hz)
    simp [Function.comp, genG_neg hz']
  rw [h1, ← List.prod_inv_reverse]

theorem wordG_dPow : wordG genG dPow = d := by
  have h : wordG genG dPow = (wordG genG dLetters) ^ 7 := by
    simp only [wordG, dPow, List.map_flatten, List.prod_flatten, List.map_replicate,
      List.prod_replicate]
  have h2 : wordG genG dLetters = wordJ dWord := by
    unfold wordG dLetters wordJ
    rw [List.map_map]
    exact congrArg List.prod
      (List.map_congr_left fun x _ => by by_cases hx : x = 0 <;> simp [hx, genG])
  rw [h, h2]
  rfl

theorem piPt_eq
    (k : ℕ) : piPt sp8G4 k = idx 31671 (wordG genG (prefWord k)) 0 := by
  have h := Rep.wordT (n := 31671) (G := J) (by norm_num) (prefWord k) (fun l _ => rep_gen l)
  have h0 := h 0 (by norm_num)
  unfold piPt
  rw [seedLetter_eq]
  exact h0

theorem piPt_lt (k : ℕ) : piPt sp8G4 k < 31671 := by
  rw [piPt_eq]
  exact idx_lt _ (by norm_num)

theorem img_eq_conjPt
    {k : ℕ} (hk : k < 10) : img k = conjPt (piPt sp8G4 k) := by
  obtain ⟨hw, hu⟩ := imgConj_parts hk
  have hconj := conjPt_smul (wordG genG (prefWord k)) (0 : Fin 31671)
  rw [piPt_eq]
  have e : idx 31671 (wordG genG (prefWord k)) 0 =
      ((wordG genG (prefWord k) • (0 : Fin 31671) : Fin 31671) : ℕ) := idx_of_lt _ (by norm_num)
  rw [e, hconj]
  unfold img
  rw [hw, wordG_append, wordG_append, wordG_dPow, wordG_invWord_gen hu,
    show ((0 : Fin 31671) : ℕ) = 0 from rfl, conjPt_zero]

noncomputable def Lb (p : ℕ) : ℕ := sp8F.lab[p]!

noncomputable def rootP (c : ℕ) : ℕ := sp8F.roots[c]!

theorem roots_parts :
    rootP 0 = piPt sp8G4 0 ∧ rootP 1 = piPt sp8G4 8 ∧ rootP 2 = 0 := by
  have h := rootCheck_parts.1
  unfold rootP
  rw [h]
  exact ⟨rfl, rfl, rfl⟩

theorem rootP_lt
    {c : ℕ} (hc : c < 3) : rootP c < 31671 := by
  obtain ⟨h0, h1, h2⟩ := roots_parts
  interval_cases c
  · rw [h0]; exact piPt_lt 0
  · rw [h1]; exact piPt_lt 8
  · rw [h2]; norm_num

theorem lab_root
    {c : ℕ} (hc : c < 3) : Lb (rootP c) = c := rootCheck_parts.2.2.2.2 c hc

theorem labCheck_parts :
    (∀ p < 31671, Lb p < 3 ∧ ∀ k ∈ gIdx, Lb (ap imgT[k]! p) = Lb p) ∧
      ∀ k ∈ gIdx, Lb (piPt sp8G4 k) = 0 := by
  have h := sp8_parts.2.2.1
  unfold labCheck at h
  simp only [Bool.and_eq_true, allIn_eq_true, List.all_eq_true, beq_iff_eq,
    decide_eq_true_eq] at h
  obtain ⟨h1, h2⟩ := h
  exact ⟨fun p hp => h1 p (Nat.zero_le _) hp, h2⟩

theorem pathCheck_parts : ∀ p < 31671,
    evalWord imgT imgTv (pathW sp8F p) (rootP (Lb p)) = p ∧
      ∀ z ∈ pathW sp8F p, letterOK z = true := by
  have h := sp8_parts.2.2.2.1
  unfold pathCheck at h
  simp only [allIn_eq_true, Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at h
  intro p hp
  exact h p (Nat.zero_le _) hp

theorem lab_lt
    {p : ℕ} (hp : p < 31671) : Lb p < 3 := (labCheck_parts.1 p hp).1

theorem gIdx_lt {k : ℕ} (hk : k ∈ gIdx) : k < 10 := by
  simp only [gIdx, List.mem_cons, List.not_mem_nil, or_false] at hk
  omega

theorem lab_img
    {k : ℕ} (hk : k ∈ gIdx) {p : ℕ} (hp : p < 31671) :
    Lb (idx 31671 (img k) p) = Lb p := by
  rw [← rep_img (gIdx_lt hk) p hp]
  exact (labCheck_parts.1 p hp).2 k hk

theorem lab_spL
    {g : J} (hg : g ∈ spL) {p : ℕ} (hp : p < 31671) : Lb (idx 31671 g p) = Lb p := by
  induction hg using Subgroup.closure_induction generalizing p with
  | mem x hx =>
    obtain ⟨k, hk, rfl⟩ := hx
    exact lab_img hk hp
  | one => rw [idx_one]
  | mul x y _ _ hx hy => rw [idx_mul, hx (idx_lt y hp), hy hp]
  | inv x _ hx =>
    have := hx (idx_lt x⁻¹ hp)
    rw [idx_idx_inv] at this
    exact this.symm

theorem exists_word
    {p : ℕ} (hp : p < 31671) :
    ∃ l ∈ spL, idx 31671 l (rootP (Lb p)) = p := by
  obtain ⟨h1, h2⟩ := pathCheck_parts p hp
  have hl : ∀ z ∈ pathW sp8F p, z ≠ 0 ∧ z.natAbs ≤ 10 := fun z hz =>
    ne_zero_natAbs_of_letterOK (h2 z hz)
  refine ⟨wordG imgG (pathW sp8F p),
    wordG_mem_spL fun z hz => letterOK_of_sLetterOK_pos (h2 z hz), ?_⟩
  rw [← evalWord_eq _ hl (rootP_lt (lab_lt hp))]
  exact h1

abbrev Pt : Type := Fin 31671

theorem smul_val
    (g : J) (p : Pt) : ((g • p : Pt) : ℕ) = idx 31671 g p.val :=
  (idx_of_lt g p.isLt).symm

@[expose] noncomputable def tr (p : Pt) : J := conjPt p.val

theorem tr_smul
    (g : J) (p : Pt) : tr (g • p) = g * tr p * g⁻¹ := conjPt_smul g p

theorem tr_injective : Function.Injective tr := fun p q h =>
  Fin.ext (conjPt_inj (by rw [orb_size]; exact p.isLt) (by rw [orb_size]; exact q.isLt) h)

theorem smul_eq_iff_tr
    (g : J) (p q : Pt) : g • p = q ↔ g * tr p * g⁻¹ = tr q := smul_eq_iff g p q

theorem commute_iff_smul
    (p q : Pt) : Commute (tr p) (tr q) ↔ tr p • q = q := by
  rw [smul_eq_iff_tr, mul_inv_eq_iff_eq_mul]
  rfl

@[expose] noncomputable def piF
    (k : ℕ) : Pt := ⟨piPt sp8G4 k, piPt_lt k⟩

theorem img_eq_tr
    {k : ℕ} (hk : k < 10) : img k = tr (piF k) := img_eq_conjPt hk

@[expose] noncomputable def LbF
    (p : Pt) : Fin 3 := ⟨Lb p.val, lab_lt p.isLt⟩

@[expose] noncomputable def rootF
    (c : Fin 3) : Pt := ⟨rootP c.val, rootP_lt c.isLt⟩

theorem LbF_smul
    {l : J} (hl : l ∈ spL) (p : Pt) : LbF (l • p) = LbF p :=
  Fin.ext (by
    show Lb ((l • p : Pt) : ℕ) = Lb p.val
    rw [smul_val]
    exact lab_spL hl p.isLt)

theorem exists_word_F
    (p : Pt) : ∃ l ∈ spL, l • rootF (LbF p) = p := by
  obtain ⟨l, hl, h⟩ := exists_word p.isLt
  exact ⟨l, hl, Fin.ext (by rw [smul_val]; exact h)⟩

theorem LbF_rootF
    (c : Fin 3) : LbF (rootF c) = c :=
  Fin.ext (lab_root c.isLt)

theorem exists_smul_iff
    {p q : Pt} : (∃ l ∈ spL, l • p = q) ↔ LbF p = LbF q := by
  constructor
  · rintro ⟨l, hl, rfl⟩
    exact (LbF_smul hl p).symm
  · intro h
    obtain ⟨l₁, hl₁, h₁⟩ := exists_word_F p
    obtain ⟨l₂, hl₂, h₂⟩ := exists_word_F q
    rw [h] at h₁
    refine ⟨l₂ * l₁⁻¹, spL.mul_mem hl₂ (spL.inv_mem hl₁), ?_⟩
    rw [mul_smul, ← h₁, inv_smul_smul, h₂]

theorem countCheck_parts :
    ∀ c < 3, (List.range 31671).countP (fun p => sp8F.lab[p]! == c) = orbitSize c := by
  have h := sp8_parts.2.2.2.2.2.2.2.2
  unfold countCheck at h
  simp only [List.all_eq_true, List.mem_range, beq_iff_eq] at h
  exact h

theorem card_filter_fin (Q : ℕ → Prop) [DecidablePred Q] (n : ℕ) :
    (Finset.univ.filter fun p : Fin n => Q p.val).card =
      (List.range n).countP (fun p => decide (Q p)) := by
  rw [Finset.card_filter, Fin.sum_univ_eq_sum_range (fun i => if Q i then 1 else 0) n]
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih, List.range_succ, List.countP_append]
    simp

theorem card_label (c : Fin 3) :
    (Finset.univ.filter fun p : Pt => LbF p = c).card = orbitSize c.val := by
  have h := countCheck_parts c.val c.isLt
  rw [← h]
  have e : (Finset.univ.filter fun p : Pt => LbF p = c) =
      Finset.univ.filter fun p : Fin 31671 => sp8F.lab[p.val]! = c.val := by
    apply Finset.filter_congr
    intro p _
    exact Fin.ext_iff
  rw [e, card_filter_fin (fun p => sp8F.lab[p]! = c.val) 31671]
  rfl

theorem card_label_values :
    (Finset.univ.filter fun p : Pt => LbF p = 0).card = 255 ∧
      (Finset.univ.filter fun p : Pt => LbF p = 1).card = 13056 ∧
      (Finset.univ.filter fun p : Pt => LbF p = 2).card = 18360 :=
  ⟨card_label 0, card_label 1, card_label 2⟩

theorem rootF_zero :
    rootF 0 = piF 0 := Fin.ext roots_parts.1

theorem rootF_one :
    rootF 1 = piF 8 := Fin.ext roots_parts.2.1

theorem rootF_two_val :
    (rootF 2 : Pt).val = 0 := roots_parts.2.2

theorem LbF_piF
    {k : ℕ} (hk : k ∈ gIdx) : LbF (piF k) = 0 :=
  Fin.ext (labCheck_parts.2 k hk)

@[expose] def Sg :
    Set Pt := {p | LbF p = 0}

theorem smul_mem_Sg
    {l : J} (hl : l ∈ spL) {p : Pt} (hp : p ∈ Sg) : l • p ∈ Sg := by
  show LbF (l • p) = 0
  rw [LbF_smul hl]
  exact hp

theorem piF_mem_Sg
    {k : ℕ} (hk : k ∈ gIdx) : piF k ∈ Sg := LbF_piF hk

theorem tr_mem_spL
    {p : Pt} (hp : p ∈ Sg) : tr p ∈ spL := by
  obtain ⟨l, hl, h⟩ := exists_word_F p
  have h0 : LbF p = 0 := hp
  rw [h0, rootF_zero] at h
  rw [← h, tr_smul, ← img_eq_tr (by norm_num : 0 < 10)]
  exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hl (img_mem_spL (by simp [gIdx])))
    (Subgroup.inv_mem _ hl)

theorem smul_tr_mem_Sg
    {p q : Pt} (hp : p ∈ Sg) (hq : q ∈ Sg) : tr p • q ∈ Sg :=
  smul_mem_Sg (tr_mem_spL hp) hq

theorem mem_sigList
    {p : ℕ} : p ∈ sigList sp8F ↔ p < 31671 ∧ sp8F.lab[p]! = 0 := by
  unfold sigList
  simp [List.mem_filter, List.mem_range]

theorem mem_Sg
    {p : Pt} : p ∈ Sg ↔ sp8F.lab[p.val]! = 0 :=
  ⟨fun h => congrArg Fin.val h, fun h => Fin.ext h⟩

theorem vecCheck_parts :
    sp8F.vec.size = 31671 ∧ sp8F.ptOf.size = 256 ∧
      (∀ p, p < 31671 → sp8F.lab[p]! = 0 →
        1 ≤ sp8F.vec[p]! ∧ sp8F.vec[p]! ≤ 255 ∧ sp8F.ptOf[sp8F.vec[p]!]! = p) ∧
      ∀ v, 1 ≤ v → v < 256 →
        sp8F.ptOf[v]! < 31671 ∧ sp8F.lab[sp8F.ptOf[v]!]! = 0 ∧ sp8F.vec[sp8F.ptOf[v]!]! = v := by
  have h := sp8_parts.2.2.2.2.1
  unfold vecCheck at h
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, mem_sigList, allIn_eq_true,
    decide_eq_true_eq] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  exact ⟨h1, h2, fun p hp hl => by
    obtain ⟨⟨a, b⟩, c⟩ := h3 p ⟨hp, hl⟩
    exact ⟨a, b, c⟩, fun v hv1 hv2 => by
    obtain ⟨⟨a, b⟩, c⟩ := h4 v hv1 hv2
    exact ⟨a, b, c⟩⟩

@[expose] noncomputable def vecN (p : Pt) : ℕ := sp8F.vec[p.val]!

theorem vecN_range
    {p : Pt} (hp : p ∈ Sg) : 1 ≤ vecN p ∧ vecN p ≤ 255 := by
  have := vecCheck_parts.2.2.1 p.val p.isLt (mem_Sg.1 hp)
  exact ⟨this.1, this.2.1⟩

theorem vecN_inj
    {p q : Pt} (hp : p ∈ Sg) (hq : q ∈ Sg) (h : vecN p = vecN q) : p = q := by
  have h1 := (vecCheck_parts.2.2.1 p.val p.isLt (mem_Sg.1 hp)).2.2
  have h2 := (vecCheck_parts.2.2.1 q.val q.isLt (mem_Sg.1 hq)).2.2
  apply Fin.ext
  have : sp8F.vec[p.val]! = sp8F.vec[q.val]! := h
  rw [← h1, ← h2, this]

theorem exists_vecN
    {v : ℕ} (h1 : 1 ≤ v) (h2 : v ≤ 255) : ∃ p ∈ Sg, vecN p = v := by
  obtain ⟨a, b, c⟩ := vecCheck_parts.2.2.2 v h1 (by omega)
  exact ⟨⟨sp8F.ptOf[v]!, a⟩, mem_Sg.2 b, c⟩

theorem invWord_letters {u : List ℤ} (hu : ∀ z ∈ u, z ≠ 0 ∧ z.natAbs ≤ 10) :
    ∀ z ∈ invWord u, z ≠ 0 ∧ z.natAbs ≤ 10 := by
  intro z hz
  simp only [invWord, List.mem_map, List.mem_reverse] at hz
  obtain ⟨z', hz', rfl⟩ := hz
  have := hu z' hz'
  exact ⟨by omega, by simpa using this.2⟩

theorem conjAct_eq
    {p : Pt} (hp : p ∈ Sg) {q : ℕ} (hq : q < 31671) :
    conjAct imgT imgTv (pathW sp8F p.val) q = idx 31671 (tr p) q := by
  obtain ⟨h1, h2⟩ := pathCheck_parts p.val p.isLt
  have hl0 : Lb p.val = 0 := mem_Sg.1 hp
  rw [hl0, roots_parts.1] at h1
  set u := pathW sp8F p.val with hu_def
  have hu : ∀ z ∈ u, z ≠ 0 ∧ z.natAbs ≤ 10 := fun z hz => ne_zero_natAbs_of_letterOK (h2 z hz)
  have hl : idx 31671 (wordG imgG u) (piPt sp8G4 0) = p.val := by
    rw [← evalWord_eq u hu (piPt_lt 0)]
    exact h1
  have hp' : p = wordG imgG u • piF 0 := Fin.ext (by rw [smul_val]; exact hl.symm)
  have htr : tr p = wordG imgG u * img 0 * (wordG imgG u)⁻¹ := by
    rw [hp', tr_smul, img_eq_tr (by norm_num : 0 < 10)]
  have e1 : evalWord imgT imgTv (invWord u) q = idx 31671 (wordG imgG u)⁻¹ q := by
    rw [evalWord_eq _ (invWord_letters hu) hq, wordG_invWord fun z hz => (hu z hz).1]
  have e2 : ap imgT[0]! (idx 31671 (wordG imgG u)⁻¹ q) =
      idx 31671 (img 0) (idx 31671 (wordG imgG u)⁻¹ q) :=
    rep_img (by norm_num : 0 < 10) _ (idx_lt _ hq)
  unfold conjAct
  rw [e1, e2, evalWord_eq u hu (idx_lt _ (idx_lt _ hq)), htr, idx_mul, idx_mul]

theorem commPt_iff
    {p : Pt} (hp : p ∈ Sg) {q : Pt} :
    commPt imgT imgTv sp8F p.val q.val = true ↔ Commute (tr p) (tr q) := by
  rw [commute_iff_smul]
  unfold commPt
  rw [conjAct_eq hp q.isLt, beq_iff_eq, ← smul_val]
  exact ⟨fun h => Fin.ext h, fun h => congrArg Fin.val h⟩

theorem transCheck_parts
    {p q : ℕ} (hp : p < 31671) (hq : q < 31671) (hlp : sp8F.lab[p]! = 0)
    (hlq : sp8F.lab[q]! = 0) :
    sp8F.vec[conjAct imgT imgTv (pathW sp8F p) q]! =
      (sp8F.vec[q]! ^^^ (if beta sp8F.vec[p]! sp8F.vec[q]! then sp8F.vec[p]! else 0)) := by
  have h := sp8_parts.2.2.2.2.2.1
  unfold transCheck at h
  simp only [List.all_eq_true, beq_iff_eq, mem_sigList] at h
  exact h p ⟨hp, hlp⟩ q ⟨hq, hlq⟩

theorem vecN_trans
    {p q : Pt} (hp : p ∈ Sg) (hq : q ∈ Sg) :
    vecN (tr p • q) = vecN q ^^^ (if beta (vecN p) (vecN q) then vecN p else 0) := by
  have h := transCheck_parts p.isLt q.isLt (mem_Sg.1 hp) (mem_Sg.1 hq)
  rw [conjAct_eq hp q.isLt] at h
  unfold vecN
  rw [smul_val]
  exact h

theorem commute_iff_beta
    {p q : Pt} (hp : p ∈ Sg) (hq : q ∈ Sg) :
    Commute (tr p) (tr q) ↔ beta (vecN p) (vecN q) = false := by
  rw [commute_iff_smul]
  have hmem := smul_tr_mem_Sg hp hq
  have h := vecN_trans hp hq
  have hp1 := (vecN_range hp).1
  constructor
  · intro h0
    rw [h0] at h
    by_contra hb
    have hb' : beta (vecN p) (vecN q) = true := by simpa using hb
    rw [ite_eq_left hb'] at h
    have h' : vecN q ^^^ 0 = vecN q ^^^ vecN p := by rw [Nat.xor_zero]; exact h
    have := (Nat.xor_right_inj.1 h').symm
    omega
  · intro hb
    rw [hb] at h
    simp only [Bool.false_eq_true, ite_false, Nat.xor_zero] at h
    exact vecN_inj hmem hq h

theorem sepCheck_parts
    {c : ℕ} (hc : c < 3) :
    (∀ pr ∈ stabPairs c, (∀ z ∈ stabWord imgT sp8F c pr, sLetterOK z = true) ∧
        evalWord imgT imgTv (stabWord imgT sp8F c pr) (rootP c) = rootP c) ∧
    (∀ y < 31671, (∀ p ∈ sigList sp8F,
        commPt imgT imgTv sp8F p y = commPt imgT imgTv sp8F p (rootP c)) → Lb y = c) ∧
    (∀ y < 31671, Lb y = c →
      (∀ pr ∈ stabPairs c, evalWord imgT imgTv (stabWord imgT sp8F c pr) y = y) → y = rootP c) := by
  have h := sp8_parts.2.2.2.2.2.2.1
  unfold sepCheck at h
  rw [List.all_eq_true] at h
  have hc' := h c (List.mem_range.2 hc)
  rw [Bool.and_eq_true] at hc'
  obtain ⟨hws, hy⟩ := hc'
  rw [allIn_eq_true] at hy
  refine ⟨fun pr hpr => ?_, fun y hy' hpat => ?_, fun y hy' hl hfix => ?_⟩
  · rw [List.all_eq_true] at hws
    have := hws (stabWord imgT sp8F c pr) (List.mem_map.2 ⟨pr, hpr, rfl⟩)
    rw [Bool.and_eq_true, List.all_eq_true, beq_iff_eq] at this
    exact this
  · have h1 := (Bool.and_eq_true _ _ ▸ hy y (Nat.zero_le _) hy' : _ ∧ _).1
    rw [Bool.or_eq_true, Bool.not_eq_true'] at h1
    rcases h1 with h2 | h2
    · exfalso
      have h3 : ((sigList sp8F).all fun p =>
          commPt imgT imgTv sp8F p y == commPt imgT imgTv sp8F p sp8F.roots[c]!) = true :=
        List.all_eq_true.2 fun p hp => beq_iff_eq.2 (hpat p hp)
      rw [h3] at h2
      exact Bool.noConfusion h2
    · exact beq_iff_eq.1 h2
  · have h1 := (Bool.and_eq_true _ _ ▸ hy y (Nat.zero_le _) hy' : _ ∧ _).2
    rw [Bool.or_eq_true, Bool.not_eq_true'] at h1
    rcases h1 with h2 | h2
    · exfalso
      have h3 : (sp8F.lab[y]! == c &&
          (List.map (stabWord imgT sp8F c) (stabPairs c)).all fun w =>
            evalWord imgT imgTv w y == y) = true := by
        rw [Bool.and_eq_true, beq_iff_eq, List.all_eq_true]
        refine ⟨hl, fun w hw => ?_⟩
        obtain ⟨pr, hpr, rfl⟩ := List.mem_map.1 hw
        exact beq_iff_eq.2 (hfix pr hpr)
      rw [h3] at h2
      exact Bool.noConfusion h2
    · exact beq_iff_eq.1 h2

theorem commute_conj_iff
    (g a b : J) : Commute (g * a * g⁻¹) (g * b * g⁻¹) ↔ Commute a b := by
  unfold Commute SemiconjBy
  constructor
  · intro h
    have : g * (a * b) * g⁻¹ = g * (b * a) * g⁻¹ := by
      simpa [mul_assoc] using h
    simpa using this
  · intro h
    have : g * (a * b) * g⁻¹ = g * (b * a) * g⁻¹ := by rw [h]
    simpa [mul_assoc] using this

theorem centralizer_trivial
    {g : J} (hg : ∀ k ∈ gIdx, g * img k = img k * g) : g = 1 := by
  have hcomm : ∀ l ∈ spL, g * l = l * g := by
    intro l hl
    induction hl using Subgroup.closure_induction with
    | mem x hx =>
      obtain ⟨k, hk, rfl⟩ := hx
      exact hg k hk
    | one => rw [mul_one, one_mul]
    | mul x y _ _ hx hy => rw [← mul_assoc, hx, mul_assoc, hy, mul_assoc]
    | inv x _ hx =>
      have h1 : x⁻¹ * (g * x) * x⁻¹ = x⁻¹ * (x * g) * x⁻¹ := by rw [hx]
      simp only [mul_assoc, mul_inv_cancel, mul_one, inv_mul_cancel_left] at h1
      exact h1.symm
  have h0 : g • piF 0 = piF 0 := by
    rw [smul_eq_iff_tr, ← img_eq_tr (by norm_num : 0 < 10), mul_inv_eq_iff_eq_mul]
    exact hg 0 (by simp [gIdx])
  have hfixSg : ∀ p ∈ Sg, g • p = p := by
    intro p hp
    obtain ⟨l, hl, h⟩ := exists_word_F p
    have hp0 : LbF p = 0 := hp
    rw [hp0, rootF_zero] at h
    rw [← h, smul_smul, hcomm l hl, ← smul_smul, h0]
  have hpat : ∀ q : Pt, ∀ p ∈ sigList sp8F, commPt imgT imgTv sp8F p (g • q).val =
      commPt imgT imgTv sp8F p q.val := by
    intro q p hp
    obtain ⟨hpn, hpl⟩ := mem_sigList.1 hp
    have hpS : (⟨p, hpn⟩ : Pt) ∈ Sg := mem_Sg.2 hpl
    have hgp : g * tr ⟨p, hpn⟩ * g⁻¹ = tr ⟨p, hpn⟩ := by
      rw [← smul_eq_iff_tr]
      exact hfixSg _ hpS
    rw [Bool.eq_iff_iff, commPt_iff hpS, commPt_iff hpS, tr_smul]
    conv_lhs => rw [← hgp]
    exact commute_conj_iff g _ _
  have hroot : ∀ c : Fin 3, g • rootF c = rootF c := by
    intro c
    have hc := c.isLt
    obtain ⟨hs1, hs2, hs3⟩ := sepCheck_parts hc
    have hlab : Lb (g • rootF c).val = c.val := hs2 _ (g • rootF c).isLt (fun p hp => by
      have := hpat (rootF c) p hp
      exact this)
    refine Fin.ext (hs3 _ (g • rootF c).isLt hlab fun pr hpr => ?_)
    obtain ⟨hl, hev⟩ := hs1 pr hpr
    set w := stabWord imgT sp8F c.val pr with hw
    have hw' : ∀ z ∈ w, z ≠ 0 ∧ z.natAbs ≤ 10 := fun z hz => ne_zero_natAbs_of_sLetterOK (hl z hz)
    have hsmem : wordG imgG w ∈ spL := wordG_mem_spL hl
    have hsroot : wordG imgG w • rootF c = rootF c :=
      Fin.ext (by
        show ((wordG imgG w • rootF c : Pt) : ℕ) = rootP c.val
        rw [smul_val]
        show idx 31671 (wordG imgG w) (rootP c.val) = rootP c.val
        rw [← evalWord_eq w hw' (rootP_lt hc)]
        exact hev)
    have hsy : wordG imgG w • (g • rootF c) = g • rootF c := by
      rw [smul_smul, (hcomm _ hsmem).symm, ← smul_smul, hsroot]
    rw [evalWord_eq w hw' (g • rootF c).isLt, ← smul_val, hsy]
  have hall : ∀ q : Pt, g • q = q := by
    intro q
    obtain ⟨l, hl, h⟩ := exists_word_F q
    rw [← h, smul_smul, hcomm l hl, ← smul_smul, hroot]
  exact eq_one_of_fix_all hall

theorem tr_rootF_two :
    tr (rootF 2) = d := by
  show conjPt (rootF 2).val = d
  rw [rootF_two_val, conjPt_zero]

theorem rep_dTable : Rep 31671 (dTable orb) d :=
  Rep.powT (by norm_num) (rep_dWordTab dWord) 7

theorem gen_witness :
    ∃ q : Pt, LbF q = 2 ∧ LbF (d • q) = 1 := by
  have h := sp8_parts.2.2.2.2.2.2.2.1
  unfold genCheck at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨h0, h2⟩, h3⟩ := h
  have hd : ap (dTable orb) 2 = idx 31671 d 2 := rep_dTable 2 (by norm_num)
  rw [hd] at h3
  refine ⟨⟨2, by norm_num⟩, Fin.ext h2, Fin.ext ?_⟩
  show sp8F.lab[((d • (⟨2, by norm_num⟩ : Pt) : Pt) : ℕ)]! = 1
  rw [smul_val]
  exact h3

@[expose] noncomputable def allImgs :
    Set J := {x | ∃ k < 10, x = img k}

theorem imgG_mem_closure {z : ℤ} (hz : z ≠ 0 ∧ z.natAbs ≤ 10) :
    imgG z ∈ Subgroup.closure allImgs := by
  unfold imgG
  split_ifs with h
  · exact Subgroup.subset_closure ⟨(z - 1).toNat, by omega, rfl⟩
  · exact Subgroup.inv_mem _ (Subgroup.subset_closure ⟨(-z - 1).toNat, by omega, rfl⟩)

theorem wordG_mem_closure
    {w : List ℤ} (hw : ∀ z ∈ w, z ≠ 0 ∧ z.natAbs ≤ 10) :
    wordG imgG w ∈ Subgroup.closure allImgs := by
  induction w with
  | nil => exact Subgroup.one_mem _
  | cons z w ih =>
    have h2 : wordG imgG (z :: w) = imgG z * wordG imgG w := by simp [wordG]
    rw [h2]
    exact Subgroup.mul_mem _ (imgG_mem_closure (hw z List.mem_cons_self))
      (ih fun z' h => hw z' (List.mem_cons_of_mem _ h))

theorem closure_img_eq_top :
    Subgroup.closure allImgs = ⊤ := by
  have ha : a ∈ Subgroup.closure allImgs := by
    rw [← surjA_eq]
    exact wordG_mem_closure fun z hz => letters_ok _ (surjWords_mem (by decide)) z hz
  have hb : b ∈ Subgroup.closure allImgs := by
    rw [← surjB_eq]
    exact wordG_mem_closure fun z hz => letters_ok _ (surjWords_mem (by decide)) z hz
  rw [eq_top_iff, ← closure_ab, Subgroup.closure_le]
  rintro x (rfl | rfl)
  · exact ha
  · exact hb

theorem gen_all
    {C : Subgroup J} (hC : spL ≤ C) {x : Pt} (hx : LbF x ≠ 0) (hxC : tr x ∈ C) :
    C = ⊤ := by
  have key : ∀ y : Pt, LbF y = 1 → tr y ∈ C → img 8 ∈ C := by
    intro y hy hyC
    obtain ⟨l, hl, h⟩ := exists_word_F y
    rw [hy, rootF_one] at h
    have : img 8 = l⁻¹ * tr y * l := by
      rw [← h, tr_smul, ← img_eq_tr (by norm_num : 8 < 10)]
      group
    rw [this]
    exact C.mul_mem (C.mul_mem (C.inv_mem (hC hl)) hyC) (hC hl)
  have h8 : img 8 ∈ C := by
    have hcases : LbF x = 1 ∨ LbF x = 2 := by
      revert hx
      generalize LbF x = c
      revert c
      decide
    rcases hcases with h1 | h2
    · exact key x h1 hxC
    · obtain ⟨l, hl, h⟩ := exists_word_F x
      rw [h2] at h
      have hdC : d ∈ C := by
        have : d = l⁻¹ * tr x * l := by
          rw [← h, tr_smul, tr_rootF_two]
          group
        rw [this]
        exact C.mul_mem (C.mul_mem (C.inv_mem (hC hl)) hxC) (hC hl)
      obtain ⟨q, hq2, hq1⟩ := gen_witness
      obtain ⟨l', hl', h'⟩ := exists_word_F q
      rw [hq2] at h'
      have htrq : tr q ∈ C := by
        rw [← h', tr_smul, tr_rootF_two]
        exact C.mul_mem (C.mul_mem (hC hl') hdC) (C.inv_mem (hC hl'))
      have hdq : tr (d • q) ∈ C := by
        rw [tr_smul]
        exact C.mul_mem (C.mul_mem hdC htrq) (C.inv_mem hdC)
      exact key _ hq1 hdq
  rw [eq_top_iff, ← closure_img_eq_top, Subgroup.closure_le]
  rintro _ ⟨k, hk, rfl⟩
  by_cases h8k : k = 8
  · subst h8k
    exact h8
  · refine hC (img_mem_spL ?_)
    simp only [gIdx, List.mem_cons, List.not_mem_nil, or_false]
    omega

end CFSG.Monster.Existence.Fi23Sp8

module

public import CFSG.Monster.B.Classical.E6FoldedCode

public noncomputable section

namespace CFSG.Monster.B.Classical.E6Folded

theorem jElt_inj {i m : ℕ} (hi : i < 48) (hm : m < 48) (h : jElt i = jElt m) : i = m := by
  have h' := congrArg code h
  rw [code_jElt hi, code_jElt hm, List.getD_eq_getElem _ _ (by rw [jCodes_length]; exact hi),
    List.getD_eq_getElem _ _ (by rw [jCodes_length]; exact hm)] at h'
  exact jCodes_nodup.getElem_inj_iff.1 h'

theorem elt_inj {a b i m : ℕ} (ha : a < 24) (hb : b < 24) (hi : i < 48) (hm : m < 48)
    (h : tElt a * jElt i = tElt b * jElt m) : a = b ∧ i = m := by
  obtain ⟨h₁, h₂⟩ := tElt_mul_inj ha hb (jElt_mem hi) (jElt_mem hm) h
  exact ⟨h₁, jElt_inj hi hm h₂⟩

theorem mem_W_iff_elt (w : Equiv.Perm Λ) : w ∈ W ↔ ∃ a < 24, ∃ i < 48, w = tElt a * jElt i := by
  rw [mem_W_iff]
  constructor
  · rintro ⟨a, ha, v, hv, rfl⟩
    obtain ⟨i, hi, rfl⟩ := (mem_WJ_iff v).1 hv
    exact ⟨a, ha, i, hi, rfl⟩
  · rintro ⟨a, ha, i, hi, rfl⟩
    exact ⟨a, ha, jElt i, jElt_mem hi, rfl⟩

theorem elt_mem_W (a i : ℕ) : tElt a * jElt i ∈ W :=
  Subgroup.mul_mem _ (tElt_mem_W a) (wordProd_mem_W _)

theorem elt_apply_θΛ {a i : ℕ} (ha : a < 24) (hi : i < 48) :
    (tElt a * jElt i) θΛ = ι ⟨a, ha⟩ :=
  tElt_mul_apply_θΛ ha (jElt_mem hi)

theorem form_θ_ι (a : Fin 24) : form θ (ι a).1 = levList.getD a 0 := levList_eq a a.2

@[expose] def pairLength (a i : ℕ) : ℕ := (tWords.getD a []).length + (jWords.getD i []).length

@[expose] def pairWeight (a i : ℕ) : ℕ :=
  wordWeight (tWords.getD a []) * wordWeight (jWords.getD i [])

open _root_.Classical in
@[expose] def pairOf (w : Equiv.Perm Λ) : ℕ × ℕ :=
  if h : ∃ p : ℕ × ℕ, p.1 < 24 ∧ p.2 < 48 ∧ w = tElt p.1 * jElt p.2 then h.choose else (0, 0)

theorem pairOf_eq {a i : ℕ} (ha : a < 24) (hi : i < 48) : pairOf (tElt a * jElt i) = (a, i) := by
  have h : ∃ p : ℕ × ℕ, p.1 < 24 ∧ p.2 < 48 ∧ tElt a * jElt i = tElt p.1 * jElt p.2 :=
    ⟨(a, i), ha, hi, rfl⟩
  rw [pairOf, dite_eq_left h]
  obtain ⟨h₁, h₂, h₃⟩ := h.choose_spec
  obtain ⟨e₁, e₂⟩ := elt_inj ha h₁ hi h₂ h₃
  exact Prod.ext e₁.symm e₂.symm

@[expose] def certLength (w : Equiv.Perm Λ) : ℕ := pairLength (pairOf w).1 (pairOf w).2

@[expose] def certWeight (w : Equiv.Perm Λ) : ℕ := pairWeight (pairOf w).1 (pairOf w).2

theorem certLength_eq {a i : ℕ} (ha : a < 24) (hi : i < 48) :
    certLength (tElt a * jElt i) = pairLength a i := by
  rw [certLength, pairOf_eq ha hi]

theorem certWeight_eq {a i : ℕ} (ha : a < 24) (hi : i < 48) :
    certWeight (tElt a * jElt i) = pairWeight a i := by
  rw [certWeight, pairOf_eq ha hi]

theorem one_eq_elt : (1 : Equiv.Perm Λ) = tElt 23 * jElt 0 := by
  rw [tElt_23, jElt_zero, mul_one]

theorem gen_mul_elt (k : Fin 4) {a i : ℕ} (ha : a < 24) (hi : i < 48) :
    ∃ b < 24, ∃ m < 48, gen k * (tElt a * jElt i) = tElt b * jElt m ∧
      pairLength b m ≤ pairLength a i + 1 ∧
      (pairLength b m = pairLength a i + 1 → pairWeight b m = letterWeight k * pairWeight a i) := by
  rcases gen_mul_tElt k ha with ⟨h, hl, hw⟩ | ⟨-, j, hj, h, hjk⟩
  · refine ⟨gidx k a, gidx_lt k ha, i, hi, by rw [← mul_assoc, h], by unfold pairLength; omega,
      fun heq => ?_⟩
    have : (tWords.getD (gidx k a) []).length = (tWords.getD a []).length + 1 := by
      unfold pairLength at heq
      omega
    rw [pairWeight, pairWeight, hw this, mul_assoc]
  · obtain ⟨m, hm, hcode, hl, hw⟩ := jCodes_edge i hi j ((mem_J_iff j).1 hj)
    have hjm : gen j * jElt i = jElt m :=
      code_injective (by rw [code_mul, code_gen, code_jElt hi, hcode, code_jElt hm])
    refine ⟨a, ha, m, hm, by rw [← mul_assoc, h, mul_assoc, hjm], by unfold pairLength; omega,
      fun heq => ?_⟩
    have : (jWords.getD m []).length = (jWords.getD i []).length + 1 := by
      unfold pairLength at heq
      omega
    rw [pairWeight, pairWeight, hw this, ← hjk]
    ring

theorem exists_descent {a i : ℕ} (ha : a < 24) (hi : i < 48) (hne : tElt a * jElt i ≠ 1) :
    ∃ k : Fin 4, ∃ b < 24, ∃ m < 48, gen k * (tElt a * jElt i) = tElt b * jElt m ∧
      pairLength b m + 1 = pairLength a i := by
  by_cases h23 : a = 23
  · subst h23
    rcases jWords_tail i hi with h0 | ⟨m, hm, htail⟩
    · exact absurd (by rw [tElt_23, jElt, h0]; rfl) hne
    · have hne' : jWords.getD i [] ≠ [] := by
        intro h0
        exact hne (by rw [tElt_23, jElt, h0]; rfl)
      obtain ⟨k, l, hkl⟩ := List.exists_cons_of_ne_nil hne'
      rw [hkl, List.tail_cons] at htail
      refine ⟨k, 23, by norm_num, m, hm, ?_, ?_⟩
      · rw [tElt_23, one_mul, one_mul, jElt, hkl, wordProd_cons, ← mul_assoc, gen_mul_self,
          one_mul, htail]
        rfl
      · rw [pairLength, pairLength, tWords_theta, hkl, List.length_cons, htail]
        rfl
  · obtain ⟨hne', b, hb, htail⟩ := tWords_tail a ha h23
    obtain ⟨k, l, hkl⟩ := List.exists_cons_of_ne_nil hne'
    rw [hkl, List.tail_cons] at htail
    refine ⟨k, b, hb, i, hi, ?_, ?_⟩
    · rw [tElt, hkl, wordProd_cons, ← mul_assoc, ← mul_assoc, gen_mul_self, one_mul, htail]
      rfl
    · rw [pairLength, pairLength, hkl, List.length_cons, htail]
      omega

theorem length_certificate :
    (∀ w ∈ W, wordLength w = certLength w) ∧
      (∀ w l, IsReducedWord w l → wordWeight l = certWeight w) := by
  apply wordLength_eq_and_weight_eq
  · rw [one_eq_elt, certLength_eq (by norm_num) (by norm_num), pairLength, tWords_theta,
      jWords_zero]
    rfl
  · rw [one_eq_elt, certWeight_eq (by norm_num) (by norm_num), pairWeight, tWords_theta,
      jWords_zero]
    rfl
  · intro w hw k
    obtain ⟨a, ha, i, hi, rfl⟩ := (mem_W_iff_elt w).1 hw
    obtain ⟨b, hb, m, hm, h, hl, -⟩ := gen_mul_elt k ha hi
    rw [h, certLength_eq hb hm, certLength_eq ha hi]
    exact hl
  · intro w hw k hk
    obtain ⟨a, ha, i, hi, rfl⟩ := (mem_W_iff_elt w).1 hw
    obtain ⟨b, hb, m, hm, h, -, hq⟩ := gen_mul_elt k ha hi
    rw [h, certLength_eq hb hm, certLength_eq ha hi] at hk
    rw [h, certWeight_eq hb hm, certWeight_eq ha hi]
    exact hq hk
  · intro w hw hne
    obtain ⟨a, ha, i, hi, rfl⟩ := (mem_W_iff_elt w).1 hw
    obtain ⟨k, b, hb, m, hm, h, hl⟩ := exists_descent ha hi hne
    exact ⟨k, by rw [h, certLength_eq hb hm, certLength_eq ha hi]; exact hl⟩

theorem wordProd_append (l l' : List (Fin 4)) : wordProd (l ++ l') = wordProd l * wordProd l' := by
  simp [wordProd]

theorem exists_isReducedWord {w : Equiv.Perm Λ} (hw : w ∈ W) : ∃ l, IsReducedWord w l := by
  obtain ⟨a, -, i, -, rfl⟩ := (mem_W_iff_elt w).1 hw
  have hne : {n | ∃ l : List (Fin 4), wordProd l = tElt a * jElt i ∧ l.length = n}.Nonempty :=
    ⟨_, tWords.getD a [] ++ jWords.getD i [], wordProd_append _ _, rfl⟩
  obtain ⟨l, hl, hlen⟩ := Nat.sInf_mem hne
  exact ⟨l, (⟨hl, hlen⟩ : wordProd l = _ ∧ l.length = wordLength _)⟩

theorem wordWeight_eq_of_isReducedWord {w : Equiv.Perm Λ} {l l' : List (Fin 4)}
    (hl : IsReducedWord w l) (hl' : IsReducedWord w l') : wordWeight l = wordWeight l' := by
  rw [length_certificate.2 w l hl, length_certificate.2 w l' hl']

theorem qWeight_eq_of_isReducedWord {w : Equiv.Perm Λ} {l : List (Fin 4)}
    (hl : IsReducedWord w l) : qWeight w = wordWeight l := by
  have h : ∃ l, IsReducedWord w l := ⟨l, hl⟩
  rw [qWeight, dite_eq_left h]
  exact wordWeight_eq_of_isReducedWord h.choose_spec hl

theorem qWeight_elt {a i : ℕ} (ha : a < 24) (hi : i < 48) :
    qWeight (tElt a * jElt i) = pairWeight a i := by
  obtain ⟨l, hl⟩ := exists_isReducedWord (elt_mem_W a i)
  rw [qWeight_eq_of_isReducedWord hl, length_certificate.2 _ l hl, certWeight_eq ha hi]

theorem WJ_eq_image : (WJ : Set (Equiv.Perm Λ)) = jElt '' ↑(Finset.range 48) := by
  ext w
  simp only [SetLike.mem_coe, mem_WJ_iff, Set.mem_image, Finset.coe_range, Set.mem_Iio]
  constructor
  · rintro ⟨i, hi, rfl⟩
    exact ⟨i, hi, rfl⟩
  · rintro ⟨i, hi, rfl⟩
    exact ⟨i, hi, rfl⟩

theorem sum_range_jWords : ∑ i ∈ Finset.range 48, wordWeight (jWords.getD i []) = 93555 := by
  decide +kernel

theorem finsum_qWeight_WJ : ∑ᶠ w ∈ (WJ : Set (Equiv.Perm Λ)), qWeight w = 93555 := by
  have hinj : Set.InjOn jElt ↑(Finset.range 48) := fun i hi m hm h =>
    jElt_inj (by simpa using hi) (by simpa using hm) h
  rw [WJ_eq_image, finsum_mem_image hinj, finsum_mem_coe_finset, ← sum_range_jWords]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hi' : i < 48 := by simpa using hi
  have := qWeight_elt (a := 23) (by norm_num) hi'
  rw [tElt_23, one_mul] at this
  rw [this, pairWeight, tWords_theta]
  simp

@[expose] def levelPairs (d : ℤ) : Finset (ℕ × ℕ) :=
  (Finset.range 24 ×ˢ Finset.range 48).filter fun p => levList.getD p.1 0 = d

theorem level_set_eq_image (d : ℤ) :
    {w : Equiv.Perm Λ | w ∈ W ∧ form θ (w θΛ).1 = d} =
      (fun p : ℕ × ℕ => tElt p.1 * jElt p.2) '' ↑(levelPairs d) := by
  ext w
  simp only [Set.mem_ofPred_eq, Set.mem_image, Finset.mem_coe, levelPairs, Finset.mem_filter,
    Finset.mem_product, Finset.mem_range]
  constructor
  · rintro ⟨hw, hd⟩
    obtain ⟨a, ha, i, hi, rfl⟩ := (mem_W_iff_elt w).1 hw
    rw [elt_apply_θΛ ha hi, form_θ_ι] at hd
    exact ⟨(a, i), ⟨⟨ha, hi⟩, hd⟩, rfl⟩
  · rintro ⟨⟨a, i⟩, ⟨⟨ha, hi⟩, hd⟩, rfl⟩
    refine ⟨elt_mem_W a i, ?_⟩
    rw [elt_apply_θΛ ha hi, form_θ_ι]
    exact hd

theorem finsum_level (d : ℤ) :
    ∑ᶠ w ∈ {w : Equiv.Perm Λ | w ∈ W ∧ form θ (w θΛ).1 = d}, qWeight w =
      ∑ p ∈ levelPairs d, pairWeight p.1 p.2 := by
  have hmem : ∀ p ∈ levelPairs d, p.1 < 24 ∧ p.2 < 48 := fun p hp => by
    simp only [levelPairs, Finset.mem_filter, Finset.mem_product, Finset.mem_range] at hp
    exact hp.1
  have hinj : Set.InjOn (fun p : ℕ × ℕ => tElt p.1 * jElt p.2) ↑(levelPairs d) :=
    fun p hp q hq h => by
      obtain ⟨hp₁, hp₂⟩ := hmem p hp
      obtain ⟨hq₁, hq₂⟩ := hmem q hq
      obtain ⟨e₁, e₂⟩ := elt_inj hp₁ hq₁ hp₂ hq₂ h
      exact Prod.ext e₁ e₂
  rw [level_set_eq_image, finsum_mem_image hinj, finsum_mem_coe_finset]
  refine Finset.sum_congr rfl fun p hp => ?_
  obtain ⟨h₁, h₂⟩ := hmem p hp
  exact qWeight_elt h₁ h₂

theorem sum_levelPairs_two : ∑ p ∈ levelPairs 2, pairWeight p.1 p.2 = 93555 * 1 := by
  decide +kernel

theorem sum_levelPairs_one : ∑ p ∈ levelPairs 1, pairWeight p.1 p.2 = 93555 * 1782 := by
  decide +kernel

theorem sum_levelPairs_zero : ∑ p ∈ levelPairs 0, pairWeight p.1 p.2 = 93555 * 44352 := by
  decide +kernel

theorem sum_levelPairs_neg_one :
    ∑ p ∈ levelPairs (-1), pairWeight p.1 p.2 = 93555 * 1824768 := by
  decide +kernel

theorem sum_levelPairs_neg_two :
    ∑ p ∈ levelPairs (-2), pairWeight p.1 p.2 = 93555 * 2097152 := by
  decide +kernel

theorem orbit_WJ (α : Λ) : MulAction.orbit WJ α = {β | form θ β.1 = form θ α.1} := by
  ext β
  obtain ⟨a, rfl⟩ := ι.surjective α
  obtain ⟨b, rfl⟩ := ι.surjective β
  rw [MulAction.mem_orbit_iff, Set.mem_ofPred_eq, form_θ_ι, form_θ_ι, eq_comm,
    ← jCodes_orbit a a.2 b b.2]
  constructor
  · rintro ⟨⟨v, hv⟩, hvb⟩
    obtain ⟨i, hi, rfl⟩ := (mem_WJ_iff v).1 hv
    rw [Subgroup.smul_def, Equiv.Perm.smul_def, apply_ι_eq_iff, code_jElt hi] at hvb
    exact ⟨i, hi, hvb⟩
  · rintro ⟨i, hi, h⟩
    refine ⟨⟨jElt i, jElt_mem hi⟩, ?_⟩
    rw [Subgroup.smul_def, Equiv.Perm.smul_def, apply_ι_eq_iff, code_jElt hi]
    exact h

theorem range_level : Set.range (fun α : Λ => form θ α.1) = {2, 1, 0, -1, -2} := by
  ext d
  simp only [Set.mem_range, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨α, rfl⟩
    obtain ⟨a, rfl⟩ := ι.surjective α
    rw [form_θ_ι]
    simpa using levList_mem a a.2
  · rintro (rfl | rfl | rfl | rfl | rfl)
    · exact ⟨ι 23, by rw [form_θ_ι]; decide⟩
    · exact ⟨ι 14, by rw [form_θ_ι]; decide⟩
    · exact ⟨ι 5, by rw [form_θ_ι]; decide⟩
    · exact ⟨ι 1, by rw [form_θ_ι]; decide⟩
    · exact ⟨ι 0, by rw [form_θ_ι]; decide⟩

theorem ncard_level (d : ℤ) : {α : Λ | form θ α.1 = d}.ncard =
    (Finset.univ.filter fun a : Fin 24 => levList.getD a 0 = d).card := by
  have h : {α : Λ | form θ α.1 = d} =
      ι '' ↑(Finset.univ.filter fun a : Fin 24 => levList.getD a 0 = d) := by
    ext α
    obtain ⟨a, rfl⟩ := ι.surjective α
    simp only [Set.mem_ofPred_eq, form_θ_ι, Set.mem_image, Finset.coe_filter, Finset.mem_univ,
      true_and, ι.injective.eq_iff, exists_eq_right]
  rw [h, Set.ncard_image_of_injective _ ι.injective, Set.ncard_coe_finset]

theorem card_level :
    (Finset.univ.filter fun a : Fin 24 => levList.getD a 0 = 2).card = 1 ∧
    (Finset.univ.filter fun a : Fin 24 => levList.getD a 0 = 1).card = 8 ∧
    (Finset.univ.filter fun a : Fin 24 => levList.getD a 0 = 0).card = 6 ∧
    (Finset.univ.filter fun a : Fin 24 => levList.getD a 0 = -1).card = 8 ∧
    (Finset.univ.filter fun a : Fin 24 => levList.getD a 0 = -2).card = 1 := by
  decide +kernel

theorem orbitK_eq : orbitK = ι '' {a : Fin 24 | (a : ℕ) ∈ sIdx} := by
  ext α
  obtain ⟨a, rfl⟩ := ι.surjective α
  simp only [orbitK, Set.mem_ofPred_eq, Set.mem_image, ι.injective.eq_iff, exists_eq_right]
  rw [← kCodes_orbit a a.2]
  constructor
  · rintro ⟨w, hw, h⟩
    obtain ⟨i, hi, rfl⟩ := (mem_WK_iff w).1 hw
    rw [← ι_23, apply_ι_eq_iff, code_kElt hi] at h
    exact ⟨i, hi, h⟩
  · rintro ⟨i, hi, h⟩
    refine ⟨kElt i, (mem_WK_iff _).2 ⟨i, hi, rfl⟩, ?_⟩
    rw [← ι_23, apply_ι_eq_iff, code_kElt hi]
    exact h

theorem sIdx_lt : ∀ y ∈ sIdx, y < 24 := by decide

theorem ncard_orbitK : orbitK.ncard = 6 := by
  have h : {a : Fin 24 | (a : ℕ) ∈ sIdx} = ↑(Finset.univ.filter fun a : Fin 24 => (a : ℕ) ∈ sIdx) :=
    by simp
  rw [orbitK_eq, Set.ncard_image_of_injective _ ι.injective, h, Set.ncard_coe_finset]
  decide +kernel

@[expose] def xSet (i : ℕ) : Set Λ := ι '' {a : Fin 24 | (a : ℕ) ∈ xList.getD i []}

theorem mem_xSet (i : ℕ) (a : Fin 24) : ι a ∈ xSet i ↔ (a : ℕ) ∈ xList.getD i [] := by
  simp [xSet]

theorem image_ι (w : Equiv.Perm Λ) (A : Set (Fin 24)) :
    ⇑w '' (ι '' A) = ι '' {b | ∃ a ∈ A, (code w).getD a 0 = b} := by
  ext β
  obtain ⟨b, rfl⟩ := ι.surjective β
  simp only [Set.mem_image, ι.injective.eq_iff, exists_eq_right, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨_, ⟨a, ha, rfl⟩, h⟩
    exact ⟨a, ha, (apply_ι_eq_iff w a b).1 h⟩
  · rintro ⟨a, ha, h⟩
    exact ⟨ι a, ⟨a, ha, rfl⟩, (apply_ι_eq_iff w a b).2 h⟩

theorem gen_image_xSet (k : Fin 4) {i : ℕ} (hi : i < 24) :
    ∃ m < 24, ⇑(gen k) '' xSet i = xSet m := by
  obtain ⟨m, hm, h⟩ := xList_closed i hi k
  refine ⟨m, hm, ?_⟩
  rw [xSet, image_ι, xSet, code_gen]
  congr 1
  ext b
  simp only [Set.mem_ofPred_eq]
  rw [h b b.2]
  constructor
  · rintro ⟨a, ha, hab⟩
    exact ⟨a, ha, hab⟩
  · rintro ⟨y, hy, hyb⟩
    exact ⟨⟨y, xList_lt i hi y hy⟩, hy, hyb⟩

theorem image_orbitK_eq_xSet {w : Equiv.Perm Λ} (hw : w ∈ W) : ∃ i < 24, ⇑w '' orbitK = xSet i := by
  have hstep : ∀ (k : Fin 4) (y : Equiv.Perm Λ), (∃ i < 24, ⇑y '' orbitK = xSet i) →
      ∃ i < 24, ⇑(gen k * y) '' orbitK = xSet i := by
    rintro k y ⟨i, hi, h⟩
    obtain ⟨m, hm, h'⟩ := gen_image_xSet k hi
    exact ⟨m, hm, by rw [Equiv.Perm.coe_mul, Set.image_comp, h, h']⟩
  induction hw using Subgroup.closure_induction_left with
  | one =>
    refine ⟨0, by norm_num, ?_⟩
    rw [Equiv.Perm.coe_one, Set.image_id, orbitK_eq, xSet, xList_zero]
  | mul_left x hx y _ ih =>
    obtain ⟨k, rfl⟩ := hx
    exact hstep k y ih
  | inv_mul_cancel x hx y _ ih =>
    obtain ⟨k, rfl⟩ := hx
    rw [gen_inv]
    exact hstep k y ih

theorem xSet_eq_image {i : ℕ} (hi : i < 24) :
    xSet i = ⇑(wordProd (xWords.getD i [])) '' orbitK := by
  rw [orbitK_eq, image_ι, xSet, code_wordProd]
  congr 1
  ext b
  simp only [Set.mem_ofPred_eq]
  rw [xWords_image i hi b b.2]
  constructor
  · rintro ⟨y, hy, hyb⟩
    exact ⟨⟨y, sIdx_lt y hy⟩, hy, hyb⟩
  · rintro ⟨a, ha, hab⟩
    exact ⟨a, ha, hab⟩

theorem translates_eq :
    {X : Set Λ | ∃ w ∈ W, X = ⇑w '' orbitK} = xSet '' {i | i < 24} := by
  ext X
  simp only [Set.mem_ofPred_eq, Set.mem_image]
  constructor
  · rintro ⟨w, hw, rfl⟩
    obtain ⟨i, hi, h⟩ := image_orbitK_eq_xSet hw
    exact ⟨i, hi, h.symm⟩
  · rintro ⟨i, hi, rfl⟩
    exact ⟨_, wordProd_mem_W _, xSet_eq_image hi⟩

theorem xSet_injOn : Set.InjOn xSet {i | i < 24} := by
  intro i hi m hm h
  rcases xList_distinct i hi m hm with h' | ⟨a, ha, hne⟩
  · exact h'
  · exfalso
    apply hne
    rw [← mem_xSet i ⟨a, ha⟩, ← mem_xSet m ⟨a, ha⟩, h]

theorem ncard_translates : {X : Set Λ | ∃ w ∈ W, X = ⇑w '' orbitK}.ncard = 24 := by
  rw [translates_eq, xSet_injOn.ncard_image]
  have : {i : ℕ | i < 24} = ↑(Finset.range 24) := by ext; simp
  rw [this, Set.ncard_coe_finset, Finset.card_range]

theorem exists_translate_iff {α β : Λ} (hne : α ≠ β) :
    (∃ w ∈ W, α ∈ ⇑w '' orbitK ∧ β ∈ ⇑w '' orbitK) ↔ form α.1 β.1 = 1 ∨ form α.1 β.1 = 0 := by
  obtain ⟨a, rfl⟩ := ι.surjective α
  obtain ⟨b, rfl⟩ := ι.surjective β
  have hab : (a : ℕ) ≠ b := fun h => hne (congrArg ι (Fin.ext h))
  rw [ι_apply, ι_apply]
  rcases xList_pair a a.2 b b.2 with h | h
  · exact absurd h hab
  rw [← h]
  constructor
  · rintro ⟨w, hw, ha, hb⟩
    obtain ⟨i, hi, hX⟩ := image_orbitK_eq_xSet hw
    rw [hX, mem_xSet] at ha hb
    exact ⟨i, hi, ha, hb⟩
  · rintro ⟨i, hi, ha, hb⟩
    refine ⟨wordProd (xWords.getD i []), wordProd_mem_W _, ?_, ?_⟩
    · rw [← xSet_eq_image hi, mem_xSet]
      exact ha
    · rw [← xSet_eq_image hi, mem_xSet]
      exact hb

theorem level_apply_of_mem_WJ {v : Equiv.Perm Λ} (hv : v ∈ WJ) (α : Λ) :
    form θ (v α).1 = form θ α.1 := by
  have h : v α ∈ MulAction.orbit WJ α := ⟨⟨v, hv⟩, rfl⟩
  rw [orbit_WJ] at h
  exact h

theorem double_coset_eq :
    {x : Equiv.Perm Λ | ∃ a ∈ WJ, ∃ b ∈ WK, ∃ c ∈ WJ, x = a * b * c} =
      {w | w ∈ W ∧ (form θ (w θΛ).1 = 2 ∨ form θ (w θΛ).1 = 1 ∨ form θ (w θΛ).1 = 0)} := by
  ext x
  simp only [Set.mem_ofPred_eq]
  constructor
  · rintro ⟨a, ha, b, hb, c, hc, rfl⟩
    refine ⟨Subgroup.mul_mem _ (Subgroup.mul_mem _ (WJ_le_W ha) (WK_le_W hb)) (WJ_le_W hc), ?_⟩
    rw [Equiv.Perm.mul_apply, apply_θΛ_of_mem_WJ hc, Equiv.Perm.mul_apply,
      level_apply_of_mem_WJ ha]
    have hbθ : b θΛ ∈ orbitK := ⟨b, hb, rfl⟩
    rw [orbitK_eq] at hbθ
    obtain ⟨y, hy, hyb⟩ := hbθ
    rw [← hyb, form_θ_ι]
    exact sIdx_lev y hy
  · rintro ⟨hw, hlev⟩
    obtain ⟨z, hz⟩ := ι.surjective (x θΛ)
    rw [← hz, form_θ_ι] at hlev
    obtain ⟨i, hi, y, hy, hyz⟩ := jCodes_sIdx z z.2 hlev
    have hyK : ι ⟨y, sIdx_lt y hy⟩ ∈ orbitK := by
      rw [orbitK_eq]
      exact ⟨_, hy, rfl⟩
    obtain ⟨b, hb, hbθ⟩ := hyK
    have hxθ : x θΛ = (jElt i * b) θΛ := by
      rw [Equiv.Perm.mul_apply, hbθ, ← hz, eq_comm, apply_ι_eq_iff, code_jElt hi]
      exact hyz
    have hc : (jElt i * b)⁻¹ * x ∈ WJ := by
      rw [mem_WJ_iff_stabilizer]
      refine ⟨Subgroup.mul_mem _ (Subgroup.inv_mem _ (Subgroup.mul_mem _ (WJ_le_W (jElt_mem hi))
        (WK_le_W hb))) hw, ?_⟩
      rw [Equiv.Perm.mul_apply, Equiv.Perm.inv_eq_iff_eq]
      exact hxθ
    exact ⟨jElt i, jElt_mem hi, b, hb, _, hc, by rw [mul_inv_cancel_left]⟩

theorem e6_highest_root_folded_point_orbits :
    Nat.card Λ = 24 ∧ Nat.card W = 1152 ∧ Nat.card WJ = 48 ∧ Nat.card WK = 48 ∧
    (∀ w : Equiv.Perm Λ, w ∈ WJ ↔ w ∈ W ∧ w θΛ = θΛ) ∧
    (∀ α : Λ, MulAction.orbit WJ α = {β | form θ β.1 = form θ α.1}) ∧
    Set.range (fun α : Λ => form θ α.1) = {2, 1, 0, -1, -2} ∧
    {α : Λ | form θ α.1 = 2}.ncard = 1 ∧ {α : Λ | form θ α.1 = 1}.ncard = 8 ∧
    {α : Λ | form θ α.1 = 0}.ncard = 6 ∧ {α : Λ | form θ α.1 = -1}.ncard = 8 ∧
    {α : Λ | form θ α.1 = -2}.ncard = 1 ∧
    (∀ (w : Equiv.Perm Λ) (l l' : List (Fin 4)), IsReducedWord w l → IsReducedWord w l' →
      wordWeight l = wordWeight l') ∧
    (∀ w ∈ W, ∃ l, IsReducedWord w l) ∧
    (∀ (w : Equiv.Perm Λ) (l : List (Fin 4)), IsReducedWord w l → qWeight w = wordWeight l) ∧
    ∑ᶠ w ∈ (WJ : Set (Equiv.Perm Λ)), qWeight w = 93555 ∧
    ∑ᶠ w ∈ {w : Equiv.Perm Λ | w ∈ W ∧ form θ (w θΛ).1 = 2}, qWeight w = 93555 * 1 ∧
    ∑ᶠ w ∈ {w : Equiv.Perm Λ | w ∈ W ∧ form θ (w θΛ).1 = 1}, qWeight w = 93555 * 1782 ∧
    ∑ᶠ w ∈ {w : Equiv.Perm Λ | w ∈ W ∧ form θ (w θΛ).1 = 0}, qWeight w = 93555 * 44352 ∧
    ∑ᶠ w ∈ {w : Equiv.Perm Λ | w ∈ W ∧ form θ (w θΛ).1 = -1}, qWeight w = 93555 * 1824768 ∧
    ∑ᶠ w ∈ {w : Equiv.Perm Λ | w ∈ W ∧ form θ (w θΛ).1 = -2}, qWeight w = 93555 * 2097152 ∧
    1 + 1782 + 44352 + 1824768 + 2097152 = 3968055 ∧
    orbitK.ncard = 6 ∧
    {X : Set Λ | ∃ w ∈ W, X = ⇑w '' orbitK}.ncard = 24 ∧
    (∀ α β : Λ, α ≠ β →
      ((∃ w ∈ W, α ∈ ⇑w '' orbitK ∧ β ∈ ⇑w '' orbitK) ↔ form α.1 β.1 = 1 ∨ form α.1 β.1 = 0)) ∧
    {x : Equiv.Perm Λ | ∃ a ∈ WJ, ∃ b ∈ WK, ∃ c ∈ WJ, x = a * b * c} =
      {w | w ∈ W ∧ (form θ (w θΛ).1 = 2 ∨ form θ (w θΛ).1 = 1 ∨ form θ (w θΛ).1 = 0)} := by
  obtain ⟨c2, c1, c0, cm1, cm2⟩ := card_level
  refine ⟨card_Λ, card_W, card_WJ, card_WK, mem_WJ_iff_stabilizer, orbit_WJ, range_level,
    by rw [ncard_level, c2], by rw [ncard_level, c1], by rw [ncard_level, c0],
    by rw [ncard_level, cm1], by rw [ncard_level, cm2],
    fun w l l' => wordWeight_eq_of_isReducedWord, fun w hw => exists_isReducedWord hw,
    fun w l => qWeight_eq_of_isReducedWord, finsum_qWeight_WJ,
    by rw [finsum_level, sum_levelPairs_two], by rw [finsum_level, sum_levelPairs_one],
    by rw [finsum_level, sum_levelPairs_zero], by rw [finsum_level, sum_levelPairs_neg_one],
    by rw [finsum_level, sum_levelPairs_neg_two], by norm_num, ncard_orbitK, ncard_translates,
    fun α β => exists_translate_iff, double_coset_eq⟩

end CFSG.Monster.B.Classical.E6Folded

module

public import CFSG.Quasithin.H13.L32NSp4Inputs
public import CFSG.Quasithin.H13.L32NKGSp4
public import CFSG.LocalAnalysis.ComponentClassification.PresentationLocalSymplecticSix

public section

namespace CFSG.Quasithin.H13.Sp4Cert

open KGCert CFSG.ComponentClassification.PresentationLocal Matrix

abbrev Mat4 : Type := Matrix (Fin 4) (Fin 4) (ZMod 2)

@[expose] def decodeC4 (A : List ℕ) : Mat4 := Matrix.of fun i j => vec4 (A.getD j 0) i

@[expose] def ValidC4 (A : List ℕ) : Prop := A.length = 4 ∧ ∀ c ∈ A, c < 16

@[expose] def colsOf4 (M : Mat4) : List ℕ :=
  [enc4 fun i => M i 0, enc4 fun i => M i 1, enc4 fun i => M i 2, enc4 fun i => M i 3]

theorem validC4_colsOf4 (M : Mat4) : ValidC4 (colsOf4 M) := by
  refine ⟨rfl, fun c hc => ?_⟩
  simp only [colsOf4, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> exact enc4_lt _

theorem decodeC4_colsOf4 (M : Mat4) : decodeC4 (colsOf4 M) = M := by
  ext i j
  fin_cases j <;> simp [decodeC4, colsOf4, vec4_enc4]

theorem vec4_lt_inj {m n : ℕ} (hm : m < 16) (hn : n < 16) (h : vec4 m = vec4 n) : m = n :=
  vec4_inj hm hn h

theorem getD_lt {A : List ℕ} (hA : ValidC4 A) (j : ℕ) : A.getD j 0 < 16 := by
  by_cases hj : j < A.length
  · rw [List.getD_eq_getElem _ _ hj]
    exact hA.2 _ (List.getElem_mem hj)
  · rw [List.getD_eq_default _ _ (by omega)]
    norm_num

theorem decodeC4_injOn {A A' : List ℕ} (hA : ValidC4 A) (hA' : ValidC4 A')
    (h : decodeC4 A = decodeC4 A') : A = A' := by
  apply List.ext_getElem (hA.1.trans hA'.1.symm)
  intro j hj hj'
  have hj4 : j < 4 := hA.1 ▸ hj
  have hcol : vec4 (A.getD j 0) = vec4 (A'.getD j 0) := by
    ext i
    have := congrFun (congrFun h i) ⟨j, hj4⟩
    simpa [decodeC4] using this
  have h1 := vec4_lt_inj (getD_lt hA j) (getD_lt hA' j) hcol
  rwa [List.getD_eq_getElem _ _ hj, List.getD_eq_getElem _ _ hj'] at h1

theorem colsOf4_decodeC4 {A : List ℕ} (hA : ValidC4 A) : colsOf4 (decodeC4 A) = A :=
  decodeC4_injOn (validC4_colsOf4 _) hA (decodeC4_colsOf4 _)

theorem decodeC4_mulVec {A : List ℕ} (hA : A.length = 4) (v : ℕ) :
    (decodeC4 A).mulVec (vec4 v) = vec4 (mulVecC A v) := by
  obtain ⟨e0, e1, e2, e3, -, -, -, -, -, -⟩ := fin_vals
  have h4 : A.getD 4 0 = 0 := List.getD_eq_default _ _ (by omega)
  have h5 : A.getD 5 0 = 0 := List.getD_eq_default _ _ (by omega)
  ext i
  simp only [mulVecC, h4, h5, ite_self, Nat.xor_zero, vec4_xor, vec4_ite, Pi.add_apply,
    Pi.smul_apply, smul_eq_mul, Matrix.mulVec, dotProduct, Fin.sum_univ_four, decodeC4,
    Matrix.of_apply]
  simp only [vec4, bt, e0, e1, e2, e3]
  ring

theorem length_mulC (A B : List ℕ) : (mulC A B).length = B.length := List.length_map _

theorem decodeC4_mulC {A B : List ℕ} (hA : A.length = 4) (hB : B.length = 4) :
    decodeC4 (mulC A B) = decodeC4 A * decodeC4 B := by
  ext i j
  have hj : (j : ℕ) < B.length := by rw [hB]; exact j.isLt
  have hget : (mulC A B).getD j 0 = mulVecC A (B.getD j 0) := by
    simp only [mulC, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hj,
      Option.map_some, Option.getD_some]
  simp only [decodeC4, Matrix.of_apply, Matrix.mul_apply]
  rw [hget, ← decodeC4_mulVec hA]
  simp only [Matrix.mulVec, dotProduct, decodeC4, Matrix.of_apply]

theorem decodeC4_oneC4 : decodeC4 oneC4 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> decide

theorem validC4_oneC4 : ValidC4 oneC4 := ⟨rfl, by decide⟩

theorem mulVecC_lt16 {A : List ℕ} (hA : ValidC4 A) (v : ℕ) : mulVecC A v < 16 := by
  have h4 : A.getD 4 0 = 0 := List.getD_eq_default _ _ (by rw [hA.1])
  have h5 : A.getD 5 0 = 0 := List.getD_eq_default _ _ (by rw [hA.1]; omega)
  have h16 : (16 : ℕ) = 2 ^ 4 := by norm_num
  have hite : ∀ (c : Bool) (n : ℕ), n < 2 ^ 4 → (if c then n else 0) < 2 ^ 4 := by
    intro c n hn
    cases c
    · simp
    · simpa using hn
  have hx : ∀ m n : ℕ, m < 2 ^ 4 → n < 2 ^ 4 → m ^^^ n < 2 ^ 4 := fun m n hm hn =>
    Nat.xor_lt_two_pow hm hn
  simp only [mulVecC, h4, h5, ite_self, Nat.xor_zero]
  rw [h16]
  exact hx _ _ (hx _ _ (hx _ _ (hite _ _ (h16 ▸ getD_lt hA 0)) (hite _ _ (h16 ▸ getD_lt hA 1)))
    (hite _ _ (h16 ▸ getD_lt hA 2))) (hite _ _ (h16 ▸ getD_lt hA 3))

theorem validC4_mulC {A B : List ℕ} (hA : ValidC4 A) (hB : ValidC4 B) : ValidC4 (mulC A B) := by
  refine ⟨(length_mulC A B).trans hB.1, fun c hc => ?_⟩
  obtain ⟨v, -, rfl⟩ := List.mem_map.mp hc
  exact mulVecC_lt16 hA v

theorem codeC_inj {x y : List ℕ} (hx : ValidC4 x) (hy : ValidC4 y) (h : codeC x = codeC y) :
    x = y := by
  have hx0 := getD_lt hx 0
  have hx1 := getD_lt hx 1
  have hx2 := getD_lt hx 2
  have hx3 := getD_lt hx 3
  have hy0 := getD_lt hy 0
  have hy1 := getD_lt hy 1
  have hy2 := getD_lt hy 2
  have hy3 := getD_lt hy 3
  simp only [codeC] at h
  apply List.ext_getElem (hx.1.trans hy.1.symm)
  intro j hj hj'
  have hj4 : j < 4 := hx.1 ▸ hj
  rw [← List.getD_eq_getElem _ 0 hj, ← List.getD_eq_getElem _ 0 hj']
  interval_cases j <;> omega

theorem testBit_foldl_addM (l : List (List ℕ)) (m : ℕ) (c : ℕ) :
    (l.foldl addM m).testBit c = true ↔ m.testBit c = true ∨ ∃ y ∈ l, codeC y = c := by
  induction l generalizing m with
  | nil => simp
  | cons y l ih =>
    rw [List.foldl_cons, ih]
    have hbit : ((1 : ℕ) <<< codeC y).testBit c = true ↔ codeC y = c := by
      rw [Nat.one_shiftLeft, Nat.testBit_two_pow, decide_eq_true_iff]
    simp only [addM, Nat.testBit_or, Bool.or_eq_true, List.mem_cons, exists_eq_or_imp, hbit]
    constructor
    · rintro ((h | h) | h)
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr h)
    · rintro (h | h | h)
      · exact Or.inl (Or.inl h)
      · exact Or.inl (Or.inr h)
      · exact Or.inr h

theorem memM_maskOf {l : List (List ℕ)} {x : List ℕ} :
    memM (maskOf l) x = true ↔ ∃ y ∈ l, codeC y = codeC x := by
  rw [memM, maskOf, testBit_foldl_addM]
  simp

theorem mem_of_memM_maskOf {l : List (List ℕ)} (hl : ∀ y ∈ l, ValidC4 y) {x : List ℕ}
    (hx : ValidC4 x) (h : memM (maskOf l) x = true) : x ∈ l := by
  obtain ⟨y, hy, hyx⟩ := memM_maskOf.mp h
  rwa [← codeC_inj (hl y hy) hx hyx]

theorem memM_maskOf_of_mem {l : List (List ℕ)} {x : List ℕ} (h : x ∈ l) :
    memM (maskOf l) x = true :=
  memM_maskOf.mpr ⟨x, h, rfl⟩

theorem subM_iff {m m' : ℕ} : subM m m' = true ↔ ∀ c, m.testBit c = true → m'.testBit c = true := by
  constructor
  · intro h c hc
    have h1 : m &&& m' = m := by simpa [subM] using h
    have := congrArg (fun n => n.testBit c) h1
    simp only [Nat.testBit_and, hc, Bool.true_and] at this
    exact this
  · intro h
    simp only [subM, beq_iff_eq]
    apply Nat.eq_of_testBit_eq
    intro c
    rw [Nat.testBit_and]
    cases hc : m.testBit c
    · simp
    · simp [h c hc]

@[expose] def formJ (u w : Fin 4 → ZMod 2) : ZMod 2 := u ⬝ᵥ (antidiagGram *ᵥ w)

theorem formJ_eq (u w : Fin 4 → ZMod 2) :
    formJ u w = u 0 * w 3 + u 1 * w 2 + u 2 * w 1 + u 3 * w 0 := by
  simp only [formJ, dotProduct, Matrix.mulVec, Fin.sum_univ_four, antidiagGram, Matrix.of_apply]
  norm_num

theorem b2z_bJ (u w : ℕ) : b2z (bJ u w) = formJ (vec4 u) (vec4 w) := by
  rw [bJ, b2z_bfN, formJ_eq]
  simp only [bfE, KGCert.gram]
  have h12 : ∀ k : ℕ, (12 : ℕ).testBit k = (k == 2 || k == 3) := by
    intro k
    rcases Nat.lt_or_ge k 4 with hk | hk
    · interval_cases k <;> rfl
    · have : (12 : ℕ) < 2 ^ k :=
        lt_of_lt_of_le (by norm_num) (Nat.pow_le_pow_right (by norm_num) hk)
      rw [Nat.testBit_lt_two_pow this]
      simp only [Bool.false_eq, Bool.or_eq_false_iff, beq_eq_false_iff_ne, ne_eq]
      omega
  obtain ⟨-, -, -, -, f0, f1, f2, f3, f4, f5⟩ := fin_vals
  simp only [f0, f1, f2, f3, f4, f5, h12]
  simp [b2z]
  ring

theorem antidiagGram_apply (i j : Fin 4) :
    antidiagGram i j = b2z (bJ (2 ^ (i : ℕ)) (2 ^ (j : ℕ))) := by
  fin_cases i <;> fin_cases j <;> decide

theorem transpose_mul_mul_apply (M : Mat4) (i j : Fin 4) :
    (Mᵀ * antidiagGram * M) i j = formJ (fun k => M k i) (fun k => M k j) := by
  simp only [Matrix.mul_apply, Matrix.transpose_apply, formJ, dotProduct, Matrix.mulVec,
    Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
  ring

theorem isSympC_iff {A : List ℕ} : isSympC A = true ↔
    (decodeC4 A)ᵀ * antidiagGram * decodeC4 A = antidiagGram := by
  have hcol : ∀ j : Fin 4, (fun k => decodeC4 A k j) = vec4 (A.getD j 0) := fun j => rfl
  constructor
  · intro h
    ext i j
    rw [transpose_mul_mul_apply, hcol, hcol, ← b2z_bJ, antidiagGram_apply]
    have := List.all_eq_true.mp (List.all_eq_true.mp h i (List.mem_range.mpr i.isLt)) j
      (List.mem_range.mpr j.isLt)
    rw [beq_iff_eq] at this
    rw [this]
  · intro h
    refine List.all_eq_true.mpr fun i hi => List.all_eq_true.mpr fun j hj => ?_
    have hi4 := List.mem_range.mp hi
    have hj4 := List.mem_range.mp hj
    have := congrFun (congrFun h ⟨i, hi4⟩) ⟨j, hj4⟩
    rw [transpose_mul_mul_apply, hcol, hcol, ← b2z_bJ, antidiagGram_apply] at this
    rw [beq_iff_eq]
    exact b2z_inj this

theorem mem_spElsC {A : List ℕ} : A ∈ spElsC ↔ ValidC4 A ∧ isSympC A = true := by
  constructor
  · intro h
    simp only [spElsC, List.mem_flatMap, List.mem_range, List.mem_filterMap,
      Option.ite_none_right_eq_some, Option.some.injEq] at h
    obtain ⟨a, ha, b, hb, c, hc, d, hd, hs, rfl⟩ := h
    refine ⟨⟨rfl, ?_⟩, hs⟩
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    omega
  · rintro ⟨⟨hl, hlt⟩, hs⟩
    match A, hl, hlt, hs with
    | [a, b, c, d], _, hlt, hs =>
      simp only [spElsC, List.mem_flatMap, List.mem_range, List.mem_filterMap,
        Option.ite_none_right_eq_some, Option.some.injEq]
      exact ⟨a, hlt a (by simp), b, hlt b (by simp), c, hlt c (by simp), d, hlt d (by simp),
        hs, rfl⟩

theorem colsOf4_mem_spElsC {g : GL (Fin 4) (ZMod 2)} (hg : g ∈ sympFour) :
    colsOf4 (g : Mat4) ∈ spElsC := by
  rw [mem_spElsC]
  refine ⟨validC4_colsOf4 _, ?_⟩
  rw [isSympC_iff, decodeC4_colsOf4]
  exact hg

end CFSG.Quasithin.H13.Sp4Cert

module

public import Certificates.Certificate111601
public import CFSG.LocalAnalysis.ComponentClassification.J2CoverModelsSylow
public import CFSG.Sporadic.J2.Representations.Module12Irreducible

public section

namespace CFSG.RankThree.PartTwo.J2Residue.C4725

open CFSG.ComponentClassification.J2Cover.Models CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
open CFSG.Sporadic.J2.Module12

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem psiCheck_spec {i j : ℕ} (hi : i < 4725) (hj : j < 2) :
    mulCols (colsJ j) psiData[actT j i]! = psiData[i]! := by
  have h := (Certificates.certificate111601).1
  unfold psiCheck at h
  exact beq_iff_eq.1 (allLt_spec (allLt_spec h hi) hj)

theorem orbitCheck_spec {i : ℕ} (hi : i < 4725) :
    (psiData[i]! ^^^ psiData[xAct i]! ^^^ psiData[xAct (xAct i)]!) = 0 := by
  have h := (Certificates.certificate111601).2.1
  unfold orbitCheck at h
  exact beq_iff_eq.1 (allLt_spec h hi)

theorem basisCheck_spec :
    basisPt 0 = 0 ∧ (∀ l < 12, basisPt l < 4725) ∧
      (∀ c < 12, mulCols basisCols (binvCols.getD c 0) = 2 ^ c) ∧
      (∀ c < 12, mulCols binvCols (basisCols.getD c 0) = 2 ^ c) := by
  have h := (Certificates.certificate111601).2.2.1
  unfold basisCheck at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨h0, hlt⟩, h1⟩, h2⟩ := h
  exact ⟨h0, fun l hl => of_decide_eq_true (allLt_spec hlt hl),
    fun c hc => beq_iff_eq.1 (allLt_spec h1 hc), fun c hc => beq_iff_eq.1 (allLt_spec h2 hc)⟩

theorem keptCheck_spec {n : ℕ} (hn : n < 4713) :
    (keptCodes[n]! % 3 = 0 ∧ keptCodes[n]! / 3 < 4725 ∧
        ((keptTri ())[n]!).1 = keptCodes[n]! / 3 ∧
        ((keptTri ())[n]!).2.1 = xAct ((keptTri ())[n]!).1 ∧
        ((keptTri ())[n]!).2.2 = xAct ((keptTri ())[n]!).2.1) ∨
      (keptCodes[n]! / 3 < n ∧
        ((keptTri ())[n]!).1 = actT (keptCodes[n]! % 3 - 1) ((keptTri ())[keptCodes[n]! / 3]!).1 ∧
        ((keptTri ())[n]!).2.1 =
          actT (keptCodes[n]! % 3 - 1) ((keptTri ())[keptCodes[n]! / 3]!).2.1 ∧
        ((keptTri ())[n]!).2.2 =
          actT (keptCodes[n]! % 3 - 1) ((keptTri ())[keptCodes[n]! / 3]!).2.2) := by
  have h := (Certificates.certificate111601).2.2.2.1
  unfold keptCheck at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  have hn' := allLt_spec h.2 hn
  by_cases hr : keptCodes[n]! % 3 = 0
  · left
    simp only [hr, ↓reduceIte, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hn'
    exact ⟨hr, hn'.1.1.1, hn'.1.1.2, hn'.1.2, hn'.2⟩
  · right
    simp only [hr, ↓reduceIte, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hn'
    exact ⟨hn'.1.1.1, hn'.1.1.2, hn'.1.2, hn'.2⟩

theorem targetCheck_spec {l j : ℕ} (hl : l < 12) (hj : j < 2) :
    (∀ n ∈ maskList (2 * l + j), n < 4713) ∧
      xorTri (keptTri ()) (maskList (2 * l + j)) =
        2 ^ actT j (basisPt l) ^^^ coeffXor (tCoeffs.getD (2 * l + j) 0) := by
  have h := (Certificates.certificate111601).2.2.2.2.1
  unfold targetCheck at h
  have h' := allLt_spec (allLt_spec h hl) hj
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, decide_eq_true_eq] at h'
  exact h'

theorem conjCheck_spec :
    eqA 315 (compA 315 (wordArr gWord) CFSG.RankThree.PartTwo.Sec4.Sporadic.J2.zArr)
        (compA 315 (wordArr x0Word) (wordArr gWord)) = true ∧
      eqA 315 (compA 315 (wordArr x0Word) (compA 315 (wordArr x0Word) (wordArr x0Word)))
        (idA 315) = true := by
  have h := (Certificates.certificate111601).2.2.2.2.2
  unfold conjCheck at h
  simpa only [Bool.and_eq_true] using h

@[expose] def bv (x : ℕ) : Fin 12 → ZMod 2 := fun r => if x.testBit r then 1 else 0

@[expose] def matOfCols (cols : List ℕ) : Matrix (Fin 12) (Fin 12) (ZMod 2) :=
  Matrix.of fun r c => bv (cols.getD c 0) r

theorem bv_xor (x y : ℕ) : bv (x ^^^ y) = bv x + bv y := by
  funext r
  simp only [bv, Nat.testBit_xor, Pi.add_apply]
  cases x.testBit r <;> cases y.testBit r <;> decide

theorem bv_zero : bv 0 = 0 := by
  funext r
  simp [bv]

theorem bv_two_pow (c : Fin 12) : bv (2 ^ (c : ℕ)) = Pi.single c 1 := by
  funext r
  simp only [bv, Nat.testBit_two_pow, Pi.single_apply, decide_eq_true_eq]
  by_cases h : (c : ℕ) = r
  · rw [if_pos h, if_pos (Fin.ext h).symm]
  · rw [if_neg h, if_neg fun h' => h (congrArg Fin.val h'.symm)]

theorem bv_foldl {α : Type*} (l : List α) (f : α → ℕ) (x : ℕ) :
    bv (l.foldl (fun acc n => acc ^^^ f n) x) = bv x + (l.map fun n => bv (f n)).sum := by
  induction l generalizing x with
  | nil => simp
  | cons a l ih => rw [List.foldl_cons, ih, bv_xor, List.map_cons, List.sum_cons, add_assoc]

theorem bv_mulCols (cols : List ℕ) (x : ℕ) :
    bv (mulCols cols x) = (matOfCols cols).mulVec (bv x) := by
  have e : mulCols cols x = (List.finRange 12).foldl
      (fun acc (c : Fin 12) => acc ^^^ if x.testBit c.val then cols.getD c.val 0 else 0) 0 := by
    rw [mulCols]
    congr 1
    funext acc c
    split_ifs <;> simp
  rw [e, bv_foldl, bv_zero, zero_add, ← Fin.sum_univ_def]
  funext r
  simp only [Finset.sum_apply, Matrix.mulVec, dotProduct, matOfCols, Matrix.of_apply, bv]
  refine Finset.sum_congr rfl fun c _ => ?_
  split_ifs <;> simp_all

@[expose] def Mj (j : ℕ) : Matrix (Fin 12) (Fin 12) (ZMod 2) := matOfCols (colsJ j)

theorem Mj_zero : Mj 0 = Amat := by
  rw [Amat_toM]
  decide +kernel

theorem Mj_one : Mj 1 = Bmat := by
  rw [Bmat_toM]
  decide +kernel

theorem exists_inv_mul_Mj {j : ℕ} (hj : j < 2) :
    ∃ N : Matrix (Fin 12) (Fin 12) (ZMod 2), N * Mj j = 1 := by
  interval_cases j
  · exact ⟨toM12 a12, by rw [Mj_zero, Amat_toM, a12_mul]⟩
  · exact ⟨toM12 b12i, by rw [Mj_one, Bmat_toM, b12i_mul]⟩

theorem eq_zero_of_Mj_mulVec {j : ℕ} (hj : j < 2) {x : Fin 12 → ZMod 2}
    (h : (Mj j).mulVec x = 0) : x = 0 := by
  obtain ⟨N, hN⟩ := exists_inv_mul_Mj hj
  rw [← Matrix.one_mulVec x, ← hN, ← Matrix.mulVec_mulVec, h, Matrix.mulVec_zero]

@[expose] def psiVec (i : ℕ) : Fin 12 → ZMod 2 := bv psiData[i]!

theorem psiVec_equivariant {i j : ℕ} (hi : i < 4725)
    (hj : j < 2) : (Mj j).mulVec (psiVec (actT j i)) = psiVec i := by
  rw [psiVec, psiVec, Mj, ← bv_mulCols, psiCheck_spec hi hj]

theorem psiVec_orbit {i : ℕ} (hi : i < 4725) :
    psiVec i + psiVec (xAct i) + psiVec (xAct (xAct i)) = 0 := by
  rw [psiVec, psiVec, psiVec, ← bv_xor, ← bv_xor, orbitCheck_spec hi, bv_zero]

@[expose] def basisMat : Matrix (Fin 12) (Fin 12) (ZMod 2) := matOfCols basisCols

@[expose] def binvMat : Matrix (Fin 12) (Fin 12) (ZMod 2) := matOfCols binvCols

theorem basisCols_getD {l : ℕ} (hl : l < 12) : basisCols.getD l 0 = psiData[basisPt l]! := by
  simp [basisCols, List.getD_eq_getElem?_getD, hl]

theorem basisMat_apply (r l : Fin 12) : basisMat r l = psiVec (basisPt l) r := by
  rw [basisMat, matOfCols, Matrix.of_apply, basisCols_getD l.isLt, psiVec]

theorem mul_eq_one_of_cols {cols cols' : List ℕ}
    (h : ∀ c < 12, mulCols cols (cols'.getD c 0) = 2 ^ c) :
    matOfCols cols * matOfCols cols' = 1 := by
  ext r c
  have e := congrFun (bv_mulCols cols (cols'.getD c 0)) r
  rw [h c c.isLt, bv_two_pow, Pi.single_apply] at e
  rw [Matrix.mul_apply, Matrix.one_apply, e]
  rfl

theorem basisMat_mul_binvMat : basisMat * binvMat = 1 :=
  mul_eq_one_of_cols basisCheck_spec.2.2.1

theorem binvMat_mul_basisMat : binvMat * basisMat = 1 :=
  mul_eq_one_of_cols basisCheck_spec.2.2.2

theorem mulVec_mem_of_mem_Aalg (U : Submodule (ZMod 2) (Fin 12 → ZMod 2))
    (hA : ∀ v ∈ U, Amat.mulVec v ∈ U) (hB : ∀ v ∈ U, Bmat.mulVec v ∈ U) :
    ∀ X ∈ Aalg, ∀ v ∈ U, X.mulVec v ∈ U := by
  let A' : Subalgebra (ZMod 2) (Matrix (Fin 12) (Fin 12) (ZMod 2)) :=
    { carrier := {X | ∀ v ∈ U, X.mulVec v ∈ U}
      mul_mem' := fun {X Y} hX hY v hv => by
        rw [← Matrix.mulVec_mulVec]
        exact hX _ (hY v hv)
      one_mem' := fun v hv => by
        rw [Matrix.one_mulVec]
        exact hv
      add_mem' := fun {X Y} hX hY v hv => by
        rw [Matrix.add_mulVec]
        exact U.add_mem (hX v hv) (hY v hv)
      zero_mem' := fun v _ => by
        rw [Matrix.zero_mulVec]
        exact U.zero_mem
      algebraMap_mem' := fun c v hv => by
        rw [Algebra.algebraMap_eq_smul_one, Matrix.smul_mulVec, Matrix.one_mulVec]
        exact U.smul_mem c hv }
  have hle : Aalg ≤ A' := Algebra.adjoin_le (by
    rintro X (rfl | rfl)
    exacts [hA, hB])
  exact fun X hX => hle hX

theorem eq_bot_or_eq_top_of_mulVec_mem (U : Submodule (ZMod 2) (Fin 12 → ZMod 2))
    (hA : ∀ v ∈ U, Amat.mulVec v ∈ U) (hB : ∀ v ∈ U, Bmat.mulVec v ∈ U) : U = ⊥ ∨ U = ⊤ :=
  Module12_irreducible U (mulVec_mem_of_mem_Aalg U hA hB)

abbrev PSpace : Type := Fin 4725 → ZMod 2

@[expose] def ev (k : Fin 4725) : PSpace := Pi.single k 1

@[expose] def vecF (x : ℕ) : PSpace := fun k => if x.testBit k then 1 else 0

theorem vecF_xor (x y : ℕ) : vecF (x ^^^ y) = vecF x + vecF y := by
  funext k
  simp only [vecF, Nat.testBit_xor, Pi.add_apply]
  cases x.testBit k <;> cases y.testBit k <;> decide

theorem vecF_zero : vecF 0 = 0 := by
  funext k
  simp [vecF]

theorem vecF_two_pow {a : ℕ} (ha : a < 4725) : vecF (2 ^ a) = ev ⟨a, ha⟩ := by
  funext k
  simp only [vecF, Nat.testBit_two_pow, ev, Pi.single_apply, Fin.ext_iff, decide_eq_true_eq]
  by_cases h : a = (k : ℕ)
  · rw [if_pos h, if_pos h.symm]
  · rw [if_neg h, if_neg (Ne.symm h)]

theorem vecF_foldl {α : Type*} (l : List α) (f : α → ℕ) (x : ℕ) :
    vecF (l.foldl (fun acc n => acc ^^^ f n) x) = vecF x + (l.map fun n => vecF (f n)).sum := by
  induction l generalizing x with
  | nil => simp
  | cons a l ih => rw [List.foldl_cons, ih, vecF_xor, List.map_cons, List.sum_cons, add_assoc]

theorem eq_sum_ev (f : PSpace) : f = ∑ k, f k • ev k := by
  funext i
  simp [ev, Finset.sum_apply, Pi.single_apply]

@[expose] noncomputable def wordP (w : List ℕ) : P :=
  (w.map letterP).prod

theorem coe_wordP (w : List ℕ) :
    (wordP w : Perm315) = wordPerm w := by
  induction w with
  | nil => rfl
  | cons k w ih =>
    rw [wordP, List.map_cons, List.prod_cons, Subgroup.coe_mul, ← wordP, ih, wordPerm_cons]
    rfl

@[expose] noncomputable def x0P : P := wordP x0Word

theorem cosetAct_letterP
    (i : Fin 4725) (j : ℕ) : (cosetAct i (letterP j) : ℕ) = actT j i := by
  rcases Nat.lt_or_ge j 2 with hj | hj
  · exact (cosetAct_letter i hj).1
  · have hj0 : j ≠ 0 := by omega
    have h1 : letterP j = letterP 1 := Subtype.ext (by simp [letterP, letter, hj0])
    have h2 : actT j i = actT 1 i := by simp [actT, hj0]
    rw [h1, h2]
    exact (cosetAct_letter i (by norm_num)).1

theorem actT_lt (j : ℕ)
    (i : Fin 4725) : actT j i < 4725 := by
  rw [← cosetAct_letterP]
  exact (cosetAct i (letterP j)).isLt

theorem cosetAct_wordP
    (w : List ℕ) (i : Fin 4725) : (cosetAct i (wordP w) : ℕ) = wordAct w i := by
  induction w generalizing i with
  | nil =>
    show (cosetAct i 1 : ℕ) = i
    rw [cosetAct_one]
  | cons j w ih =>
    rw [wordP, List.map_cons, List.prod_cons, cosetAct_mul, ← wordP, ih, wordAct, wordAct,
      List.foldl_cons, cosetAct_letterP]

theorem xAct_lt (i : Fin 4725) :
    xAct i < 4725 := by
  rw [xAct, ← cosetAct_wordP]
  exact (cosetAct i (wordP x0Word)).isLt

theorem cosetAct_x0P
    (i : Fin 4725) : cosetAct i x0P = ⟨xAct i, xAct_lt i⟩ :=
  Fin.ext (cosetAct_wordP x0Word i)

theorem repP_eq_wordP (k : ℕ) : repP k = wordP (cosetWord k) :=
  Subtype.ext (by rw [coe_wordP]; exact rep_eq k)

theorem cosetAct_zero_repP
    (k : Fin 4725) : cosetAct 0 (repP k) = k := by
  refine (decomp_unique (i := 0) (g := repP k) (s := 1) (k := k) ?_).2
  simp [repP, rep_zero]

theorem x0P_pow_three :
    x0P ^ 3 = 1 := by
  have h := eq_of_eqA (rep_compA (rep_wordArr x0Word) (rep_compA (rep_wordArr x0Word)
    (rep_wordArr x0Word))) rep_idA conjCheck_spec.2
  apply Subtype.ext
  rw [x0P, SubmonoidClass.coe_pow, coe_wordP, pow_three]
  exact h

@[expose] noncomputable def T
    (g : P) : PSpace →ₗ[ZMod 2] PSpace :=
  LinearMap.funLeft (ZMod 2) (ZMod 2) (cosetPerm g).symm

theorem T_ev (g : P)
    (k : Fin 4725) : T g (ev k) = ev (cosetAct k g) := by
  funext i
  simp only [T, LinearMap.funLeft_apply, ev]
  rw [← Function.comp_apply (f := Pi.single k (1 : ZMod 2)), Pi.single_comp_equiv,
    Equiv.symm_symm, cosetPerm_apply]

theorem T_inv_apply (g : P)
    (f : PSpace) : T g (T g⁻¹ f) = f := by
  funext i
  show f (cosetAct (cosetAct i g⁻¹) g⁻¹⁻¹) = f i
  rw [← cosetAct_mul, inv_inv, inv_mul_cancel, cosetAct_one]

@[expose] noncomputable def Psi : PSpace →ₗ[ZMod 2] (Fin 12 → ZMod 2) :=
  Fintype.linearCombination (ZMod 2) fun k : Fin 4725 => psiVec k

theorem Psi_apply (f : PSpace) : Psi f = ∑ k, f k • psiVec k :=
  Fintype.linearCombination_apply _ _ _

theorem Psi_ev (k : Fin 4725) : Psi (ev k) = psiVec k := by
  rw [ev, Psi, Fintype.linearCombination_apply_single, one_smul]

theorem Mj_mulVec_Psi_T
    {j : ℕ} (hj : j < 2) (f : PSpace) :
    (Mj j).mulVec (Psi (T (letterP j) f)) = Psi f := by
  rw [Psi_apply, Psi_apply, ← Equiv.sum_comp (cosetPerm (letterP j))]
  simp only [T, LinearMap.funLeft_apply, Equiv.symm_apply_apply, Matrix.mulVec_sum,
    Matrix.mulVec_smul]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [cosetPerm_apply, cosetAct_letterP, psiVec_equivariant k.isLt hj]

theorem Psi_T_eq_zero
    {j : ℕ} (hj : j < 2) {f : PSpace} (hf : Psi f = 0) :
    Psi (T (letterP j) f) = 0 :=
  eq_zero_of_Mj_mulVec hj (by rw [Mj_mulVec_Psi_T hj, hf])

theorem Psi_orbit
    (a : Fin 4725) :
    Psi (ev a + ev (cosetAct a x0P) + ev (cosetAct (cosetAct a x0P) x0P)) = 0 := by
  rw [map_add, map_add, Psi_ev, Psi_ev, Psi_ev, cosetAct_x0P, cosetAct_x0P]
  exact psiVec_orbit a.isLt

@[expose] noncomputable def sec : (Fin 12 → ZMod 2) →ₗ[ZMod 2] PSpace :=
  (Fintype.linearCombination (ZMod 2) fun l : Fin 12 => vecF (2 ^ basisPt l)) ∘ₗ
    binvMat.mulVecLin

theorem basisPt_lt (l : Fin 12) : basisPt l < 4725 :=
  basisCheck_spec.2.1 l l.isLt

theorem Psi_vecF_basis (l : Fin 12) :
    Psi (vecF (2 ^ basisPt l)) = psiVec (basisPt l) := by
  rw [vecF_two_pow (basisPt_lt l), Psi_ev]

theorem Psi_sec (y : Fin 12 → ZMod 2) : Psi (sec y) = y := by
  have h1 : ∀ c : Fin 12 → ZMod 2, Psi (∑ l, c l • vecF (2 ^ basisPt l)) = basisMat.mulVec c := by
    intro c
    funext r
    rw [map_sum]
    simp only [map_smul, Psi_vecF_basis, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
      Matrix.mulVec, dotProduct, basisMat_apply]
    exact Finset.sum_congr rfl fun l _ => mul_comm _ _
  rw [sec, LinearMap.comp_apply, Fintype.linearCombination_apply, h1, Matrix.mulVecLin_apply,
    Matrix.mulVec_mulVec, basisMat_mul_binvMat, Matrix.one_mulVec]

theorem vecF_basis_mem_range_sec (l : Fin 12) :
    vecF (2 ^ basisPt l) ∈ LinearMap.range sec := by
  refine ⟨basisMat.mulVec (Pi.single l 1), ?_⟩
  rw [sec, LinearMap.comp_apply, Matrix.mulVecLin_apply, Matrix.mulVec_mulVec,
    binvMat_mul_basisMat, Matrix.one_mulVec, Fintype.linearCombination_apply_single, one_smul]

theorem vecF_triBits
    {t : ℕ × ℕ × ℕ} (h1 : t.1 < 4725) (h2 : t.2.1 < 4725) (h3 : t.2.2 < 4725) :
    vecF (triBits t) = ev ⟨t.1, h1⟩ + ev ⟨t.2.1, h2⟩ + ev ⟨t.2.2, h3⟩ := by
  rw [triBits, vecF_xor, vecF_xor, vecF_two_pow h1, vecF_two_pow h2, vecF_two_pow h3]

theorem kept_mem
    (W : Submodule (ZMod 2) PSpace)
    (hT : ∀ j < 2, ∀ f ∈ W, T (letterP j) f ∈ W)
    (hO : ∀ a : Fin 4725, ev a + ev (cosetAct a x0P) + ev (cosetAct (cosetAct a x0P) x0P) ∈ W) :
    ∀ n < 4713, ∃ (h1 : ((keptTri ())[n]!).1 < 4725) (h2 : ((keptTri ())[n]!).2.1 < 4725)
      (h3 : ((keptTri ())[n]!).2.2 < 4725), vecF (triBits (keptTri ())[n]!) ∈ W := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro hn
  rcases keptCheck_spec hn with ⟨-, ha, e1, e2, e3⟩ | ⟨hq, e1, e2, e3⟩
  · set t := (keptTri ())[n]!
    have h1 : t.1 < 4725 := e1 ▸ ha
    have h2 : t.2.1 < 4725 := e2 ▸ xAct_lt ⟨t.1, h1⟩
    have h3 : t.2.2 < 4725 := e3 ▸ xAct_lt ⟨t.2.1, h2⟩
    refine ⟨h1, h2, h3, ?_⟩
    rw [vecF_triBits h1 h2 h3]
    have k1 : cosetAct ⟨t.1, h1⟩ x0P = ⟨t.2.1, h2⟩ := by
      rw [cosetAct_x0P]
      exact Fin.ext e2.symm
    have k2 : cosetAct ⟨t.2.1, h2⟩ x0P = ⟨t.2.2, h3⟩ := by
      rw [cosetAct_x0P]
      exact Fin.ext e3.symm
    have := hO ⟨t.1, h1⟩
    rwa [k1, k2] at this
  · set t := (keptTri ())[n]!
    set q := keptCodes[n]! / 3
    set j := keptCodes[n]! % 3 - 1
    have hj : j < 2 := by omega
    obtain ⟨g1, g2, g3, hp⟩ := ih q hq (by omega)
    set p := (keptTri ())[q]!
    have h1 : t.1 < 4725 := e1 ▸ actT_lt j ⟨p.1, g1⟩
    have h2 : t.2.1 < 4725 := e2 ▸ actT_lt j ⟨p.2.1, g2⟩
    have h3 : t.2.2 < 4725 := e3 ▸ actT_lt j ⟨p.2.2, g3⟩
    refine ⟨h1, h2, h3, ?_⟩
    have k1 : cosetAct ⟨p.1, g1⟩ (letterP j) = ⟨t.1, h1⟩ :=
      Fin.ext ((cosetAct_letterP _ j).trans e1.symm)
    have k2 : cosetAct ⟨p.2.1, g2⟩ (letterP j) = ⟨t.2.1, h2⟩ :=
      Fin.ext ((cosetAct_letterP _ j).trans e2.symm)
    have k3 : cosetAct ⟨p.2.2, g3⟩ (letterP j) = ⟨t.2.2, h3⟩ :=
      Fin.ext ((cosetAct_letterP _ j).trans e3.symm)
    have key : vecF (triBits t) = T (letterP j) (vecF (triBits p)) := by
      rw [vecF_triBits h1 h2 h3, vecF_triBits g1 g2 g3, map_add, map_add, T_ev, T_ev, T_ev, k1,
        k2, k3]
    rw [key]
    exact hT j hj _ hp

theorem range_sec_sup_eq_top
    (W : Submodule (ZMod 2) PSpace)
    (hT : ∀ j < 2, ∀ f ∈ W, T (letterP j) f ∈ W)
    (hO : ∀ a : Fin 4725, ev a + ev (cosetAct a x0P) + ev (cosetAct (cosetAct a x0P) x0P) ∈ W) :
    LinearMap.range sec ⊔ W = ⊤ := by
  set Z := LinearMap.range sec ⊔ W
  have hsec : ∀ l : Fin 12, vecF (2 ^ basisPt l) ∈ Z := fun l =>
    Submodule.mem_sup_left (vecF_basis_mem_range_sec l)
  have htarget : ∀ l : Fin 12, ∀ j < 2,
      ev (cosetAct ⟨basisPt l, basisPt_lt l⟩ (letterP j)) ∈ Z := by
    intro l j hj
    obtain ⟨hall, heq⟩ := targetCheck_spec l.isLt hj
    have hb : actT j (basisPt l) < 4725 := actT_lt j ⟨basisPt l, basisPt_lt l⟩
    have hev : ev (cosetAct ⟨basisPt l, basisPt_lt l⟩ (letterP j)) =
        vecF (2 ^ actT j (basisPt l)) := by
      rw [vecF_two_pow hb]
      congr 1
      exact Fin.ext (cosetAct_letterP _ j)
    have hW : vecF (xorTri (keptTri ()) (maskList (2 * l + j))) ∈ W := by
      rw [xorTri, vecF_foldl, vecF_zero, zero_add]
      refine list_sum_mem fun x hx => ?_
      obtain ⟨n, hn, rfl⟩ := List.mem_map.1 hx
      obtain ⟨-, -, -, h⟩ := kept_mem W hT hO n (hall n hn)
      exact h
    have hC : vecF (coeffXor (tCoeffs.getD (2 * l + j) 0)) ∈ LinearMap.range sec := by
      have e : coeffXor (tCoeffs.getD (2 * l + j) 0) = (List.range 12).foldl
          (fun acc l' => acc ^^^ if (tCoeffs.getD (2 * l + j) 0).testBit l' then
            2 ^ basisPt l' else 0) 0 := by
        rw [coeffXor]
        congr 1
        funext acc l'
        split_ifs <;> simp
      rw [e, vecF_foldl, vecF_zero, zero_add]
      refine list_sum_mem fun x hx => ?_
      obtain ⟨l', hl', rfl⟩ := List.mem_map.1 hx
      split_ifs
      · exact vecF_basis_mem_range_sec ⟨l', List.mem_range.1 hl'⟩
      · rw [vecF_zero]
        exact Submodule.zero_mem _
    rw [hev]
    have e2 : vecF (2 ^ actT j (basisPt l)) = vecF (xorTri (keptTri ()) (maskList (2 * l + j))) +
        vecF (coeffXor (tCoeffs.getD (2 * l + j) 0)) := by
      rw [heq, vecF_xor, add_assoc, CharTwo.add_self_eq_zero, add_zero]
    rw [e2]
    exact Z.add_mem (Submodule.mem_sup_right hW) (Submodule.mem_sup_left hC)
  have hZT : ∀ j < 2, ∀ f ∈ Z, T (letterP j) f ∈ Z := by
    intro j hj f hf
    obtain ⟨u, ⟨y, rfl⟩, w, hw, rfl⟩ := Submodule.mem_sup.1 hf
    rw [map_add]
    refine Z.add_mem ?_ (Submodule.mem_sup_right (hT j hj w hw))
    rw [sec, LinearMap.comp_apply, Fintype.linearCombination_apply, map_sum]
    refine Z.sum_mem fun l _ => ?_
    rw [map_smul, vecF_two_pow (basisPt_lt l), T_ev]
    exact Z.smul_mem _ (htarget l j hj)
  have hZT' : ∀ j : ℕ, ∀ f ∈ Z, T (letterP j) f ∈ Z := by
    intro j f hf
    rcases Nat.lt_or_ge j 2 with hj | hj
    · exact hZT j hj f hf
    · have h1 : letterP j = letterP 1 :=
        Subtype.ext (by simp [letterP, letter, show j ≠ 0 by omega])
      rw [h1]
      exact hZT 1 (by norm_num) f hf
  have hword : ∀ (w : List ℕ) (k : Fin 4725), ev k ∈ Z → ev (cosetAct k (wordP w)) ∈ Z := by
    intro w
    induction w with
    | nil =>
      intro k hk
      rw [show wordP [] = 1 from rfl, cosetAct_one]
      exact hk
    | cons j w ih =>
      intro k hk
      rw [wordP, List.map_cons, List.prod_cons, cosetAct_mul, ← wordP]
      apply ih
      rw [← T_ev]
      exact hZT' j _ hk
  have h0 : ev 0 ∈ Z := by
    have := hsec 0
    rwa [vecF_two_pow (basisPt_lt 0), show (⟨basisPt ((0 : Fin 12) : ℕ), basisPt_lt 0⟩ :
      Fin 4725) = 0 from Fin.ext basisCheck_spec.1] at this
  have hall : ∀ k : Fin 4725, ev k ∈ Z := by
    intro k
    have := hword (cosetWord k) 0 h0
    rwa [← repP_eq_wordP, cosetAct_zero_repP] at this
  refine eq_top_iff.2 fun f _ => ?_
  rw [eq_sum_ev f]
  exact Z.sum_mem fun k _ => Z.smul_mem _ (hall k)

section Prop33

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

theorem exists_fixed_ne_zero
    [Finite V] [Nontrivial V] (ρ : P →* Module.End (ZMod 2) V) :
    ∃ v : V, v ≠ 0 ∧ ∀ s : S, ρ (incl s) v = v := by
  letI : MulAction S V := MulAction.compHom V (ρ.comp incl)
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hS : IsPGroup 2 S := IsPGroup.of_card (n := 7) (by rw [card_S]; norm_num)
  have h2 : 2 ∣ Nat.card V := by
    obtain ⟨v, hv⟩ := exists_ne (0 : V)
    have hv2 : 2 • v = 0 := by
      rw [← Nat.cast_smul_eq_nsmul (ZMod 2), Nat.cast_ofNat,
        show (2 : ZMod 2) = 0 from rfl, zero_smul]
    rw [← addOrderOf_eq_prime hv2 hv]
    exact addOrderOf_dvd_natCard v
  have h0 : (0 : V) ∈ MulAction.fixedPoints S V := fun s => map_zero (ρ (incl s))
  obtain ⟨b, hb, hne⟩ := hS.exists_fixed_point_of_prime_dvd_card_of_fixed_point V h2 h0
  exact ⟨b, hne.symm, fun s => hb s⟩

@[expose] noncomputable def phiL (ρ : P →* Module.End (ZMod 2) V)
    (v : V) : PSpace →ₗ[ZMod 2] V :=
  Fintype.linearCombination (ZMod 2) fun k : Fin 4725 => ρ (repP k)⁻¹ v

theorem phiL_ev (ρ : P →* Module.End (ZMod 2) V) (v : V)
    (k : Fin 4725) : phiL ρ v (ev k) = ρ (repP k)⁻¹ v := by
  rw [ev, phiL, Fintype.linearCombination_apply_single, one_smul]

theorem rho_repP_cosetAct
    (ρ : P →* Module.End (ZMod 2) V) {v : V} (hv : ∀ s : S, ρ (incl s) v = v)
    (k : Fin 4725) (g : P) : ρ (repP (cosetAct k g))⁻¹ v = ρ g⁻¹ (ρ (repP k)⁻¹ v) := by
  have h : repP k * g = incl (factor k g) * repP (cosetAct k g) :=
    Subtype.ext (by rw [Subgroup.coe_mul, Subgroup.coe_mul, incl_coe]; exact rep_mul_eq k g)
  have h' : (repP (cosetAct k g))⁻¹ = g⁻¹ * (repP k)⁻¹ * incl (factor k g) := by
    rw [eq_inv_mul_of_mul_eq h.symm, mul_inv_rev, mul_inv_rev, inv_inv, mul_assoc]
  rw [h', map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, hv]

theorem phiL_T
    (ρ : P →* Module.End (ZMod 2) V) {v : V} (hv : ∀ s : S, ρ (incl s) v = v) (g : P)
    (f : PSpace) : phiL ρ v (T g f) = ρ g⁻¹ (phiL ρ v f) := by
  rw [phiL, Fintype.linearCombination_apply, Fintype.linearCombination_apply,
    ← Equiv.sum_comp (cosetPerm g), map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [T, LinearMap.funLeft_apply, Equiv.symm_apply_apply, map_smul]
  rw [cosetPerm_apply, rho_repP_cosetAct ρ hv]

theorem phiL_orbit
    (ρ : P →* Module.End (ZMod 2) V) {v : V}
    (hv : ∀ s : S, ρ (incl s) v = v) (hfix : ∀ u : V, ρ x0P u = u → u = 0) (a : Fin 4725) :
    phiL ρ v (ev a + ev (cosetAct a x0P) + ev (cosetAct (cosetAct a x0P) x0P)) = 0 := by
  rw [map_add, map_add, phiL_ev, phiL_ev, phiL_ev, rho_repP_cosetAct ρ hv,
    rho_repP_cosetAct ρ hv, rho_repP_cosetAct ρ hv]
  set w := ρ (repP a)⁻¹ v
  set y := ρ x0P⁻¹
  have hy3 : y (y (y w)) = w := by
    have : y * y * y = 1 := by
      rw [← map_mul, ← map_mul, ← pow_three', inv_pow, x0P_pow_three, inv_one, map_one]
    rw [← Module.End.mul_apply, ← Module.End.mul_apply, this, Module.End.one_apply]
  apply hfix
  have hyu : y (w + y w + y (y w)) = w + y w + y (y w) := by
    rw [map_add, map_add, hy3]
    abel
  calc ρ x0P (w + y w + y (y w)) = ρ x0P (y (w + y w + y (y w))) := by rw [hyu]
    _ = w + y w + y (y w) := by
      rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]

end Prop33

end CFSG.RankThree.PartTwo.J2Residue.C4725

module

public import CFSG.Sporadic.J4
public import CFSG.Sporadic.J4.QTOutNorm
public import CFSG.Sporadic.J4.QTRankProof
public import CFSG.Sporadic.HS.SmallF2Spec
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_16FactsSix
public import Certificates.Certificate7860

public section

namespace CFSG.ASVolI

open CFSG.Sporadic.J4 CFSG.Sporadic.J4.QT CFSG.Sporadic.J4.Native CFSG.J4Tree.Native
open scoped Matrix

@[expose] noncomputable def burnsideJ4NP_codeMat (a : Code) : Matrix (Fin 12) (Fin 12) (ZMod 2) :=
  CFSG.Sporadic.SmallF2.rowsMatrix 12 a.rows

@[expose] def burnsideJ4NP_CodeWF (a : Code) : Prop := a.rows.size = 12 ∧ ∀ x ∈ a.rows, x < 2 ^ 12

theorem burnsideJ4NP_code_mul_rows (a b : Code) :
    (a * b).rows = CFSG.Sporadic.SmallF2.Native.mulRows 12 a.rows b.rows := rfl

theorem burnsideJ4NP_codeMat_mul (a b : Code) :
    burnsideJ4NP_codeMat (a * b) = burnsideJ4NP_codeMat a * burnsideJ4NP_codeMat b := by
  unfold burnsideJ4NP_codeMat
  rw [burnsideJ4NP_code_mul_rows, CFSG.Sporadic.SmallF2.rowsMatrix_mulRows]

theorem burnsideJ4NP_code_one_rows :
    (1 : Code).rows = CFSG.Sporadic.SmallF2.Native.idRows 12 := by
  apply Array.ext
  · simp [CFSG.Sporadic.SmallF2.Native.idRows]
    rfl
  · intro i h1 h2
    simp only [CFSG.Sporadic.SmallF2.Native.idRows, Array.getElem_ofFn]
    have hi : i < 12 := by simpa [CFSG.Sporadic.SmallF2.Native.idRows] using h2
    interval_cases i <;> rfl

theorem burnsideJ4NP_codeMat_one : burnsideJ4NP_codeMat 1 = 1 := by
  unfold burnsideJ4NP_codeMat
  rw [burnsideJ4NP_code_one_rows, CFSG.Sporadic.SmallF2.rowsMatrix_idRows]

theorem burnsideJ4NP_codeWF_of_wf {a : Code} (h : a.wf = true) : burnsideJ4NP_CodeWF a := by
  unfold Code.wf at h
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, decide_eq_true_eq] at h
  exact ⟨h.1, fun x hx => h.2 x (Array.mem_toList_iff.2 hx)⟩

theorem burnsideJ4NP_codeWF_one : burnsideJ4NP_CodeWF 1 :=
  burnsideJ4NP_codeWF_of_wf (by decide)

theorem burnsideJ4NP_codeWF_getD {L : Array Code} (h : L.all Code.wf = true) (i : ℕ) :
    burnsideJ4NP_CodeWF (L[i]?.getD 1) := by
  rw [Array.all_eq_true] at h
  cases hi : L[i]? with
  | none => exact burnsideJ4NP_codeWF_one
  | some x =>
    obtain ⟨hlt, rfl⟩ := Array.getElem?_eq_some_iff.1 hi
    exact burnsideJ4NP_codeWF_of_wf (h i hlt)

theorem burnsideJ4NP_vecMulN_lt {R : Array ℕ} (hR : ∀ x ∈ R, x < 2 ^ 12) (v : ℕ) :
    CFSG.Sporadic.SmallF2.Native.vecMulN 12 R v < 2 ^ 12 := by
  unfold CFSG.Sporadic.SmallF2.Native.vecMulN
  have key : ∀ (l : List ℕ) (acc : ℕ), acc < 2 ^ 12 →
      l.foldl (fun acc j => if v.testBit j then acc ^^^ (R[j]?.getD 0) else acc) acc < 2 ^ 12 := by
    intro l
    induction l with
    | nil => intro acc h; exact h
    | cons j l ih =>
      intro acc h
      rw [List.foldl_cons]
      apply ih
      split_ifs
      · refine Nat.xor_lt_two_pow h ?_
        cases hj : R[j]? with
        | none => simp
        | some x => simpa using hR x (Array.mem_of_getElem? hj)
      · exact h
  exact key _ 0 (by norm_num)

theorem burnsideJ4NP_codeWF_mul {a b : Code} (ha : burnsideJ4NP_CodeWF a)
    (hb : burnsideJ4NP_CodeWF b) : burnsideJ4NP_CodeWF (a * b) := by
  rw [burnsideJ4NP_CodeWF, burnsideJ4NP_code_mul_rows]
  unfold CFSG.Sporadic.SmallF2.Native.mulRows
  refine ⟨by rw [Array.size_map]; exact ha.1, fun x hx => ?_⟩
  obtain ⟨y, -, rfl⟩ := Array.mem_map.1 hx
  exact burnsideJ4NP_vecMulN_lt hb.2 y

theorem burnsideJ4NP_codeMat_inj {a b : Code} (ha : burnsideJ4NP_CodeWF a)
    (hb : burnsideJ4NP_CodeWF b) (h : burnsideJ4NP_codeMat a = burnsideJ4NP_codeMat b) : a = b := by
  obtain ⟨ra⟩ := a
  obtain ⟨rb⟩ := b
  obtain ⟨has, hal⟩ := ha
  obtain ⟨hbs, hbl⟩ := hb
  congr 1
  refine Array.ext (by rw [has, hbs]) fun i hia hib => ?_
  have hi : i < 12 := by simpa [has] using hia
  have hrow : CFSG.Sporadic.SmallF2.toVecD 12 (ra[i]?.getD 0) =
      CFSG.Sporadic.SmallF2.toVecD 12 (rb[i]?.getD 0) := by
    funext j
    have := congrFun (congrFun h ⟨i, hi⟩) j
    simpa [burnsideJ4NP_codeMat, CFSG.Sporadic.SmallF2.rowsMatrix_apply] using this
  rw [Array.getElem?_eq_getElem hia, Array.getElem?_eq_getElem hib, Option.getD_some,
    Option.getD_some] at hrow
  exact CFSG.Sporadic.SmallF2.toVecD_injective (hal _ (Array.getElem_mem hia))
    (hbl _ (Array.getElem_mem hib)) hrow

@[expose] noncomputable def burnsideJ4NP_codeOfMat (A : Matrix (Fin 12) (Fin 12) (ZMod 2)) : Code :=
  ⟨Array.ofFn fun i : Fin 12 =>
    CFSG.Sporadic.SmallF2.Native.ofBits 12 fun j => if h : j < 12 then decide (A i ⟨j, h⟩ = 1) else false⟩

theorem burnsideJ4NP_codeWF_codeOfMat (A : Matrix (Fin 12) (Fin 12) (ZMod 2)) :
    burnsideJ4NP_CodeWF (burnsideJ4NP_codeOfMat A) := by
  refine ⟨by simp [burnsideJ4NP_codeOfMat], fun x hx => ?_⟩
  obtain ⟨i, rfl⟩ := Array.mem_ofFn.1 hx
  exact CFSG.Sporadic.SmallF2.ofBits_lt _ _

theorem burnsideJ4NP_codeMat_codeOfMat (A : Matrix (Fin 12) (Fin 12) (ZMod 2)) :
    burnsideJ4NP_codeMat (burnsideJ4NP_codeOfMat A) = A := by
  ext i j
  rw [burnsideJ4NP_codeMat, CFSG.Sporadic.SmallF2.rowsMatrix_apply, burnsideJ4NP_codeOfMat]
  simp only [Array.getElem?_ofFn, i.isLt, ↓reduceDIte, Option.getD_some]
  rw [CFSG.Sporadic.SmallF2.toVecD_ofBits]
  simp only [j.isLt, ↓reduceDIte, Fin.eta]
  have h01 : ∀ x : ZMod 2, x = 0 ∨ x = 1 := by decide
  rcases h01 (A i j) with h | h <;> simp [h]

@[expose] noncomputable def burnsideJ4NP_projMat : Matrix (Fin 112) (Fin 12) (ZMod 2) :=
  Matrix.of fun i j => CFSG.Sporadic.SmallF2.toVecD 12 (projP[i.val]?.getD 0) j

@[expose] noncomputable def burnsideJ4NP_secMat : Matrix (Fin 12) (Fin 112) (ZMod 2) :=
  Matrix.of fun r j => (secCb[r.val]?.getD V2.zero).toVec j

@[expose] noncomputable def burnsideJ4NP_rho (g : J) : Matrix (Fin 12) (Fin 12) (ZMod 2) :=
  burnsideJ4NP_secMat * Mx g * burnsideJ4NP_projMat

@[expose] def burnsideJ4NP_Compat (g : J) : Prop :=
  Mx g * burnsideJ4NP_projMat = burnsideJ4NP_projMat * burnsideJ4NP_rho g

theorem burnsideJ4NP_proj12 (v : V2) :
    CFSG.Sporadic.SmallF2.toVecD 12 (proj12 v) = v.toVec ᵥ* burnsideJ4NP_projMat := by
  unfold proj12
  rw [CFSG.Sporadic.SmallF2.foldl_xor_toVecD, CFSG.Sporadic.SmallF2.toVecD_zero, zero_add]
  funext k
  simp only [Finset.sum_apply, Matrix.vecMul, dotProduct, burnsideJ4NP_projMat, Matrix.of_apply]
  rw [← Fin.sum_univ_eq_sum_range (fun i =>
    (if v.testBit i = true then CFSG.Sporadic.SmallF2.toVecD 12 (projP[i]?.getD 0) else 0) k)]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [V2.toVec_apply]
  split_ifs <;> simp

theorem burnsideJ4NP_codeMat_rho12 (M : Array V2) :
    burnsideJ4NP_codeMat (rho12 M) = burnsideJ4NP_secMat * rowsMatrix M * burnsideJ4NP_projMat := by
  ext r k
  rw [burnsideJ4NP_codeMat, CFSG.Sporadic.SmallF2.rowsMatrix_apply, Matrix.mul_apply_eq_vecMul,
    Matrix.mul_apply_eq_vecMul]
  unfold rho12
  simp only
  rw [Array.getElem?_map]
  have hr : r.val < secCb.size := by simp [secCb]
  rw [Array.getElem?_eq_getElem hr, Option.map_some, Option.getD_some, burnsideJ4NP_proj12,
    frApply_toVec_eq_vecMul]
  congr 2
  funext j
  simp [burnsideJ4NP_secMat, Array.getElem?_eq_getElem hr]

theorem burnsideJ4NP_compatOK {M : Array V2} (h : compatOK M = true) :
    rowsMatrix M * burnsideJ4NP_projMat = burnsideJ4NP_projMat * burnsideJ4NP_codeMat (rho12 M) := by
  unfold compatOK at h
  rw [List.all_eq_true] at h
  ext i k
  rw [Matrix.mul_apply_eq_vecMul, Matrix.mul_apply_eq_vecMul]
  have hi := h i.val (List.mem_range.2 i.isLt)
  rw [beq_iff_eq] at hi
  have h1 : (rowsMatrix M i) = (M[i.val]?.getD V2.zero).toVec := by
    funext j; rfl
  have h2 : burnsideJ4NP_projMat i = CFSG.Sporadic.SmallF2.toVecD 12 (projP[i.val]?.getD 0) := by
    funext j; rfl
  rw [h1, h2, ← burnsideJ4NP_proj12, burnsideJ4NP_codeMat,
    ← CFSG.Sporadic.SmallF2.toVecD_vecMulN, hi]

theorem burnsideJ4NP_secOK (h : secOK = true) : burnsideJ4NP_secMat * burnsideJ4NP_projMat = 1 := by
  unfold secOK at h
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range] at h
  ext r k
  rw [Matrix.mul_apply_eq_vecMul]
  have hr := h.2 r.val r.isLt
  have e : burnsideJ4NP_secMat r = (secCb[r.val]?.getD V2.zero).toVec := by funext j; rfl
  rw [e, ← burnsideJ4NP_proj12, hr, CFSG.Sporadic.SmallF2.toVecD_apply, Matrix.one_apply,
    Nat.one_shiftLeft, Nat.testBit_two_pow]
  by_cases hrk : r = k
  · subst hrk; simp
  · have : r.val ≠ k.val := fun e => hrk (Fin.ext e)
    simp [hrk, this]

section Cert

theorem burnsideJ4NP_affChecks_parts :
    secOK = true ∧ locCodesOK (locMats ()) (locInvs ()) = true ∧ eFaithOK = true ∧
      etaInEOK = true ∧ tauOK = true ∧ shapeOK = true ∧ literalsOK = true := by
  have h := (Certificates.certificate7860).1
  unfold affChecks at h
  simp only [Bool.and_eq_true] at h
  exact ⟨h.1.1.1.1.1.1, h.1.1.1.1.1.2, h.1.1.1.1.2, h.1.1.1.2, h.1.1.2, h.1.2, h.2⟩

theorem burnsideJ4NP_literals :
    xCode.all Code.wf = true ∧ xiCode.all Code.wf = true ∧ uCode.all Code.wf = true ∧
      kCode.all Code.wf = true ∧ tauInvTab.all (· < 2048) = true := by
  have h := burnsideJ4NP_affChecks_parts.2.2.2.2.2.2
  unfold literalsOK at h
  simp only [Bool.and_eq_true] at h
  exact ⟨h.1.1.1.1, h.1.1.1.2, h.1.1.2, h.1.2, h.2⟩

theorem burnsideJ4NP_secMat_projMat : burnsideJ4NP_secMat * burnsideJ4NP_projMat = 1 :=
  burnsideJ4NP_secOK burnsideJ4NP_affChecks_parts.1

theorem burnsideJ4NP_locCodes {k : ℕ} (hk : k < 3) :
    compatOK ((locMats ())[k]?.getD (idRows ())) = true ∧
      rho12 ((locMats ())[k]?.getD (idRows ())) = xCode[k]?.getD 1 ∧
      rho12 ((locInvs ())[k]?.getD (idRows ())) = xiCode[k]?.getD 1 := by
  have h := burnsideJ4NP_affChecks_parts.2.1
  unfold locCodesOK at h
  simp only [Bool.and_eq_true, List.all_eq_true, List.mem_range, beq_iff_eq] at h
  exact ⟨(h k hk).1.1, (h k hk).1.2, (h k hk).2⟩

theorem burnsideJ4NP_uCode_eq {j : ℕ} (hj : j < 11) : codeOfWord (uWord j) = uCode[j]?.getD 1 := by
  have h := (Certificates.certificate7860).2
  unfold burnsideJ4NP_affDataOK at h
  simp only [Bool.and_eq_true, List.all_eq_true, List.mem_range, beq_iff_eq] at h
  exact h.1 j hj

theorem burnsideJ4NP_kCode_eq {i : ℕ} (hi : i < 4) :
    codeOfWord (kWords.getD i []) = kCode[i]?.getD 1 := by
  have h := (Certificates.certificate7860).2
  unfold burnsideJ4NP_affDataOK at h
  simp only [Bool.and_eq_true, List.all_eq_true, List.mem_range, beq_iff_eq] at h
  exact h.2 i hi

theorem burnsideJ4NP_codeWF_letterCode (ℓ : ℤ) : burnsideJ4NP_CodeWF (letterCode ℓ) := by
  unfold letterCode
  split_ifs
  · exact burnsideJ4NP_codeWF_getD burnsideJ4NP_literals.1 _
  · exact burnsideJ4NP_codeWF_getD burnsideJ4NP_literals.2.1 _

theorem burnsideJ4NP_codeWF_codeOfWord (w : List ℤ) : burnsideJ4NP_CodeWF (codeOfWord w) := by
  unfold codeOfWord
  have key : ∀ (l : List ℤ) (A : Code), burnsideJ4NP_CodeWF A →
      burnsideJ4NP_CodeWF (l.foldl (fun acc ℓ => acc * letterCode ℓ) A) := by
    intro l
    induction l with
    | nil => intro A hA; exact hA
    | cons ℓ l ih =>
      intro A hA
      rw [List.foldl_cons]
      exact ih _ (burnsideJ4NP_codeWF_mul hA (burnsideJ4NP_codeWF_letterCode ℓ))
  exact key w 1 burnsideJ4NP_codeWF_one

theorem burnsideJ4NP_codeWF_etaCode (c : ℕ) : burnsideJ4NP_CodeWF (etaCode c) := by
  unfold etaCode
  have key : ∀ (l : List ℕ) (A : Code), burnsideJ4NP_CodeWF A →
      burnsideJ4NP_CodeWF (l.foldl
        (fun acc j => if c.testBit j then acc * (uCode[j]?.getD 1) else acc) A) := by
    intro l
    induction l with
    | nil => intro A hA; exact hA
    | cons j l ih =>
      intro A hA
      rw [List.foldl_cons]
      apply ih
      split_ifs
      · exact burnsideJ4NP_codeWF_mul hA (burnsideJ4NP_codeWF_getD burnsideJ4NP_literals.2.2.1 j)
      · exact hA
  exact key _ 1 burnsideJ4NP_codeWF_one

theorem burnsideJ4NP_codeWF_kelCode (e : ℕ) : burnsideJ4NP_CodeWF (kelCode e) := by
  unfold kelCode
  have key : ∀ (l : List ℕ) (A : Code), burnsideJ4NP_CodeWF A →
      burnsideJ4NP_CodeWF (l.foldl (fun acc i => acc * (kCode[i]?.getD 1)) A) := by
    intro l
    induction l with
    | nil => intro A hA; exact hA
    | cons i l ih =>
      intro A hA
      rw [List.foldl_cons]
      exact ih _ (burnsideJ4NP_codeWF_mul hA (burnsideJ4NP_codeWF_getD burnsideJ4NP_literals.2.2.2.1 i))
  exact key _ 1 burnsideJ4NP_codeWF_one

theorem burnsideJ4NP_codeWF_codeOfCoord (c e : ℕ) : burnsideJ4NP_CodeWF (codeOfCoord c e) :=
  burnsideJ4NP_codeWF_mul (burnsideJ4NP_codeWF_etaCode c) (burnsideJ4NP_codeWF_kelCode e)

end Cert

theorem burnsideJ4NP_rho_mul_of_compat {g h : J} (hh : burnsideJ4NP_Compat h) :
    burnsideJ4NP_rho (g * h) = burnsideJ4NP_rho g * burnsideJ4NP_rho h := by
  unfold burnsideJ4NP_rho
  rw [map_mul]
  calc burnsideJ4NP_secMat * (Mx g * Mx h) * burnsideJ4NP_projMat
      = burnsideJ4NP_secMat * Mx g * (Mx h * burnsideJ4NP_projMat) := by
        simp only [Matrix.mul_assoc]
    _ = burnsideJ4NP_secMat * Mx g * (burnsideJ4NP_projMat * burnsideJ4NP_rho h) := by rw [hh]
    _ = burnsideJ4NP_secMat * Mx g * burnsideJ4NP_projMat * burnsideJ4NP_rho h := by
        simp only [Matrix.mul_assoc]

theorem burnsideJ4NP_compat_mul {g h : J} (hg : burnsideJ4NP_Compat g)
    (hh : burnsideJ4NP_Compat h) : burnsideJ4NP_Compat (g * h) := by
  unfold burnsideJ4NP_Compat
  rw [burnsideJ4NP_rho_mul_of_compat hh, map_mul, Matrix.mul_assoc, hh, ← Matrix.mul_assoc, hg,
    Matrix.mul_assoc]

theorem burnsideJ4NP_col0_of_affShape {a : Code} (h : a.affShape = true) (i : Fin 12) :
    burnsideJ4NP_codeMat a i 0 = if i = 0 then 1 else 0 := by
  unfold Code.affShape at h
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range] at h
  obtain ⟨⟨-, h0⟩, hi⟩ := h
  rw [burnsideJ4NP_codeMat, CFSG.Sporadic.SmallF2.rowsMatrix_apply,
    CFSG.Sporadic.SmallF2.toVecD_apply, Fin.val_zero, Nat.testBit_zero]
  by_cases hi0 : i = 0
  · subst hi0
    simp [h0]
  · obtain ⟨k, hk⟩ : ∃ k, i.val = k + 1 := ⟨i.val - 1, by have := Fin.val_ne_of_ne hi0; simp at this; omega⟩
    have hk11 : k < 11 := by have := i.isLt; omega
    have := hi k hk11
    rw [hk]
    simp [hi0, this]

@[expose] noncomputable def burnsideJ4NP_enc (g : ↥Hj) : Code :=
  burnsideJ4NP_codeOfMat (burnsideJ4NP_rho g)

theorem burnsideJ4NP_codeMat_enc (g : ↥Hj) :
    burnsideJ4NP_codeMat (burnsideJ4NP_enc g) = burnsideJ4NP_rho g :=
  burnsideJ4NP_codeMat_codeOfMat _

theorem burnsideJ4NP_codeWF_enc (g : ↥Hj) : burnsideJ4NP_CodeWF (burnsideJ4NP_enc g) :=
  burnsideJ4NP_codeWF_codeOfMat _

theorem burnsideJ4NP_enc_eq_iff {g : ↥Hj} {a : Code} (ha : burnsideJ4NP_CodeWF a) :
    burnsideJ4NP_enc g = a ↔ burnsideJ4NP_rho g = burnsideJ4NP_codeMat a := by
  constructor
  · rintro rfl
    exact (burnsideJ4NP_codeMat_enc g).symm
  · intro h
    exact burnsideJ4NP_codeMat_inj (burnsideJ4NP_codeWF_enc g) ha
      (by rw [burnsideJ4NP_codeMat_enc, h])

theorem burnsideJ4NP_pcSeqT_eq (e : ℕ) : pcSeqT e = pcSeq e := rfl

section H

theorem burnsideJ4NP_rho_one : burnsideJ4NP_rho 1 = 1 := by
  unfold burnsideJ4NP_rho
  rw [map_one, Matrix.mul_one, burnsideJ4NP_secMat_projMat]

theorem burnsideJ4NP_compat_one : burnsideJ4NP_Compat 1 := by
  unfold burnsideJ4NP_Compat
  rw [burnsideJ4NP_rho_one, map_one, Matrix.one_mul, Matrix.mul_one]

theorem burnsideJ4NP_Mx_xJ (k : ℕ) :
    Mx (xJ k) = rowsMatrix ((locMats ())[k]?.getD (idRows ())) := by
  rw [Mx_apply, locMats_spec j4Facts.mat]
  rfl

theorem burnsideJ4NP_rho_xJ (k : ℕ) :
    burnsideJ4NP_rho (xJ k) = burnsideJ4NP_codeMat (rho12 ((locMats ())[k]?.getD (idRows ()))) := by
  rw [burnsideJ4NP_codeMat_rho12, burnsideJ4NP_rho, burnsideJ4NP_Mx_xJ]

theorem burnsideJ4NP_compat_xJ {k : ℕ} (hk : k < 3) : burnsideJ4NP_Compat (xJ k) := by
  unfold burnsideJ4NP_Compat
  rw [burnsideJ4NP_rho_xJ, burnsideJ4NP_Mx_xJ]
  exact burnsideJ4NP_compatOK (burnsideJ4NP_locCodes hk).1

theorem burnsideJ4NP_compat_of_mem {g : J} (hg : g ∈ Hj) : burnsideJ4NP_Compat g := by
  have hcl : g ∈ Submonoid.closure ({xJ 0, xJ 1, xJ 2} : Set J) := by
    rw [← Subgroup.closure_toSubmonoid_of_finite]
    exact hg
  clear hg
  induction hcl using Submonoid.closure_induction with
  | mem x hx =>
    rcases hx with rfl | rfl | rfl
    · exact burnsideJ4NP_compat_xJ (by norm_num)
    · exact burnsideJ4NP_compat_xJ (by norm_num)
    · exact burnsideJ4NP_compat_xJ (by norm_num)
  | one => exact burnsideJ4NP_compat_one
  | mul x y _ _ hx hy => exact burnsideJ4NP_compat_mul hx hy

theorem burnsideJ4NP_rho_mul {g h : J} (hh : h ∈ Hj) :
    burnsideJ4NP_rho (g * h) = burnsideJ4NP_rho g * burnsideJ4NP_rho h :=
  burnsideJ4NP_rho_mul_of_compat (burnsideJ4NP_compat_of_mem hh)

theorem burnsideJ4NP_rho_inv_mul {g : J} (hg : g ∈ Hj) :
    burnsideJ4NP_rho g⁻¹ * burnsideJ4NP_rho g = 1 := by
  rw [← burnsideJ4NP_rho_mul hg, inv_mul_cancel, burnsideJ4NP_rho_one]

theorem burnsideJ4NP_rho_mul_inv {g : J} (hg : g ∈ Hj) :
    burnsideJ4NP_rho g * burnsideJ4NP_rho g⁻¹ = 1 := by
  rw [← burnsideJ4NP_rho_mul (Hj.inv_mem hg), mul_inv_cancel, burnsideJ4NP_rho_one]

theorem burnsideJ4NP_rho_col0 {g : J} (hg : g ∈ Hj) (i : Fin 12) :
    burnsideJ4NP_rho g i 0 = if i = 0 then 1 else 0 := by
  have hcl : g ∈ Submonoid.closure ({xJ 0, xJ 1, xJ 2} : Set J) := by
    rw [← Subgroup.closure_toSubmonoid_of_finite]
    exact hg
  clear hg
  revert i
  suffices h : g ∈ Hj ∧ ∀ i : Fin 12, burnsideJ4NP_rho g i 0 = if i = 0 then 1 else 0 from h.2
  induction hcl using Submonoid.closure_induction with
  | mem x hx =>
    have hshape : ∀ k < 3, (xCode[k]?.getD 1).affShape = true := by
      have h := burnsideJ4NP_affChecks_parts.2.2.2.2.2.1
      unfold shapeOK at h
      simp only [Bool.and_eq_true, Array.all_eq_true] at h
      intro k hk
      have hk' : k < xCode.size := by simp [xCode]; omega
      rw [Array.getElem?_eq_getElem hk', Option.getD_some]
      exact h.1 k hk'
    have key : ∀ k < 3, ∀ i : Fin 12, burnsideJ4NP_rho (xJ k) i 0 = if i = 0 then 1 else 0 := by
      intro k hk i
      rw [burnsideJ4NP_rho_xJ, (burnsideJ4NP_locCodes hk).2.1]
      exact burnsideJ4NP_col0_of_affShape (hshape k hk) i
    rcases hx with rfl | rfl | rfl
    · exact ⟨xJ_mem (by norm_num), key 0 (by norm_num)⟩
    · exact ⟨xJ_mem (by norm_num), key 1 (by norm_num)⟩
    · exact ⟨xJ_mem (by norm_num), key 2 (by norm_num)⟩
  | one =>
    refine ⟨Hj.one_mem, fun i => ?_⟩
    simp [burnsideJ4NP_rho_one, Matrix.one_apply]
  | mul x y _ _ hx hy =>
    refine ⟨Hj.mul_mem hx.1 hy.1, fun i => ?_⟩
    rw [burnsideJ4NP_rho_mul hy.1, Matrix.mul_apply]
    simp only [hy.2, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    exact hx.2 i

theorem burnsideJ4NP_rho_XJ {ℓ : ℤ} (hℓ : ℓ ∈ letters) :
    burnsideJ4NP_rho (XJ ℓ) = burnsideJ4NP_codeMat (letterCode ℓ) := by
  have hM := j4Facts.mat
  have hx : burnsideJ4NP_rho (XJ ℓ) =
      burnsideJ4NP_codeMat (rho12 (xRows (locMats ()) (locInvs ()) ℓ)) := by
    rw [burnsideJ4NP_codeMat_rho12, burnsideJ4NP_rho, Mx_XJ hM]
  rw [hx]
  congr 1
  rcases letters_cases hℓ with rfl | rfl | rfl | rfl | rfl | rfl
  · exact (burnsideJ4NP_locCodes (k := 0) (by norm_num)).2.1
  · exact (burnsideJ4NP_locCodes (k := 1) (by norm_num)).2.1
  · exact (burnsideJ4NP_locCodes (k := 2) (by norm_num)).2.1
  · exact (burnsideJ4NP_locCodes (k := 0) (by norm_num)).2.2
  · exact (burnsideJ4NP_locCodes (k := 1) (by norm_num)).2.2
  · exact (burnsideJ4NP_locCodes (k := 2) (by norm_num)).2.2

theorem burnsideJ4NP_rho_fold_word : ∀ (w : List ℤ), (∀ ℓ ∈ w, ℓ ∈ letters) →
    ∀ (a : J) (A : Code), a ∈ Hj → burnsideJ4NP_rho a = burnsideJ4NP_codeMat A →
      burnsideJ4NP_rho (a * (w.map XJ).prod) =
        burnsideJ4NP_codeMat (w.foldl (fun acc ℓ => acc * letterCode ℓ) A)
  | [], _, a, A, _, h => by simpa using h
  | ℓ :: w, hw, a, A, ha, h => by
    have hℓ : ℓ ∈ letters := hw ℓ (List.mem_cons_self ..)
    have hw' : ∀ ℓ' ∈ w, ℓ' ∈ letters := fun ℓ' h' => hw ℓ' (List.mem_cons_of_mem _ h')
    rw [List.map_cons, List.prod_cons, List.foldl_cons, ← mul_assoc]
    refine burnsideJ4NP_rho_fold_word w hw' _ _ (Hj.mul_mem ha (XJ_mem hℓ)) ?_
    rw [burnsideJ4NP_rho_mul (XJ_mem hℓ), h, burnsideJ4NP_rho_XJ hℓ, burnsideJ4NP_codeMat_mul]

theorem burnsideJ4NP_rho_wordProd {w : List ℤ} (hw : ∀ ℓ ∈ w, ℓ ∈ letters) :
    burnsideJ4NP_rho (wordProd xJ w) = burnsideJ4NP_codeMat (codeOfWord w) := by
  have := burnsideJ4NP_rho_fold_word w hw 1 1 Hj.one_mem
    (by rw [burnsideJ4NP_rho_one, burnsideJ4NP_codeMat_one])
  rwa [one_mul, ← wordProd_xJ] at this

theorem burnsideJ4NP_rho_uJ {j : ℕ} (hj : j < 11) :
    burnsideJ4NP_rho (uJ j) = burnsideJ4NP_codeMat (uCode[j]?.getD 1) := by
  rw [uJ, burnsideJ4NP_rho_wordProd (uWord_letters.1 j hj), burnsideJ4NP_uCode_eq hj]

theorem burnsideJ4NP_rho_fold_eta (c : ℕ) : ∀ (l : List ℕ), (∀ j ∈ l, j < 11) → ∀ (a : J) (A : Code),
    a ∈ Hj → burnsideJ4NP_rho a = burnsideJ4NP_codeMat A →
    burnsideJ4NP_rho (l.foldl (fun acc j => if c.testBit j then acc * uJ j else acc) a) =
      burnsideJ4NP_codeMat (l.foldl
        (fun acc j => if c.testBit j then acc * (uCode[j]?.getD 1) else acc) A)
  | [], _, _, _, _, h => h
  | j :: l, hl, a, A, ha, h => by
    have hj : j < 11 := hl j (List.mem_cons_self ..)
    have hl' : ∀ j' ∈ l, j' < 11 := fun j' hj' => hl j' (List.mem_cons_of_mem _ hj')
    rw [List.foldl_cons, List.foldl_cons]
    by_cases hb : c.testBit j = true
    · simp only [hb, ite_true]
      refine burnsideJ4NP_rho_fold_eta c l hl' _ _ (Hj.mul_mem ha (uJ_mem hj)) ?_
      rw [burnsideJ4NP_rho_mul (uJ_mem hj), h, burnsideJ4NP_rho_uJ hj, burnsideJ4NP_codeMat_mul]
    · simp only [hb, Bool.false_eq_true, ite_false]
      exact burnsideJ4NP_rho_fold_eta c l hl' a A ha h

theorem burnsideJ4NP_rho_eta (c : ℕ) :
    burnsideJ4NP_rho (eta uJ 11 c) = burnsideJ4NP_codeMat (etaCode c) := by
  unfold eta etaCode
  exact burnsideJ4NP_rho_fold_eta c (List.range 11) (fun j hj => List.mem_range.1 hj) 1 _
    Hj.one_mem (by rw [burnsideJ4NP_rho_one, burnsideJ4NP_codeMat_one])

theorem burnsideJ4NP_rho_eta_ne_one {c : ℕ} (hc0 : 0 < c) (hc : c < 2 ^ 11) :
    burnsideJ4NP_rho (eta uJ 11 c) ≠ 1 := by
  have h := burnsideJ4NP_affChecks_parts.2.2.1
  unfold eFaithOK at h
  simp only [List.all_eq_true, List.mem_range, bne_iff_ne, ne_eq] at h
  have hne := h (c - 1) (by omega)
  rw [show c - 1 + 1 = c by omega] at hne
  intro h1
  rw [burnsideJ4NP_rho_eta, ← burnsideJ4NP_codeMat_one] at h1
  have e := burnsideJ4NP_codeMat_inj (burnsideJ4NP_codeWF_etaCode c) burnsideJ4NP_codeWF_one h1
  rw [e] at hne
  exact hne rfl

theorem burnsideJ4NP_comm_E_of_rho_eq_one {g : J} (hg : g ∈ Hj) (h1 : burnsideJ4NP_rho g = 1) :
    ∀ y ∈ Eg uJ 11, g * y = y * g := by
  intro y hy
  have hN : g ∈ Subgroup.normalizer (Eg uJ 11 : Set J) := by
    rw [normalizer_Eg_eq_Hj j4Facts]; exact hg
  have hyH : y ∈ Hj := Eg_le_Hj hy
  have hgy : g * y * g⁻¹ ∈ Eg uJ 11 := (Subgroup.mem_normalizer_iff.mp hN y).mp hy
  set x := g * y * g⁻¹ * y⁻¹ with hx
  have hxE : x ∈ Eg uJ 11 := (Eg uJ 11).mul_mem hgy ((Eg uJ 11).inv_mem hy)
  have hginv : burnsideJ4NP_rho g⁻¹ = 1 := by
    have := burnsideJ4NP_rho_inv_mul hg
    rwa [h1, Matrix.mul_one] at this
  have hrx : burnsideJ4NP_rho x = 1 := by
    rw [hx, burnsideJ4NP_rho_mul (Hj.inv_mem hyH), burnsideJ4NP_rho_mul (Hj.inv_mem hg),
      burnsideJ4NP_rho_mul hyH, h1, hginv, Matrix.one_mul, Matrix.mul_one,
      burnsideJ4NP_rho_mul_inv hyH]
  obtain ⟨m, hm, hxm⟩ := (mem_Eg_iff (elem_uJ j4Facts.mat)).1 hxE
  have hm0 : m = 0 := by
    by_contra hne
    exact burnsideJ4NP_rho_eta_ne_one (Nat.pos_of_ne_zero hne) hm (hxm ▸ hrx)
  rw [hm0, eta_zero] at hxm
  have : g * y * g⁻¹ = y := by
    have := congrArg (· * y) hxm
    simpa [hx, mul_assoc] using this
  calc g * y = g * y * g⁻¹ * g := by group
    _ = y * g := by rw [this]

theorem burnsideJ4NP_eq_one_of_rho_eq_one {g : J} (hg : g ∈ Hj) (h1 : burnsideJ4NP_rho g = 1) :
    g = 1 := by
  have hgE : g ∈ Eg uJ 11 :=
    centralizer_Hj j4Facts.mat j4Facts g hg (burnsideJ4NP_comm_E_of_rho_eq_one hg h1)
  obtain ⟨m, hm, rfl⟩ := (mem_Eg_iff (elem_uJ j4Facts.mat)).1 hgE
  have hm0 : m = 0 := by
    by_contra hne
    exact burnsideJ4NP_rho_eta_ne_one (Nat.pos_of_ne_zero hne) hm h1
  rw [hm0, eta_zero]

theorem burnsideJ4NP_rho_injOn {g h : J} (hg : g ∈ Hj) (hh : h ∈ Hj)
    (e : burnsideJ4NP_rho g = burnsideJ4NP_rho h) : g = h := by
  have : burnsideJ4NP_rho (g * h⁻¹) = 1 := by
    rw [burnsideJ4NP_rho_mul (Hj.inv_mem hh), e, burnsideJ4NP_rho_mul_inv hh]
  have := burnsideJ4NP_eq_one_of_rho_eq_one (Hj.mul_mem hg (Hj.inv_mem hh)) this
  rwa [mul_inv_eq_one] at this

theorem burnsideJ4NP_enc_isEnc : CFSG.QuasithinUnique.Unc25K1.Six.IsEnc burnsideJ4NP_enc where
  inj g h e := by
    have := congrArg burnsideJ4NP_codeMat e
    rw [burnsideJ4NP_codeMat_enc, burnsideJ4NP_codeMat_enc] at this
    exact Subtype.ext (burnsideJ4NP_rho_injOn g.2 h.2 this)
  map_mul g h := by
    refine (burnsideJ4NP_enc_eq_iff (burnsideJ4NP_codeWF_mul (burnsideJ4NP_codeWF_enc g)
      (burnsideJ4NP_codeWF_enc h))).2 ?_
    rw [burnsideJ4NP_codeMat_mul, burnsideJ4NP_codeMat_enc, burnsideJ4NP_codeMat_enc]
    exact burnsideJ4NP_rho_mul h.2
  map_one := by
    refine (burnsideJ4NP_enc_eq_iff burnsideJ4NP_codeWF_one).2 ?_
    rw [burnsideJ4NP_codeMat_one]
    exact burnsideJ4NP_rho_one

theorem burnsideJ4NP_enc_wordProd {w : List ℤ} (hw : ∀ ℓ ∈ w, ℓ ∈ letters) :
    burnsideJ4NP_enc ⟨wordProd xJ w, wordProd_mem_Hj hw⟩ = codeOfWord w :=
  (burnsideJ4NP_enc_eq_iff (burnsideJ4NP_codeWF_codeOfWord w)).2 (burnsideJ4NP_rho_wordProd hw)

theorem burnsideJ4NP_enc_eta (c : ℕ) :
    burnsideJ4NP_enc ⟨eta uJ 11 c, Eg_le_Hj (eta_mem_Eg 11 le_rfl c)⟩ = etaCode c :=
  (burnsideJ4NP_enc_eq_iff (burnsideJ4NP_codeWF_etaCode c)).2 (burnsideJ4NP_rho_eta c)

theorem burnsideJ4NP_mem_Eg_iff {g : J} (hg : g ∈ Hj) :
    g ∈ Eg uJ 11 ↔ (burnsideJ4NP_enc ⟨g, hg⟩).inE = true := by
  have hE := burnsideJ4NP_affChecks_parts.2.2.2.1
  have hT := burnsideJ4NP_affChecks_parts.2.2.2.2.1
  unfold etaInEOK at hE
  unfold tauOK at hT
  simp only [List.all_eq_true, List.mem_range] at hE
  simp only [List.all_eq_true, List.mem_range, beq_iff_eq] at hT
  constructor
  · intro hgE
    obtain ⟨m, hm, rfl⟩ := (mem_Eg_iff (elem_uJ j4Facts.mat)).1 hgE
    rw [burnsideJ4NP_enc_eta m]
    exact hE m hm
  · intro hin
    set a := burnsideJ4NP_enc ⟨g, hg⟩ with ha
    have hca : burnsideJ4NP_codeMat a = burnsideJ4NP_rho g := burnsideJ4NP_codeMat_enc ⟨g, hg⟩
    have hwf : burnsideJ4NP_CodeWF a := burnsideJ4NP_codeWF_enc _
    have hs : 0 < a.rows.size := by rw [hwf.1]; norm_num
    have hr0lt : a.rows[0]?.getD 0 < 2 ^ 12 := by
      rw [Array.getElem?_eq_getElem hs, Option.getD_some]
      exact hwf.2 _ (Array.getElem_mem hs)
    have hodd : (a.rows[0]?.getD 0) % 2 = 1 := by
      have h00 := burnsideJ4NP_rho_col0 hg 0
      rw [if_pos rfl, ← hca, burnsideJ4NP_codeMat, CFSG.Sporadic.SmallF2.rowsMatrix_apply,
        CFSG.Sporadic.SmallF2.toVecD_apply, Fin.val_zero] at h00
      by_contra hc
      have h0 : (a.rows[0]?.getD 0).testBit 0 = false := by
        rw [Nat.testBit_zero]
        simpa using hc
      rw [h0] at h00
      simp at h00
    set t := a.rows[0]?.getD 0 >>> 1 with ht
    have htlt : t < 2048 := by
      rw [ht, Nat.shiftRight_eq_div_pow]
      omega
    have hrow0 : a.rows[0]?.getD 0 = 1 + 2 * t := by
      rw [ht, Nat.shiftRight_eq_div_pow]
      omega
    have hclt : tauInv t < 2048 := by
      unfold tauInv
      have hTab := burnsideJ4NP_literals.2.2.2.2
      rw [Array.all_eq_true] at hTab
      have key : ∀ (l : List ℕ) (acc : ℕ), acc < 2 ^ 11 →
          l.foldl (fun acc i => if t.testBit i then acc ^^^ (tauInvTab[i]?.getD 0) else acc) acc
            < 2 ^ 11 := by
        intro l
        induction l with
        | nil => intro acc h; exact h
        | cons i l ih =>
          intro acc h
          rw [List.foldl_cons]
          apply ih
          split_ifs
          · refine Nat.xor_lt_two_pow h ?_
            cases hi : tauInvTab[i]? with
            | none => simp
            | some x =>
              obtain ⟨hlt, rfl⟩ := Array.getElem?_eq_some_iff.1 hi
              simpa using hTab i hlt
          · exact h
      exact key _ 0 (by norm_num)
    have heq : etaCode (tauInv t) = a := by
      have hwf' := burnsideJ4NP_codeWF_etaCode (tauInv t)
      have hin' := hE (tauInv t) hclt
      have hT' := hT t htlt
      unfold Code.inE at hin hin'
      simp only [List.all_eq_true, List.mem_range, beq_iff_eq] at hin hin'
      have hrows : (etaCode (tauInv t)).rows = a.rows := by
        refine Array.ext (by rw [hwf'.1, hwf.1]) fun i h1 h2 => ?_
        have hi12 : i < 12 := by rw [hwf'.1] at h1; exact h1
        have key : (etaCode (tauInv t)).rows[i]?.getD 0 = a.rows[i]?.getD 0 := by
          rcases Nat.eq_zero_or_pos i with rfl | hpos
          · rw [hT', hrow0]
          · obtain ⟨k, rfl⟩ : ∃ k, i = k + 1 := ⟨i - 1, by omega⟩
            rw [hin' k (by omega), hin k (by omega)]
        rwa [Array.getElem?_eq_getElem h1, Array.getElem?_eq_getElem h2, Option.getD_some,
          Option.getD_some] at key
      calc etaCode (tauInv t) = ⟨(etaCode (tauInv t)).rows⟩ := rfl
        _ = ⟨a.rows⟩ := by rw [hrows]
        _ = a := rfl
    have hrho : burnsideJ4NP_rho g = burnsideJ4NP_rho (eta uJ 11 (tauInv t)) := by
      rw [burnsideJ4NP_rho_eta, heq, hca]
    rw [burnsideJ4NP_rho_injOn hg (Eg_le_Hj (eta_mem_Eg 11 le_rfl _)) hrho]
    exact eta_mem_Eg 11 le_rfl _

theorem burnsideJ4NP_rho_kJ {i : ℕ} (hi : i < 4) :
    burnsideJ4NP_rho (kJ i) = burnsideJ4NP_codeMat (kCode[i]?.getD 1) := by
  rw [kJ, burnsideJ4NP_rho_wordProd (kJ_letters hi), burnsideJ4NP_kCode_eq hi]

theorem burnsideJ4NP_rho_fold_Kel : ∀ (l : List ℕ), (∀ i ∈ l, i < 4) → ∀ (a : J) (A : Code),
    a ∈ Hj → burnsideJ4NP_rho a = burnsideJ4NP_codeMat A →
    burnsideJ4NP_rho (a * (l.map kJ).prod) =
      burnsideJ4NP_codeMat (l.foldl (fun acc i => acc * (kCode[i]?.getD 1)) A)
  | [], _, a, A, _, h => by simpa using h
  | i :: l, hl, a, A, ha, h => by
    have hi : i < 4 := hl i (List.mem_cons_self ..)
    have hl' : ∀ i' ∈ l, i' < 4 := fun i' hi' => hl i' (List.mem_cons_of_mem _ hi')
    rw [List.map_cons, List.prod_cons, List.foldl_cons, ← mul_assoc]
    refine burnsideJ4NP_rho_fold_Kel l hl' _ _ (Hj.mul_mem ha (kJ_mem hi)) ?_
    rw [burnsideJ4NP_rho_mul (kJ_mem hi), h, burnsideJ4NP_rho_kJ hi, burnsideJ4NP_codeMat_mul]

theorem burnsideJ4NP_rho_Kel {e : ℕ} (he : e < 1024) :
    burnsideJ4NP_rho (Kel e) = burnsideJ4NP_codeMat (kelCode e) := by
  have := burnsideJ4NP_rho_fold_Kel (pcSeq e) (pcSeq_lt e he) 1 1 Hj.one_mem
    (by rw [burnsideJ4NP_rho_one, burnsideJ4NP_codeMat_one])
  rw [one_mul] at this
  rw [Kel, this, kelCode, burnsideJ4NP_pcSeqT_eq]

theorem burnsideJ4NP_rho_eta_mul_Kel (c : ℕ) {e : ℕ} (he : e < 1024) :
    burnsideJ4NP_rho (eta uJ 11 c * Kel e) = burnsideJ4NP_codeMat (codeOfCoord c e) := by
  rw [burnsideJ4NP_rho_mul (Kel_mem_Hj he), burnsideJ4NP_rho_eta, burnsideJ4NP_rho_Kel he,
    codeOfCoord, burnsideJ4NP_codeMat_mul]

theorem burnsideJ4NP_enc_eta_mul_Kel (c : ℕ) {e : ℕ} (he : e < 1024) :
    burnsideJ4NP_enc ⟨eta uJ 11 c * Kel e, P0_le_Hj (eta_mul_Kel_mem he)⟩ = codeOfCoord c e :=
  (burnsideJ4NP_enc_eq_iff (burnsideJ4NP_codeWF_codeOfCoord c e)).2
    (burnsideJ4NP_rho_eta_mul_Kel c he)

end H

end CFSG.ASVolI

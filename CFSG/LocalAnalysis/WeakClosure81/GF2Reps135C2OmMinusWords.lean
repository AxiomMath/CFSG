module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2OmMinusBits
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2OmMinusMinorTri
public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog516CSpin

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.LieType.Universal.Spin CFSG.LieType.Universal.Spin.Twisted

variable {K : Type*} [Field K]

open Classical in
@[expose] noncomputable def o8mPairElt (u v : ℕ) : spinGroup (quadMinus 4 K 1 1) :=
  if h : quadMinus 4 K 1 1 (o8mVec u) * quadMinus 4 K 1 1 (o8mVec v) = 1 then
    CFSG.ComponentClassification.GSThmB.Cent516.pairElt (o8mVec u) (o8mVec v) h
  else 1

@[expose] noncomputable def o8mWordElt : List ℕ → spinGroup (quadMinus 4 K 1 1)
  | u :: v :: w => o8mPairElt u v * o8mWordElt w
  | _ => 1

variable [CharP K 2]

private theorem o8mWO_det_fin_two :
    ∀ b : Fin 2 → Fin 2 → Bool,
      (Matrix.of fun r c => if b r c then (1 : ZMod 2) else 0).det =
        if (b 0 0 && b 1 1) ^^ (b 0 1 && b 1 0) then 1 else 0 := by
  simp only [Matrix.det_fin_two]
  decide +kernel

private theorem o8mWO_det_fin_three :
    ∀ b : Fin 3 → Fin 3 → Bool,
      (Matrix.of fun r c => if b r c then (1 : ZMod 2) else 0).det =
        if (b 0 0 && ((b 1 1 && b 2 2) ^^ (b 1 2 && b 2 1))) ^^
           (b 0 1 && ((b 1 0 && b 2 2) ^^ (b 1 2 && b 2 0))) ^^
           (b 0 2 && ((b 1 0 && b 2 1) ^^ (b 1 1 && b 2 0))) then 1 else 0 := by
  simp only [Matrix.det_fin_three]
  decide +kernel

private theorem o8mWO_det_zmod (col : ℕ → ℕ) (i : Fin 3) :
    (Matrix.of fun r c : Fin (i + 1) =>
      if (col (c : ℕ)).testBit (2 * (r : ℕ)) then (1 : ZMod 2) else 0).det =
      if o8mDeltaBit col i then 1 else 0 := by
  fin_cases i
  · simp [o8mDeltaBit]
  · simpa [o8mDeltaBit] using
      o8mWO_det_fin_two (fun r c : Fin 2 => (col (c : ℕ)).testBit (2 * (r : ℕ)))
  · simpa [o8mDeltaBit] using
      o8mWO_det_fin_three (fun r c : Fin 3 => (col (c : ℕ)).testBit (2 * (r : ℕ)))

private theorem o8mWO_det_eq (col : ℕ → ℕ) (i : Fin 3) :
    (Matrix.of fun r c : Fin (i + 1) =>
      if (col (c : ℕ)).testBit (2 * (r : ℕ)) then (1 : K) else 0).det =
      if o8mDeltaBit col i then 1 else 0 := by
  let φ : ZMod 2 →+* K := ZMod.castHom (dvd_refl 2) K
  have hmap : (Matrix.of fun r c : Fin (i + 1) =>
        if (col (c : ℕ)).testBit (2 * (r : ℕ)) then (1 : ZMod 2) else 0).map φ =
      (Matrix.of fun r c : Fin (i + 1) =>
        if (col (c : ℕ)).testBit (2 * (r : ℕ)) then (1 : K) else 0) := by
    ext r c
    simp only [Matrix.map_apply, Matrix.of_apply]
    cases h : (col (c : ℕ)).testBit (2 * (r : ℕ)) <;> simp [φ]
  calc (Matrix.of fun r c : Fin (i + 1) =>
          if (col (c : ℕ)).testBit (2 * (r : ℕ)) then (1 : K) else 0).det
      = ((Matrix.of fun r c : Fin (i + 1) =>
          if (col (c : ℕ)).testBit (2 * (r : ℕ)) then (1 : ZMod 2) else 0).map φ).det := by
        rw [hmap]
    _ = φ ((Matrix.of fun r c : Fin (i + 1) =>
          if (col (c : ℕ)).testBit (2 * (r : ℕ)) then (1 : ZMod 2) else 0).det) :=
        (RingHom.map_det φ _).symm
    _ = φ (if o8mDeltaBit col i then (1 : ZMod 2) else 0) := by rw [o8mWO_det_zmod]
    _ = if o8mDeltaBit col i then (1 : K) else 0 := by
        cases h : o8mDeltaBit col i <;> simp [φ]

private theorem o8mWO_minorProd_iff (p q r δ0 δ1 δ2 : Bool) :
    ((p = true → δ0) ∧ (q = true → δ1) ∧ (r = true → δ2)) ↔
      ((!p || δ0) && (!q || δ1) && (!r || δ2)) = true := by
  cases p <;> cases q <;> cases r <;> cases δ0 <;> cases δ1 <;> cases δ2 <;>
    decide +kernel

theorem spinAction_o8mWordElt {w : List ℕ} (hw : o8mEvenWord w = true) (x : ℕ) :
    spinAction (quadMinus 4 K 1 1) (o8mWordElt w) (o8mVec x) = o8mVec (o8mWordBit w x) := by
  induction w using o8mWordElt.induct with
  | case1 u v w ih =>
      simp only [o8mEvenWord, List.length_cons, List.all_cons, Bool.and_eq_true,
        beq_iff_eq] at hw
      have hw' : o8mEvenWord w = true := by
        simp only [o8mEvenWord, Bool.and_eq_true, beq_iff_eq]
        exact ⟨by omega, hw.2.2.2⟩
      have hu : o8mNormBit u = true := hw.2.1
      have hv : o8mNormBit v = true := hw.2.2.1
      have hnorm : quadMinus 4 K 1 1 (o8mVec u) * quadMinus 4 K 1 1 (o8mVec v) = 1 := by
        rw [quadMinus_o8mVec, quadMinus_o8mVec, if_pos hu, if_pos hv, one_mul]
      rw [o8mWordElt.eq_1]
      simp only [o8mWordBit, List.foldr_cons]
      rw [map_mul, LinearEquiv.mul_apply, ih hw']
      rw [o8mPairElt, dif_pos hnorm,
        CFSG.ComponentClassification.GSThmB.Cent516.spinAction_pairElt hnorm,
        LinearEquiv.mul_apply, reflect_o8mVec hv, reflect_o8mVec hu]
      rfl
  | case2 t ht =>
      cases t with
      | nil => simp [o8mWordElt, o8mWordBit]
      | cons u t' =>
          cases t' with
          | nil => simp [o8mEvenWord] at hw
          | cons v w => exact absurd rfl (ht u v w)

theorem o8mMinor_mat_of_spinAction {g : spinGroup (quadMinus 4 K 1 1)} {w : List ℕ}
    (hg : ∀ x, spinAction (quadMinus 4 K 1 1) g (o8mVec x) = o8mVec (o8mWordBit w x))
    (i : Fin 3) :
    o8mMinor i (mat 4 g) = if o8mDeltaBit (o8mWordCol w) i then 1 else 0 := by
  have hentry : ∀ r c : Fin 3, mat 4 g (.inl r) (.inl c) =
      if (o8mWordCol w c).testBit (2 * (r : ℕ)) then (1 : K) else 0 := by
    intro r c
    rw [mat_apply, ← o8mVec_two_pow (K := K) (a := .inl c), hg]
    simp only [o8mVec, o8mBit, o8mWordCol]
    rfl
  rw [o8mMinor]
  have hsub : (mat 4 g).submatrix
        (fun j : Fin (i + 1) => Sum.inl (Fin.castLE i.isLt j))
        (fun j : Fin (i + 1) => Sum.inl (Fin.castLE i.isLt j)) =
      Matrix.of (fun r c : Fin (i + 1) =>
        if (o8mWordCol w (c : ℕ)).testBit (2 * (r : ℕ)) then (1 : K) else 0) := by
    ext r c
    rw [Matrix.submatrix_apply, hentry]
    rfl
  rw [hsub]
  exact o8mWO_det_eq (o8mWordCol w) i

theorem o8mMinorProd_mat_of_spinAction {g : spinGroup (quadMinus 4 K 1 1)} {w : List ℕ}
    (hg : ∀ x, spinAction (quadMinus 4 K 1 1) g (o8mVec x) = o8mVec (o8mWordBit w x))
    {J : Finset (Fin 3)} {m : ℕ} (hJ : ∀ i, i ∈ J ↔ m.testBit i = true) :
    o8mMinorProd J (mat 4 g) = if o8mMinorProdBit (o8mWordCol w) m then 1 else 0 := by
  rw [o8mMinorProd]
  have hstep : ∀ i, o8mMinor i (mat 4 g) =
      if o8mDeltaBit (o8mWordCol w) i then 1 else 0 :=
    fun i => o8mMinor_mat_of_spinAction hg i
  simp only [hstep]
  rw [Finset.prod_boole]
  have hmem : (∀ i ∈ J, o8mDeltaBit (o8mWordCol w) i) ↔
      ((m.testBit 0 = true → o8mDeltaBit (o8mWordCol w) 0) ∧
       (m.testBit 1 = true → o8mDeltaBit (o8mWordCol w) 1) ∧
       (m.testBit 2 = true → o8mDeltaBit (o8mWordCol w) 2)) := by
    constructor
    · intro h
      exact ⟨fun h0 => h 0 ((hJ 0).2 h0), fun h1 => h 1 ((hJ 1).2 h1),
        fun h2 => h 2 ((hJ 2).2 h2)⟩
    · rintro ⟨h0, h1, h2⟩ i hi
      fin_cases i
      · exact h0 ((hJ 0).1 hi)
      · exact h1 ((hJ 1).1 hi)
      · exact h2 ((hJ 2).1 hi)
  have hiff : (∀ i ∈ J, o8mDeltaBit (o8mWordCol w) i) ↔
      o8mMinorProdBit (o8mWordCol w) m = true := by
    rw [hmem]
    simpa [o8mMinorProdBit] using o8mWO_minorProd_iff (m.testBit 0) (m.testBit 1) (m.testBit 2)
      (o8mDeltaBit (o8mWordCol w) 0) (o8mDeltaBit (o8mWordCol w) 1)
      (o8mDeltaBit (o8mWordCol w) 2)
  by_cases h : (∀ i ∈ J, o8mDeltaBit (o8mWordCol w) i)
  · rw [if_pos h, if_pos (hiff.mp h)]
  · rw [if_neg h, if_neg (fun hq => h (hiff.mpr hq))]

end CFSG.LocalAnalysis.WeakClosure81

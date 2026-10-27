module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2OmMinusWords

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.LieType.Universal.Spin CFSG.LieType.Universal.Spin.Twisted

private def o8mSV_rows1 : List (List ℕ) := [[], [64, 19, 64, 125], [64, 208, 64, 251],
  [64, 53, 64, 124], [64, 63, 64, 119], [64, 213, 64, 209], [64, 84, 64, 162], [64, 137, 64, 196],
  [64, 88, 64, 35], [64, 49, 64, 201], [64, 85, 64, 132], [64, 239, 64, 153], [64, 23, 64, 148],
  [64, 133, 64, 82], [64, 201, 64, 160], [64, 217, 64, 39], [64, 145, 64, 228]]

private def o8mSV_cols1 : List (List ℕ) := [[], [125, 64, 19, 64], [251, 64, 208, 64],
  [124, 64, 53, 64], [168, 64, 58, 64], [119, 64, 63, 64], [144, 64, 154, 64], [162, 64, 84, 64],
  [196, 64, 137, 64], [35, 64, 88, 64], [201, 64, 49, 64], [153, 64, 239, 64], [82, 64, 133, 64],
  [160, 64, 201, 64], [39, 64, 217, 64], [243, 64, 209, 64], [226, 64, 170, 64]]

private def o8mSV_inv1 : List ℕ := [112332, 96728, 75325, 34446, 13290, 46617, 78933, 45915,
  129835, 50931, 42670, 82173, 117659, 65552, 83646, 77294, 77809]

private def o8mSV_rows2 : List (List ℕ) := [[], [64, 19, 64, 125], [64, 208, 64, 251],
  [64, 53, 64, 124], [64, 58, 64, 168], [64, 63, 64, 119], [64, 213, 64, 209], [64, 154, 64, 144],
  [64, 84, 64, 162], [64, 137, 64, 196], [64, 88, 64, 35], [64, 49, 64, 201], [64, 85, 64, 132],
  [64, 239, 64, 153], [64, 23, 64, 148], [64, 133, 64, 82], [64, 201, 64, 160]]

private def o8mSV_cols2 : List (List ℕ) := [[], [125, 64, 19, 64], [251, 64, 208, 64],
  [124, 64, 53, 64], [168, 64, 58, 64], [119, 64, 63, 64], [144, 64, 154, 64], [162, 64, 84, 64],
  [196, 64, 137, 64], [35, 64, 88, 64], [201, 64, 49, 64], [153, 64, 239, 64], [148, 64, 23, 64],
  [82, 64, 133, 64], [160, 64, 201, 64], [192, 64, 96, 64], [101, 64, 57, 64]]

private def o8mSV_inv2 : List ℕ := [122152, 25339, 53546, 13553, 38305, 16392, 85242, 16422,
  81152, 32526, 15108, 16174, 103846, 30714, 6211, 46833, 61627]

private def o8mSV_coeff (rows cols : List (List ℕ)) (i : Fin 3) (r c : Fin 17) : Bool :=
  o8mDeltaBit (o8mWordCol (rows.getD r [] ++ cols.getD c [])) i

private def o8mSV_invT {n : ℕ} (inv : List ℕ) (r c : Fin n) : Bool := (inv.getD r 0).testBit c

private theorem o8mSV_even_rows1 :
    ∀ r : Fin 17, o8mEvenWord (o8mSV_rows1.getD r []) = true := by
  decide +kernel

private theorem o8mSV_even_cols1 :
    ∀ c : Fin 17, o8mEvenWord (o8mSV_cols1.getD c []) = true := by
  decide +kernel

private theorem o8mSV_even_rows2 :
    ∀ r : Fin 17, o8mEvenWord (o8mSV_rows2.getD r []) = true := by
  decide +kernel

private theorem o8mSV_even_cols2 :
    ∀ c : Fin 17, o8mEvenWord (o8mSV_cols2.getD c []) = true := by
  decide +kernel

private theorem o8mSV_mul1 :
    o8mBoolMat (o8mSV_coeff o8mSV_rows1 o8mSV_cols1 1) *
      o8mBoolMat (o8mSV_invT o8mSV_inv1) = 1 := by
  decide +kernel

private theorem o8mSV_mul2 :
    o8mBoolMat (o8mSV_coeff o8mSV_rows2 o8mSV_cols2 2) *
      o8mBoolMat (o8mSV_invT o8mSV_inv2) = 1 := by
  decide +kernel

private theorem o8mSV_spinAction_mul {K : Type*} [Field K] [CharP K 2]
    (rows cols : List (List ℕ))
    (hrows : ∀ r : Fin 17, o8mEvenWord (rows.getD r []) = true)
    (hcols : ∀ c : Fin 17, o8mEvenWord (cols.getD c []) = true) (r c : Fin 17) (x : ℕ) :
    spinAction (quadMinus 4 K 1 1)
        (o8mWordElt (rows.getD r []) * o8mWordElt (cols.getD c [])) (o8mVec x) =
      o8mVec (o8mWordBit (rows.getD r [] ++ cols.getD c []) x) := by
  rw [map_mul, LinearEquiv.mul_apply, spinAction_o8mWordElt (hcols c) x,
    spinAction_o8mWordElt (hrows r) (o8mWordBit (cols.getD c []) x), o8mWordBit_append]

private theorem o8mSV_minor {K : Type*} [Field K] [CharP K 2]
    (rows cols : List (List ℕ))
    (hrows : ∀ r : Fin 17, o8mEvenWord (rows.getD r []) = true)
    (hcols : ∀ c : Fin 17, o8mEvenWord (cols.getD c []) = true) (i : Fin 3) (r c : Fin 17) :
    o8mMinor i (mat 4 (o8mWordElt (rows.getD r []) * o8mWordElt (cols.getD c []))) =
      if o8mSV_coeff rows cols i r c then (1 : K) else 0 := by
  have hg : ∀ x, spinAction (quadMinus 4 K 1 1)
      (o8mWordElt (rows.getD r []) * o8mWordElt (cols.getD c [])) (o8mVec x) =
      o8mVec (o8mWordBit (rows.getD r [] ++ cols.getD c []) x) :=
    fun x => o8mSV_spinAction_mul rows cols hrows hcols r c x
  rw [o8mMinor_mat_of_spinAction hg i]
  rfl

private theorem o8mSV_det_ne_zero {K : Type*} [Field K] [CharP K 2] {k : Type*} [Field k]
    (φ : K →+* k) (rows cols : List (List ℕ)) (inv : List ℕ) (i : Fin 3)
    (hrows : ∀ r : Fin 17, o8mEvenWord (rows.getD r []) = true)
    (hcols : ∀ c : Fin 17, o8mEvenWord (cols.getD c []) = true)
    (hmul : o8mBoolMat (o8mSV_coeff rows cols i) * o8mBoolMat (o8mSV_invT inv) = 1) :
    (Matrix.of fun (r c : Fin 17) =>
      φ (o8mMinor i (mat 4
        (o8mWordElt (rows.getD r []) * o8mWordElt (cols.getD c []))))).det ≠ 0 := by
  have hchar : CharP k 2 := charP_of_injective_ringHom φ.injective 2
  have hmat : (Matrix.of fun (r c : Fin 17) =>
        φ (o8mMinor i (mat 4
          (o8mWordElt (rows.getD r []) * o8mWordElt (cols.getD c []))))) =
      Matrix.of fun (r c : Fin 17) =>
        if o8mSV_coeff rows cols i r c then (1 : k) else 0 := by
    ext r c
    simp only [Matrix.of_apply]
    rw [o8mSV_minor rows cols hrows hcols i r c, apply_ite (φ : K → k)]
    simp only [map_one, map_zero]
  rw [hmat]
  exact @o8mBoolMat_det_ne_zero 17 k _ hchar (o8mSV_coeff rows cols i) (o8mSV_invT inv) hmul

theorem o8m_seventeen_det_ne_zero {K : Type*} [Field K] [CharP K 2] {k : Type*} [Field k]
    (φ : K →+* k) {i : Fin 3} (hi : i ≠ 0) :
    ∃ a h : Fin 17 → spinGroup (quadMinus 4 K 1 1),
      (Matrix.of fun r c => φ (o8mMinor i (mat 4 (a r * h c)))).det ≠ 0 := by
  fin_cases i
  · exact (hi rfl).elim
  · refine ⟨fun r => o8mWordElt (o8mSV_rows1.getD r []),
      fun c => o8mWordElt (o8mSV_cols1.getD c []), ?_⟩
    exact o8mSV_det_ne_zero φ o8mSV_rows1 o8mSV_cols1 o8mSV_inv1 1
      o8mSV_even_rows1 o8mSV_even_cols1 o8mSV_mul1
  · refine ⟨fun r => o8mWordElt (o8mSV_rows2.getD r []),
      fun c => o8mWordElt (o8mSV_cols2.getD c []), ?_⟩
    exact o8mSV_det_ne_zero φ o8mSV_rows2 o8mSV_cols2 o8mSV_inv2 2
      o8mSV_even_rows2 o8mSV_even_cols2 o8mSV_mul2

end CFSG.LocalAnalysis.WeakClosure81

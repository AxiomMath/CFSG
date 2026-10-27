module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2OmMinusMinorTri
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2OmMinusOuter
import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2OmMinusWords

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin.SmithCurtis CFSG.LieType.Universal.Spin CFSG.LieType.Universal.Spin.Twisted
open scoped Matrix

private def o8mOuterCoeffBit (m : ℕ) (wu : List ℕ) (rows cols : Fin 4 → List ℕ) (i j : Fin 4) :
    Bool :=
  o8mMinorProdBit (o8mWordCol (rows i ++ wu ++ [64] ++ cols j ++ [64])) m ^^
    o8mMinorProdBit (o8mWordCol (rows i ++ cols j)) m

variable {K : Type} [Field K] [Finite K] [CharP K 2]

omit [Finite K] [CharP K 2] in
private theorem planeVec_planeOne_eq_o8mVec :
    (planeVec 4 (planeOne : Fin 2 → K)) = o8mVec 64 := by
  funext a
  rcases a with i | i | t
  · fin_cases i <;> rfl
  · fin_cases i <;> rfl
  · fin_cases t <;> rfl

omit [Finite K] in
private theorem eVec_add_fVec_zero_eq_o8mVec :
    (eVec 4 0 + fVec 4 0 : Vm 4 K) = o8mVec 3 := by
  rw [show (3 : ℕ) = 2 ^ o8mBit (.inl (0 : Fin 3)) ^^^ 2 ^ o8mBit (.inr (.inl (0 : Fin 3))) from
    rfl, o8mVec_xor, o8mVec_two_pow, o8mVec_two_pow]
  rfl

omit [Finite K] in
private theorem eVec_add_fVec_one_eq_o8mVec :
    (eVec 4 1 + fVec 4 1 : Vm 4 K) = o8mVec 12 := by
  rw [show (12 : ℕ) = 2 ^ o8mBit (.inl (1 : Fin 3)) ^^^ 2 ^ o8mBit (.inr (.inl (1 : Fin 3))) from
    rfl, o8mVec_xor, o8mVec_two_pow, o8mVec_two_pow]
  rfl

omit [Finite K] [CharP K 2] in
private theorem spinAction_mul_apply (g h : spinGroup (quadMinus 4 K 1 1)) (v : Vm 4 K) :
    spinAction (quadMinus 4 K 1 1) (g * h) v =
      spinAction (quadMinus 4 K 1 1) g (spinAction (quadMinus 4 K 1 1) h v) := by
  rw [map_mul, LinearEquiv.mul_apply]

variable (hirrQ : ∀ s : K, s ^ 2 + 1 * s + 1 ≠ 0)

include hirrQ in
private theorem spinAction_o8mOuterAut_o8mVec {h : spinGroup (quadMinus 4 K 1 1)} {w : List ℕ}
    (hh : ∀ x, spinAction (quadMinus 4 K 1 1) h (o8mVec x) = o8mVec (o8mWordBit w x)) (x : ℕ) :
    spinAction (quadMinus 4 K 1 1) (o8mOuterAut hirrQ h) (o8mVec x) =
      o8mVec (o8mWordBit ([64] ++ w ++ [64]) x) := by
  have hP : ∀ y, o8mPlaneRefl (b := (1 : K)) (c := 1) (o8mVec y) = o8mVec (o8mReflBit 64 y) :=
    fun y => by
      rw [o8mPlaneRefl_eq_reflect, planeVec_planeOne_eq_o8mVec]
      exact reflect_o8mVec (by decide) y
  have hPinv : (o8mPlaneRefl (b := (1 : K)) (c := 1))⁻¹ = o8mPlaneRefl (b := (1 : K)) (c := 1) := by
    refine inv_eq_of_mul_eq_one_left ?_
    rw [o8mPlaneRefl_eq_reflect]
    exact CFSG.ClassicalGroups.Orthogonal.reflect_mul_self _ _
  rw [spinAction_o8mOuterAut, hPinv, LinearEquiv.mul_apply, LinearEquiv.mul_apply, hP, hh, hP,
    o8mWordBit_append, o8mWordBit_append]
  rfl

omit [Finite K] [CharP K 2] in
private theorem map_ite_one_zero (φ : K →+* ZMod 2) (B : Bool) :
    φ (if B then 1 else 0) = if B then 1 else 0 := by
  cases B <;> simp

private theorem ite_add_ite_eq_xor (B C : Bool) :
    ((if B then 1 else 0) + (if C then 1 else 0) : ZMod 2) = if (B ^^ C) then 1 else 0 := by
  cases B <;> cases C <;> decide

include hirrQ in
private theorem omMinus_two_outer_check_case {J : Finset (Fin 3)} {m : ℕ}
    (hJ : ∀ i, i ∈ J ↔ m.testBit i = true) {u : spinGroup (quadMinus 4 K 1 1)} {wu : List ℕ}
    (hu : ∀ x, spinAction (quadMinus 4 K 1 1) u (o8mVec x) = o8mVec (o8mWordBit wu x))
    (φ : K →+* ZMod 2) (rows cols : Fin 4 → List ℕ)
    (hrows : ∀ i, o8mEvenWord (rows i) = true) (hcols : ∀ j, o8mEvenWord (cols j) = true)
    (F : Fin 4 → Fin 4 → Bool)
    (hF : o8mBoolMat (o8mOuterCoeffBit m wu rows cols) * o8mBoolMat F = 1) :
    ∃ a h : Fin 4 → spinGroup (quadMinus 4 K 1 1),
      (Matrix.of fun i j => φ (o8mMinorProd J (mat 4 (a i * (u * o8mOuterAut hirrQ (h j))))) +
        φ (o8mMinorProd J (mat 4 (a i * h j)))).det ≠ 0 := by
  refine ⟨fun i => o8mWordElt (rows i), fun j => o8mWordElt (cols j), ?_⟩
  have h1 : ∀ i j x, spinAction (quadMinus 4 K 1 1)
      (o8mWordElt (rows i) * (u * o8mOuterAut hirrQ (o8mWordElt (cols j)))) (o8mVec x) =
      o8mVec (o8mWordBit (rows i ++ wu ++ [64] ++ cols j ++ [64]) x) := by
    intro i j x
    rw [spinAction_mul_apply, spinAction_mul_apply,
      spinAction_o8mOuterAut_o8mVec hirrQ (spinAction_o8mWordElt (hcols j)), hu,
      spinAction_o8mWordElt (hrows i)]
    simp only [o8mWordBit_append, List.append_assoc]
  have h2 : ∀ i j x, spinAction (quadMinus 4 K 1 1)
      (o8mWordElt (rows i) * o8mWordElt (cols j)) (o8mVec x) =
      o8mVec (o8mWordBit (rows i ++ cols j) x) := by
    intro i j x
    rw [spinAction_mul_apply, spinAction_o8mWordElt (hcols j), spinAction_o8mWordElt (hrows i),
      o8mWordBit_append]
  have hM : (Matrix.of fun i j =>
      φ (o8mMinorProd J
          (mat 4 (o8mWordElt (rows i) * (u * o8mOuterAut hirrQ (o8mWordElt (cols j)))))) +
        φ (o8mMinorProd J (mat 4 (o8mWordElt (rows i) * o8mWordElt (cols j))))) =
      Matrix.of fun i j => if o8mOuterCoeffBit m wu rows cols i j then (1 : ZMod 2) else 0 := by
    ext i j
    rw [Matrix.of_apply, Matrix.of_apply, o8mMinorProd_mat_of_spinAction (h1 i j) hJ,
      o8mMinorProd_mat_of_spinAction (h2 i j) hJ, map_ite_one_zero, map_ite_one_zero,
      ite_add_ite_eq_xor]
    rfl
  rw [hM]
  exact o8mBoolMat_det_ne_zero hF

include hirrQ in
theorem omMinus_two_outer_checks {μ : Fin 3 → ZMod 2} (hμ0 : μ ≠ 0)
    (hμ1 : μ ≠ fun s => if s.val = 0 then 1 else 0) {u : spinGroup (quadMinus 4 K 1 1)}
    (hu : u = 1 ∨ spinAction (quadMinus 4 K 1 1) u =
      CFSG.ClassicalGroups.Orthogonal.reflect (quadMinus 4 K 1 1) (eVec 4 0 + fVec 4 0) *
        CFSG.ClassicalGroups.Orthogonal.reflect (quadMinus 4 K 1 1) (eVec 4 1 + fVec 4 1))
    (φ : K →+* ZMod 2) :
    ∃ a h : Fin 4 → spinGroup (quadMinus 4 K 1 1),
      (Matrix.of fun i j =>
        φ (o8mMinorProd (Finset.univ.filter fun i => μ i = 1)
          (mat 4 (a i * (u * o8mOuterAut hirrQ (h j))))) +
        φ (o8mMinorProd (Finset.univ.filter fun i => μ i = 1) (mat 4 (a i * h j)))).det ≠ 0 := by
  obtain ⟨a0, a1, a2, rfl⟩ : ∃ a0 a1 a2 : ZMod 2, μ = ![a0, a1, a2] :=
    ⟨μ 0, μ 1, μ 2, by funext i; fin_cases i <;> rfl⟩
  rcases hu with rfl | hu
  · have hu1 : ∀ x, spinAction (quadMinus 4 K 1 1) 1 (o8mVec x) = o8mVec (o8mWordBit [] x) :=
      fun x => by rw [map_one]; rfl
    fin_cases a0 <;> fin_cases a1 <;> fin_cases a2
    · exact absurd (by funext i; fin_cases i <;> rfl) hμ0
    · exact omMinus_two_outer_check_case hirrQ (m := 4) (by decide) hu1 φ
        ![[165, 233], [198, 7], [207, 183], [82, 214]]
        ![[69, 170], [202, 119], [29, 202], [164, 86]]
        (by decide) (by decide)
        ![![false, false, false, true], ![true, true, true, false],
          ![true, false, true, false], ![true, true, false, false]]
        (by decide +kernel)
    · exact omMinus_two_outer_check_case hirrQ (m := 2) (by decide) hu1 φ
        ![[145, 223], [165, 13], [198, 213], [160, 187]]
        ![[207, 170], [14, 247], [233, 54], [46, 214]]
        (by decide) (by decide)
        ![![false, false, false, true], ![false, false, true, true],
          ![false, true, false, false], ![true, false, true, false]]
        (by decide +kernel)
    · exact omMinus_two_outer_check_case hirrQ (m := 6) (by decide) hu1 φ
        ![[23, 153], [143, 233], [124, 154], [168, 164]]
        ![[218, 43], [90, 187], [45, 223], [148, 27]]
        (by decide) (by decide)
        ![![false, false, true, true], ![true, false, false, false],
          ![false, true, false, false], ![true, false, false, true]]
        (by decide +kernel)
    · exact absurd (by funext i; fin_cases i <;> rfl) hμ1
    · exact omMinus_two_outer_check_case hirrQ (m := 5) (by decide) hu1 φ
        ![[104, 134], [232, 148], [159, 224], [166, 243]]
        ![[183, 14], [162, 105], [27, 207], [198, 100]]
        (by decide) (by decide)
        ![![false, false, true, true], ![true, false, false, false],
          ![false, true, true, false], ![true, true, false, false]]
        (by decide +kernel)
    · exact omMinus_two_outer_check_case hirrQ (m := 3) (by decide) hu1 φ
        ![[97, 175], [209, 96], [192, 233], [175, 95]]
        ![[207, 188], [207, 85], [170, 19], [223, 130]]
        (by decide) (by decide)
        ![![true, false, false, true], ![true, true, true, true],
          ![true, true, true, false], ![true, false, true, false]]
        (by decide +kernel)
    · exact omMinus_two_outer_check_case hirrQ (m := 7) (by decide) hu1 φ
        ![[14, 154], [133, 85], [102, 149], [137, 82]]
        ![[164, 224], [179, 66], [138, 128], [197, 218]]
        (by decide) (by decide)
        ![![false, true, false, true], ![true, true, false, false],
          ![true, false, true, true], ![false, false, true, true]]
        (by decide +kernel)
  · have hu3 : ∀ x, spinAction (quadMinus 4 K 1 1) u (o8mVec x) = o8mVec (o8mWordBit [3, 12] x) :=
      fun x => by
        rw [hu, LinearEquiv.mul_apply, eVec_add_fVec_zero_eq_o8mVec, eVec_add_fVec_one_eq_o8mVec,
          reflect_o8mVec (by decide), reflect_o8mVec (by decide)]
        rfl
    fin_cases a0 <;> fin_cases a1 <;> fin_cases a2
    · exact absurd (by funext i; fin_cases i <;> rfl) hμ0
    · exact omMinus_two_outer_check_case hirrQ (m := 4) (by decide) hu3 φ
        ![[46, 49], [82, 170], [233, 210], [89, 13]]
        ![[210, 134], [198, 226], [106, 218], [168, 85]]
        (by decide) (by decide)
        ![![true, true, true, true], ![true, true, false, false],
          ![true, true, false, true], ![false, true, true, true]]
        (by decide +kernel)
    · exact omMinus_two_outer_check_case hirrQ (m := 2) (by decide) hu3 φ
        ![[159, 27], [243, 50], [45, 49], [89, 3]]
        ![[39, 46], [145, 134], [119, 66], [106, 125]]
        (by decide) (by decide)
        ![![false, false, true, false], ![true, false, true, false],
          ![false, true, true, true], ![true, false, true, true]]
        (by decide +kernel)
    · exact omMinus_two_outer_check_case hirrQ (m := 6) (by decide) hu3 φ
        ![[98, 198], [193, 168], [214, 53], [166, 154]]
        ![[197, 90], [154, 63], [217, 3], [102, 54]]
        (by decide) (by decide)
        ![![true, false, true, false], ![false, true, true, true],
          ![false, false, false, true], ![true, true, true, true]]
        (by decide +kernel)
    · exact absurd (by funext i; fin_cases i <;> rfl) hμ1
    · exact omMinus_two_outer_check_case hirrQ (m := 5) (by decide) hu3 φ
        ![[58, 125], [119, 96], [53, 179], [29, 3]]
        ![[198, 225], [159, 161], [128, 111], [86, 100]]
        (by decide) (by decide)
        ![![true, true, true, false], ![true, true, false, false],
          ![false, true, false, false], ![true, true, true, true]]
        (by decide +kernel)
    · exact omMinus_two_outer_check_case hirrQ (m := 3) (by decide) hu3 φ
        ![[84, 201], [134, 228], [28, 160], [86, 228]]
        ![[29, 30], [153, 29], [54, 68], [154, 74]]
        (by decide) (by decide)
        ![![true, false, true, false], ![true, true, true, false],
          ![true, true, true, true], ![false, true, true, true]]
        (by decide +kernel)
    · exact omMinus_two_outer_check_case hirrQ (m := 7) (by decide) hu3 φ
        ![[145, 79], [160, 49], [54, 251], [86, 137]]
        ![[11, 53], [210, 166], [252, 95], [95, 50]]
        (by decide) (by decide)
        ![![false, true, false, true], ![false, true, false, false],
          ![true, false, false, false], ![true, false, true, false]]
        (by decide +kernel)

end CFSG.LocalAnalysis.WeakClosure81

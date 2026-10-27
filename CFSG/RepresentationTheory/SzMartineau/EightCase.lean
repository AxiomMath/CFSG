module

public import CFSG.RepresentationTheory.SzMartineau.Expand
import CFSG.LocalAnalysis.SeitzReduction.RankOneSuzukiEightCoords

public section

namespace CFSG.RepresentationTheory.SzMartineau

open CFSG.Open CFSG.RankThree.GF2n.SzExplicit CFSG.CGT.PushingUpLit.SolKNA Matrix

private lemma natCard_F_one : Nat.card (F 1) = 8 := by
  rw [GaloisField.card 2 (2 * 1 + 1) (by omega)]
  norm_num

theorem pow_two_pow_mod_three (x : F 1) (c : ℕ) : x ^ 2 ^ c = x ^ 2 ^ (c % 3) := by
  let _ : Fintype (F 1) := Fintype.ofFinite _
  have hcard : Fintype.card (F 1) = 8 := by rw [← Nat.card_eq_fintype_card, natCard_F_one]
  have hx8 : x ^ 8 = x := by
    have h := FiniteField.pow_card x
    rwa [hcard] at h
  have h8pow : ∀ k : ℕ, x ^ 8 ^ k = x := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
        rw [pow_succ, pow_mul, ih, hx8]
  have h2 : 2 ^ c = 8 ^ (c / 3) * 2 ^ (c % 3) := by
    conv_lhs => rw [show c = 3 * (c / 3) + c % 3 by omega]
    rw [pow_add, pow_mul]
    norm_num
  rw [h2, pow_mul, h8pow]

theorem twHom_one_mod_three (c : ℕ) : twHom 1 c = twHom 1 (c % 3) := by
  refine MonoidHom.ext fun g => ?_
  ext i j
  simp only [twHom_apply, Matrix.map_apply]
  exact pow_two_pow_mod_three ((natHom 1 g) i j) c

variable {c : ℕ} {Y : ↥(Sz 1) → Matrix (Fin 4) (Fin 4) (F 1)}

private lemma apply_rootSz_add_one_three
    (hY : IsTwistedCocycle (natHom 1) (twHom 1 c) Y)
    (hT : ∀ x, Y (torusSz 1 x) = 0)
    {z : F 1} (hz : z ^ 3 = z + 1)
    {u : (F 1)ˣ} (hu : (u : F 1) = z)
    {A : Matrix (Fin 4) (Fin 4) (F 1)} (hA : Y (rootSz 1 1 0) = A) :
    rootMat 1 1 0 * (torusMat 1 u * A * torusMat 1 (u ^ 2 ^ c)⁻¹) +
        A * rootMat 1 (z ^ 2 ^ c) 0 =
      rootMat 1 (1 + z) 0 *
          (torusMat 1 (u ^ 5) *
            (rootMat 1 1 0 * A + A * rootMat 1 1 0) * torusMat 1 ((u ^ 5) ^ 2 ^ c)⁻¹) +
        (torusMat 1 (u ^ 3) * A * torusMat 1 ((u ^ 3) ^ 2 ^ c)⁻¹) *
          rootMat 1 0 ((z ^ 2 ^ (1 + 1)) ^ 2 ^ c) := by
  have hz0 : z ≠ 0 := by
    rintro rfl
    norm_num at hz
  have hz7 : z ^ 7 = 1 := by grind
  have hS1 : Y (rootSz 1 z 0) =
      torusMat 1 u * A * torusMat 1 (u ^ 2 ^ c)⁻¹ := by
    have h := hY.apply_rootSz_unit hT u
    rwa [hu, hA] at h
  have hS3 : Y (rootSz 1 (1 + z) 0) =
      torusMat 1 (u ^ 3) * A * torusMat 1 ((u ^ 3) ^ 2 ^ c)⁻¹ := by
    have h := hY.apply_rootSz_unit hT (u ^ 3)
    rw [hA] at h
    rwa [Units.val_pow_eq_pow_val, hu, hz, add_comm] at h
  have hS5 : Y (rootSz 1 0 (z ^ 2 ^ (1 + 1))) =
      torusMat 1 (u ^ 5) * (rootMat 1 1 0 * A + A * rootMat 1 1 0) *
        torusMat 1 ((u ^ 5) ^ 2 ^ c)⁻¹ := by
    have h := hY.apply_rootSz_zero_unit hT (u ^ 5)
    have e : ((u ^ 5 : (F 1)ˣ) : F 1) ^ (1 + 2 ^ (1 + 1)) =
        z ^ 2 ^ (1 + 1) := by
      rw [Units.val_pow_eq_pow_val, hu]
      linear_combination z ^ 4 * (z ^ 14 + z ^ 7 + 1) * hz7
    rw [e, hY.apply_rootSz_zero_one, hA] at h
    simpa [one_mul] using h
  have hR := hY.apply_rootSz_add 1 z
  simp only [one_mul] at hR
  rw [hS1, hS3, hS5, hA] at hR
  simpa [one_mul] using hR

private lemma unit_pow_seven (v : (F 1)ˣ) : v ^ 7 = 1 := by
  let _ : Fintype (F 1) := Fintype.ofFinite _
  have hcard : Fintype.card (F 1) = 8 := by rw [← Nat.card_eq_fintype_card, natCard_F_one]
  have h := FiniteField.pow_card_sub_one_eq_one (v : F 1) v.ne_zero
  rw [hcard] at h
  exact Units.ext h

private lemma torusMat_one_eq (v : (F 1)ˣ) :
    torusMat 1 v =
      Matrix.diagonal ![(v : F 1) ^ 3, (v : F 1) ^ 2, (v : F 1) ^ 5, (v : F 1) ^ 4] := by
  have h7 : (v : F 1) ^ 7 = 1 := congrArg (fun w : (F 1)ˣ => (w : F 1)) (unit_pow_seven v)
  have h25 : (v : F 1) ^ 2 * (v : F 1) ^ 5 = 1 := by
    rw [← pow_add]
    norm_num
    exact h7
  have h34 : (v : F 1) ^ 3 * (v : F 1) ^ 4 = 1 := by
    rw [← pow_add]
    norm_num
    exact h7
  ext i j
  fin_cases i <;> fin_cases j <;> simp [torusMat, Matrix.diagonal]
  · rw [inv_eq_of_mul_eq_one_right h25]
  · rw [inv_eq_of_mul_eq_one_right h34]

private lemma inv_pow_eq_pow (v : (F 1)ˣ) {k m : ℕ} (h : 7 ∣ k + m) :
    (v ^ k)⁻¹ = v ^ m := by
  apply inv_eq_of_mul_eq_one_right
  rw [← pow_add]
  obtain ⟨n, hn⟩ := h
  rw [hn, pow_mul, unit_pow_seven, one_pow]

private lemma z_unit_data {z : F 1} (hz : z ^ 3 = z + 1) :
    ∃ u : (F 1)ˣ, (u : F 1) = z ∧ orderOf u = 7 ∧ z⁻¹ = z ^ 6 ∧ z ≠ 1 := by
  have hz7 : z ^ 7 = 1 := by grind
  have hz0 : z ≠ 0 := by
    rintro rfl
    norm_num at hz
  have hz1 : z ≠ 1 := by
    rintro rfl
    norm_num at hz
    rw [show (2 : F 1) = 0 from CharTwo.two_eq_zero] at hz
    exact one_ne_zero hz
  let u : (F 1)ˣ := Units.mk0 z hz0
  have hu : (u : F 1) = z := rfl
  have hz7u : u ^ 7 = 1 := by
    rw [← Units.val_inj, Units.val_pow_eq_pow_val, hu, hz7, Units.val_one]
  have hu1 : u ≠ 1 := by
    intro h
    apply hz1
    rw [← hu, h, Units.val_one]
  haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  refine ⟨u, hu, orderOf_eq_prime hz7u hu1, ?_, hz1⟩
  rw [inv_eq_of_mul_eq_one_right (by rw [← pow_succ']; exact hz7)]

private lemma z_pow_reduce {z : F 1} (hz : z ^ 3 = z + 1) :
    z ^ 4 = z ^ 2 + z ∧ z ^ 5 = z ^ 2 + z + 1 ∧ z ^ 6 = z ^ 2 + 1 := by
  have h4 : z ^ 4 = z ^ 2 + z := by linear_combination z * hz
  have h5 : z ^ 5 = z ^ 2 + z + 1 := by linear_combination z * h4 + hz
  exact ⟨h4, h5, by linear_combination (norm := grind) z * h5 + hz⟩

private noncomputable def AOf (p0 p1 p2 p3 p4 p5 p6 p7 : F 1) :
    Matrix (Fin 4) (Fin 4) (F 1) :=
  !![p3 + p4, p0 + p2 + p5, p6, p1 + p2 + p7;
     p3 + p7, p2 + p4 + p6, p1, p0 + p5 + p6;
     p3, p2 + p7, p1 + p6, p0 + p5 + p6 + p7;
     0, p3, p2, p1 + p2 + p3]

private lemma poly_zero
    (hY : IsTwistedCocycle (natHom 1) (twHom 1 0) Y)
    (hT : ∀ x, Y (torusSz 1 x) = 0) {z : F 1} (hz : z ^ 3 = z + 1)
    {A : Matrix (Fin 4) (Fin 4) (F 1)} (hA : Y (rootSz 1 1 0) = A) :
    rootMat 1 1 0 *
        (Matrix.diagonal ![z ^ 3, z ^ 2, z ^ 5, z ^ 4] * A *
          Matrix.diagonal ![(z ^ 6) ^ 3, (z ^ 6) ^ 2, (z ^ 6) ^ 5, (z ^ 6) ^ 4]) +
      A * rootMat 1 z 0 =
    rootMat 1 (1 + z) 0 *
        (Matrix.diagonal ![(z ^ 5) ^ 3, (z ^ 5) ^ 2, (z ^ 5) ^ 5, (z ^ 5) ^ 4] *
          (rootMat 1 1 0 * A + A * rootMat 1 1 0) *
          Matrix.diagonal ![(z ^ 2) ^ 3, (z ^ 2) ^ 2, (z ^ 2) ^ 5, (z ^ 2) ^ 4]) +
      (Matrix.diagonal ![(z ^ 3) ^ 3, (z ^ 3) ^ 2, (z ^ 3) ^ 5, (z ^ 3) ^ 4] * A *
        Matrix.diagonal ![(z ^ 4) ^ 3, (z ^ 4) ^ 2, (z ^ 4) ^ 5, (z ^ 4) ^ 4]) *
        rootMat 1 0 (z ^ 4) := by
  obtain ⟨u, hu, _, _, _⟩ := z_unit_data hz
  have hR := apply_rootSz_add_one_three (c := 0) hY hT hz hu hA
  norm_num at hR
  have h1 : u⁻¹ = u ^ 6 := by simpa using inv_pow_eq_pow u (k := 1) (m := 6) (by norm_num)
  have h3 : (u ^ 3)⁻¹ = u ^ 4 := by
    simpa using inv_pow_eq_pow u (k := 3) (m := 4) (by norm_num)
  have h5 : (u ^ 5)⁻¹ = u ^ 2 := by
    simpa using inv_pow_eq_pow u (k := 5) (m := 2) (by norm_num)
  rw [h1, h3, h5] at hR
  rw [torusMat_one_eq u, torusMat_one_eq (u ^ 6), torusMat_one_eq (u ^ 5),
    torusMat_one_eq (u ^ 2), torusMat_one_eq (u ^ 3), torusMat_one_eq (u ^ 4)] at hR
  simpa only [Units.val_pow_eq_pow_val, hu] using hR

private lemma poly_one
    (hY : IsTwistedCocycle (natHom 1) (twHom 1 1) Y)
    (hT : ∀ x, Y (torusSz 1 x) = 0) {z : F 1} (hz : z ^ 3 = z + 1)
    {A : Matrix (Fin 4) (Fin 4) (F 1)} (hA : Y (rootSz 1 1 0) = A) :
    rootMat 1 1 0 *
        (Matrix.diagonal ![z ^ 3, z ^ 2, z ^ 5, z ^ 4] * A *
          Matrix.diagonal ![(z ^ 5) ^ 3, (z ^ 5) ^ 2, (z ^ 5) ^ 5, (z ^ 5) ^ 4]) +
      A * rootMat 1 (z ^ 2) 0 =
    rootMat 1 (1 + z) 0 *
        (Matrix.diagonal ![(z ^ 5) ^ 3, (z ^ 5) ^ 2, (z ^ 5) ^ 5, (z ^ 5) ^ 4] *
          (rootMat 1 1 0 * A + A * rootMat 1 1 0) *
          Matrix.diagonal ![(z ^ 4) ^ 3, (z ^ 4) ^ 2, (z ^ 4) ^ 5, (z ^ 4) ^ 4]) +
      (Matrix.diagonal ![(z ^ 3) ^ 3, (z ^ 3) ^ 2, (z ^ 3) ^ 5, (z ^ 3) ^ 4] * A *
        Matrix.diagonal ![z ^ 3, z ^ 2, z ^ 5, z ^ 4]) *
        rootMat 1 0 ((z ^ 4) ^ 2) := by
  obtain ⟨u, hu, _, _, _⟩ := z_unit_data hz
  have hR := apply_rootSz_add_one_three (c := 1) hY hT hz hu hA
  norm_num at hR
  rw [show (u ^ 5) ^ 2 = u ^ 10 by rw [← pow_mul],
    show (u ^ 3) ^ 2 = u ^ 6 by rw [← pow_mul]] at hR
  have h1 : (u ^ 2)⁻¹ = u ^ 5 := by
    simpa using inv_pow_eq_pow u (k := 2) (m := 5) (by norm_num)
  have h3 : (u ^ 6)⁻¹ = u := by
    simpa using inv_pow_eq_pow u (k := 6) (m := 1) (by norm_num)
  have h5 : (u ^ 10)⁻¹ = u ^ 4 := by
    simpa using inv_pow_eq_pow u (k := 10) (m := 4) (by norm_num)
  rw [h1, h3, h5] at hR
  rw [torusMat_one_eq u, torusMat_one_eq (u ^ 5), torusMat_one_eq (u ^ 4),
    torusMat_one_eq (u ^ 3)] at hR
  simpa only [Units.val_pow_eq_pow_val, hu] using hR

private lemma poly_two
    (hY : IsTwistedCocycle (natHom 1) (twHom 1 2) Y)
    (hT : ∀ x, Y (torusSz 1 x) = 0) {z : F 1} (hz : z ^ 3 = z + 1)
    {A : Matrix (Fin 4) (Fin 4) (F 1)} (hA : Y (rootSz 1 1 0) = A) :
    rootMat 1 1 0 *
        (Matrix.diagonal ![z ^ 3, z ^ 2, z ^ 5, z ^ 4] * A *
          Matrix.diagonal ![(z ^ 3) ^ 3, (z ^ 3) ^ 2, (z ^ 3) ^ 5, (z ^ 3) ^ 4]) +
      A * rootMat 1 (z ^ 4) 0 =
    rootMat 1 (1 + z) 0 *
        (Matrix.diagonal ![(z ^ 5) ^ 3, (z ^ 5) ^ 2, (z ^ 5) ^ 5, (z ^ 5) ^ 4] *
          (rootMat 1 1 0 * A + A * rootMat 1 1 0) *
          Matrix.diagonal ![z ^ 3, z ^ 2, z ^ 5, z ^ 4]) +
      (Matrix.diagonal ![(z ^ 3) ^ 3, (z ^ 3) ^ 2, (z ^ 3) ^ 5, (z ^ 3) ^ 4] * A *
        Matrix.diagonal ![(z ^ 2) ^ 3, (z ^ 2) ^ 2, (z ^ 2) ^ 5, (z ^ 2) ^ 4]) *
        rootMat 1 0 ((z ^ 4) ^ 4) := by
  obtain ⟨u, hu, _, _, _⟩ := z_unit_data hz
  have hR := apply_rootSz_add_one_three (c := 2) hY hT hz hu hA
  norm_num at hR
  rw [show (u ^ 5) ^ 4 = u ^ 20 by rw [← pow_mul],
    show (u ^ 3) ^ 4 = u ^ 12 by rw [← pow_mul]] at hR
  have h1 : (u ^ 4)⁻¹ = u ^ 3 := by
    simpa using inv_pow_eq_pow u (k := 4) (m := 3) (by norm_num)
  have h3 : (u ^ 12)⁻¹ = u ^ 2 := by
    simpa using inv_pow_eq_pow u (k := 12) (m := 2) (by norm_num)
  have h5 : (u ^ 20)⁻¹ = u := by
    simpa using inv_pow_eq_pow u (k := 20) (m := 1) (by norm_num)
  rw [h1, h3, h5] at hR
  rw [torusMat_one_eq u, torusMat_one_eq (u ^ 3), torusMat_one_eq (u ^ 5),
    torusMat_one_eq (u ^ 2)] at hR
  simpa only [Units.val_pow_eq_pow_val, hu] using hR


private lemma relations_zero_a
    {Y : ↥(Sz 1) → Matrix (Fin 4) (Fin 4) (F 1)}
    (hY : IsTwistedCocycle (natHom 1) (twHom 1 0) Y)
    (hT : ∀ x, Y (torusSz 1 x) = 0) {z : F 1} (hz : z ^ 3 = z + 1)
    {p0 p1 p2 p3 p4 p5 p6 p7 : F 1}
    (hA : Y (rootSz 1 1 0) = AOf p0 p1 p2 p3 p4 p5 p6 p7) :
    p2 = 0 ∧ p3 = 0 ∧ p4 = 0 ∧ p7 = 0 := by
  obtain ⟨u, hu, hord, -, -⟩ := z_unit_data hz
  have hR := poly_zero hY hT hz hA
  have e00 := congrFun (congrFun hR 0) 0
  have e10 := congrFun (congrFun hR 1) 0
  have e21 := congrFun (congrFun hR 2) 1
  have e32 := congrFun (congrFun hR 3) 2
  simp [Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_four, rootMat,
    Matrix.diagonal_mul, Matrix.mul_diagonal, AOf] at e00 e10 e21 e32
  ring_nf at e00 e10 e21 e32
  simp only [CharTwo.ofNat_eq_mod] at e00 e10 e21 e32
  norm_num at e00 e10 e21 e32
  rw [← hu] at e00 e10 e21 e32
  simp only [← Units.val_pow_eq_pow_val] at e00 e10 e21 e32
  simp (config := { singlePass := true }) only [← pow_mod_orderOf u] at e00 e10 e21 e32
  simp (config := { singlePass := true }) only [hord] at e00 e10 e21 e32
  simp only [Units.val_pow_eq_pow_val, hu] at e00 e10 e21 e32
  norm_num at e00 e10 e21 e32
  ring_nf at e00 e10 e21 e32
  simp only [CharTwo.ofNat_eq_mod] at e00 e10 e21 e32
  norm_num at e00 e10 e21 e32
  obtain ⟨hz4, hz5, hz6⟩ := z_pow_reduce hz
  simp only [hz, hz4, hz5, hz6] at e00 e10 e21 e32
  refine ⟨?_, ?_, ?_, ?_⟩
  · linear_combination (norm := grind) (z ^ 2 + 1) * e10 + (z + 1) * e21
  · linear_combination (norm := grind) (z ^ 2 + 1) * e10 + (z + 1) * e21 + (z ^ 2 + 1) * e32
  · linear_combination (norm := grind) e00 + e10 + e21 + (z + 1) * e32
  · linear_combination (norm := grind) (z + 1) * e21 + (z ^ 2 + 1) * e32

private lemma relations_zero_b
    {Y : ↥(Sz 1) → Matrix (Fin 4) (Fin 4) (F 1)}
    (hY : IsTwistedCocycle (natHom 1) (twHom 1 0) Y)
    (hT : ∀ x, Y (torusSz 1 x) = 0) {z : F 1} (hz : z ^ 3 = z + 1)
    {p0 p1 p2 p3 p4 p5 p6 p7 : F 1}
    (hA : Y (rootSz 1 1 0) = AOf p0 p1 p2 p3 p4 p5 p6 p7) :
    p1 = 0 ∧ p6 = 0 := by
  obtain ⟨u, hu, hord, -, -⟩ := z_unit_data hz
  have hR := poly_zero hY hT hz hA
  have e10 := congrFun (congrFun hR 1) 0
  have e22 := congrFun (congrFun hR 2) 2
  have e23 := congrFun (congrFun hR 2) 3
  have e32 := congrFun (congrFun hR 3) 2
  simp [Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_four, rootMat,
    Matrix.diagonal_mul, Matrix.mul_diagonal, AOf] at e10 e22 e23 e32
  ring_nf at e10 e22 e23 e32
  simp only [CharTwo.ofNat_eq_mod] at e10 e22 e23 e32
  norm_num at e10 e22 e23 e32
  rw [← hu] at e10 e22 e23 e32
  simp only [← Units.val_pow_eq_pow_val] at e10 e22 e23 e32
  simp (config := { singlePass := true }) only [← pow_mod_orderOf u] at e10 e22 e23 e32
  simp (config := { singlePass := true }) only [hord] at e10 e22 e23 e32
  simp only [Units.val_pow_eq_pow_val, hu] at e10 e22 e23 e32
  norm_num at e10 e22 e23 e32
  ring_nf at e10 e22 e23 e32
  simp only [CharTwo.ofNat_eq_mod] at e10 e22 e23 e32
  norm_num at e10 e22 e23 e32
  obtain ⟨hz4, hz5, hz6⟩ := z_pow_reduce hz
  simp only [hz, hz4, hz5, hz6] at e10 e22 e23 e32
  refine ⟨?_, ?_⟩
  · linear_combination (norm := grind) (z ^ 2 + z + 1) * e10 + z ^ 2 * e22 +
      (z + 1) * e23 + (z ^ 2 + z) * e32
  · linear_combination (norm := grind) e10 + (z ^ 2 + 1) * e22 + (z + 1) * e23 + z * e32

private lemma relations_one_a
    {Y : ↥(Sz 1) → Matrix (Fin 4) (Fin 4) (F 1)}
    (hY : IsTwistedCocycle (natHom 1) (twHom 1 1) Y)
    (hT : ∀ x, Y (torusSz 1 x) = 0) {z : F 1} (hz : z ^ 3 = z + 1)
    {p0 p1 p2 p3 p4 p5 p6 p7 : F 1}
    (hA : Y (rootSz 1 1 0) = AOf p0 p1 p2 p3 p4 p5 p6 p7) :
    p4 = 0 := by
  obtain ⟨u, hu, hord, -, -⟩ := z_unit_data hz
  have hR := poly_one hY hT hz hA
  have e10 := congrFun (congrFun hR 1) 0
  have e11 := congrFun (congrFun hR 1) 1
  have e12 := congrFun (congrFun hR 1) 2
  have e23 := congrFun (congrFun hR 2) 3
  simp [Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_four, rootMat,
    Matrix.diagonal_mul, Matrix.mul_diagonal, AOf] at e10 e11 e12 e23
  ring_nf at e10 e11 e12 e23
  simp only [CharTwo.ofNat_eq_mod] at e10 e11 e12 e23
  norm_num at e10 e11 e12 e23
  rw [← hu] at e10 e11 e12 e23
  simp only [← Units.val_pow_eq_pow_val] at e10 e11 e12 e23
  simp (config := { singlePass := true }) only [← pow_mod_orderOf u] at e10 e11 e12 e23
  simp (config := { singlePass := true }) only [hord] at e10 e11 e12 e23
  simp only [Units.val_pow_eq_pow_val, hu] at e10 e11 e12 e23
  norm_num at e10 e11 e12 e23
  ring_nf at e10 e11 e12 e23
  simp only [CharTwo.ofNat_eq_mod] at e10 e11 e12 e23
  norm_num at e10 e11 e12 e23
  obtain ⟨hz4, hz5, hz6⟩ := z_pow_reduce hz
  simp only [hz, hz4, hz5, hz6] at e10 e11 e12 e23
  linear_combination (norm := grind) (z + 1) * e10 + z * e11 + (z ^ 2 + z) * e12 + e23

private lemma relations_one_b
    {Y : ↥(Sz 1) → Matrix (Fin 4) (Fin 4) (F 1)}
    (hY : IsTwistedCocycle (natHom 1) (twHom 1 1) Y)
    (hT : ∀ x, Y (torusSz 1 x) = 0) {z : F 1} (hz : z ^ 3 = z + 1)
    {p0 p1 p2 p3 p4 p5 p6 p7 : F 1}
    (hA : Y (rootSz 1 1 0) = AOf p0 p1 p2 p3 p4 p5 p6 p7) :
    p1 = 0 ∧ p3 = 0 ∧ p6 = 0 := by
  obtain ⟨u, hu, hord, -, -⟩ := z_unit_data hz
  have hR := poly_one hY hT hz hA
  have e01 := congrFun (congrFun hR 0) 1
  have e20 := congrFun (congrFun hR 2) 0
  have e23 := congrFun (congrFun hR 2) 3
  have e33 := congrFun (congrFun hR 3) 3
  simp [Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_four, rootMat,
    Matrix.diagonal_mul, Matrix.mul_diagonal, AOf] at e01 e20 e23 e33
  ring_nf at e01 e20 e23 e33
  simp only [CharTwo.ofNat_eq_mod] at e01 e20 e23 e33
  norm_num at e01 e20 e23 e33
  rw [← hu] at e01 e20 e23 e33
  simp only [← Units.val_pow_eq_pow_val] at e01 e20 e23 e33
  simp (config := { singlePass := true }) only [← pow_mod_orderOf u] at e01 e20 e23 e33
  simp (config := { singlePass := true }) only [hord] at e01 e20 e23 e33
  simp only [Units.val_pow_eq_pow_val, hu] at e01 e20 e23 e33
  norm_num at e01 e20 e23 e33
  ring_nf at e01 e20 e23 e33
  simp only [CharTwo.ofNat_eq_mod] at e01 e20 e23 e33
  norm_num at e01 e20 e23 e33
  obtain ⟨hz4, hz5, hz6⟩ := z_pow_reduce hz
  simp only [hz, hz4, hz5, hz6] at e01 e20 e23 e33
  refine ⟨?_, ?_, ?_⟩
  · linear_combination (norm := grind) z * e20 + (z + 1) * e33
  · linear_combination (norm := grind) (z ^ 2 + 1) * e20
  · linear_combination (norm := grind) (z ^ 2 + 1) * e20 + e23 + z * e33

private lemma relations_one_c
    {Y : ↥(Sz 1) → Matrix (Fin 4) (Fin 4) (F 1)}
    (hY : IsTwistedCocycle (natHom 1) (twHom 1 1) Y)
    (hT : ∀ x, Y (torusSz 1 x) = 0) {z : F 1} (hz : z ^ 3 = z + 1)
    {p0 p1 p2 p3 p4 p5 p6 p7 : F 1}
    (hA : Y (rootSz 1 1 0) = AOf p0 p1 p2 p3 p4 p5 p6 p7) :
    p7 = 0 ∧ p0 + p5 = 0 := by
  obtain ⟨u, hu, hord, -, -⟩ := z_unit_data hz
  have hR := poly_one hY hT hz hA
  have e00 := congrFun (congrFun hR 0) 0
  have e01 := congrFun (congrFun hR 0) 1
  have e10 := congrFun (congrFun hR 1) 0
  have e11 := congrFun (congrFun hR 1) 1
  simp [Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_four, rootMat,
    Matrix.diagonal_mul, Matrix.mul_diagonal, AOf] at e00 e01 e10 e11
  ring_nf at e00 e01 e10 e11
  simp only [CharTwo.ofNat_eq_mod] at e00 e01 e10 e11
  norm_num at e00 e01 e10 e11
  rw [← hu] at e00 e01 e10 e11
  simp only [← Units.val_pow_eq_pow_val] at e00 e01 e10 e11
  simp (config := { singlePass := true }) only [← pow_mod_orderOf u] at e00 e01 e10 e11
  simp (config := { singlePass := true }) only [hord] at e00 e01 e10 e11
  simp only [Units.val_pow_eq_pow_val, hu] at e00 e01 e10 e11
  norm_num at e00 e01 e10 e11
  ring_nf at e00 e01 e10 e11
  simp only [CharTwo.ofNat_eq_mod] at e00 e01 e10 e11
  norm_num at e00 e01 e10 e11
  obtain ⟨hz4, hz5, hz6⟩ := z_pow_reduce hz
  simp only [hz, hz4, hz5, hz6] at e00 e01 e10 e11
  refine ⟨?_, ?_⟩
  · linear_combination (norm := grind) (z + 1) * e00
  · linear_combination (norm := grind) (z + 1) * e00 + (z ^ 2 + 1) * e01 + z * e10 + e11

private lemma relations_two_a
    {Y : ↥(Sz 1) → Matrix (Fin 4) (Fin 4) (F 1)}
    (hY : IsTwistedCocycle (natHom 1) (twHom 1 2) Y)
    (hT : ∀ x, Y (torusSz 1 x) = 0) {z : F 1} (hz : z ^ 3 = z + 1)
    {p0 p1 p2 p3 p4 p5 p6 p7 : F 1}
    (hA : Y (rootSz 1 1 0) = AOf p0 p1 p2 p3 p4 p5 p6 p7) :
    p2 = 0 ∧ p3 = 0 ∧ p4 = 0 ∧ p6 = 0 := by
  obtain ⟨u, hu, hord, -, -⟩ := z_unit_data hz
  have hR := poly_two hY hT hz hA
  have e00 := congrFun (congrFun hR 0) 0
  have e01 := congrFun (congrFun hR 0) 1
  have e10 := congrFun (congrFun hR 1) 0
  have e11 := congrFun (congrFun hR 1) 1
  simp [Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_four, rootMat,
    Matrix.diagonal_mul, Matrix.mul_diagonal, AOf] at e00 e01 e10 e11
  ring_nf at e00 e01 e10 e11
  simp only [CharTwo.ofNat_eq_mod] at e00 e01 e10 e11
  norm_num at e00 e01 e10 e11
  rw [← hu] at e00 e01 e10 e11
  simp only [← Units.val_pow_eq_pow_val] at e00 e01 e10 e11
  simp (config := { singlePass := true }) only [← pow_mod_orderOf u] at e00 e01 e10 e11
  simp (config := { singlePass := true }) only [hord] at e00 e01 e10 e11
  simp only [Units.val_pow_eq_pow_val, hu] at e00 e01 e10 e11
  norm_num at e00 e01 e10 e11
  ring_nf at e00 e01 e10 e11
  simp only [CharTwo.ofNat_eq_mod] at e00 e01 e10 e11
  norm_num at e00 e01 e10 e11
  obtain ⟨hz4, hz5, hz6⟩ := z_pow_reduce hz
  simp only [hz, hz4, hz5, hz6] at e00 e01 e10 e11
  refine ⟨?_, ?_, ?_, ?_⟩
  · linear_combination (norm := grind) (z ^ 2 + z) * e10 + e11
  · linear_combination (norm := grind) (z ^ 2 + z + 1) * e10
  · linear_combination (norm := grind) (z ^ 2 + z + 1) * e00
  · linear_combination (norm := grind) e00 + e01 + (z ^ 2 + z + 1) * e10 + (z + 1) * e11

private lemma relations_two_b
    {Y : ↥(Sz 1) → Matrix (Fin 4) (Fin 4) (F 1)}
    (hY : IsTwistedCocycle (natHom 1) (twHom 1 2) Y)
    (hT : ∀ x, Y (torusSz 1 x) = 0) {z : F 1} (hz : z ^ 3 = z + 1)
    {p0 p1 p2 p3 p4 p5 p6 p7 : F 1}
    (hA : Y (rootSz 1 1 0) = AOf p0 p1 p2 p3 p4 p5 p6 p7) :
    p1 = 0 := by
  obtain ⟨u, hu, hord, -, -⟩ := z_unit_data hz
  have hR := poly_two hY hT hz hA
  have e00 := congrFun (congrFun hR 0) 0
  have e01 := congrFun (congrFun hR 0) 1
  have e10 := congrFun (congrFun hR 1) 0
  have e12 := congrFun (congrFun hR 1) 2
  simp [Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_four, rootMat,
    Matrix.diagonal_mul, Matrix.mul_diagonal, AOf] at e00 e01 e10 e12
  ring_nf at e00 e01 e10 e12
  simp only [CharTwo.ofNat_eq_mod] at e00 e01 e10 e12
  norm_num at e00 e01 e10 e12
  rw [← hu] at e00 e01 e10 e12
  simp only [← Units.val_pow_eq_pow_val] at e00 e01 e10 e12
  simp (config := { singlePass := true }) only [← pow_mod_orderOf u] at e00 e01 e10 e12
  simp (config := { singlePass := true }) only [hord] at e00 e01 e10 e12
  simp only [Units.val_pow_eq_pow_val, hu] at e00 e01 e10 e12
  norm_num at e00 e01 e10 e12
  ring_nf at e00 e01 e10 e12
  simp only [CharTwo.ofNat_eq_mod] at e00 e01 e10 e12
  norm_num at e00 e01 e10 e12
  obtain ⟨hz4, hz5, hz6⟩ := z_pow_reduce hz
  simp only [hz, hz4, hz5, hz6] at e00 e01 e10 e12
  linear_combination (norm := grind) (z ^ 2 + 1) * e00 + e01 + z * e10 + e12

private lemma relations_two_c
    {Y : ↥(Sz 1) → Matrix (Fin 4) (Fin 4) (F 1)}
    (hY : IsTwistedCocycle (natHom 1) (twHom 1 2) Y)
    (hT : ∀ x, Y (torusSz 1 x) = 0) {z : F 1} (hz : z ^ 3 = z + 1)
    {p0 p1 p2 p3 p4 p5 p6 p7 : F 1}
    (hA : Y (rootSz 1 1 0) = AOf p0 p1 p2 p3 p4 p5 p6 p7) :
    p0 + p5 = 0 := by
  obtain ⟨u, hu, hord, -, -⟩ := z_unit_data hz
  have hR := poly_two hY hT hz hA
  have e00 := congrFun (congrFun hR 0) 0
  have e02 := congrFun (congrFun hR 0) 2
  have e10 := congrFun (congrFun hR 1) 0
  have e11 := congrFun (congrFun hR 1) 1
  simp [Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_four, rootMat,
    Matrix.diagonal_mul, Matrix.mul_diagonal, AOf] at e00 e02 e10 e11
  ring_nf at e00 e02 e10 e11
  simp only [CharTwo.ofNat_eq_mod] at e00 e02 e10 e11
  norm_num at e00 e02 e10 e11
  rw [← hu] at e00 e02 e10 e11
  simp only [← Units.val_pow_eq_pow_val] at e00 e02 e10 e11
  simp (config := { singlePass := true }) only [← pow_mod_orderOf u] at e00 e02 e10 e11
  simp (config := { singlePass := true }) only [hord] at e00 e02 e10 e11
  simp only [Units.val_pow_eq_pow_val, hu] at e00 e02 e10 e11
  norm_num at e00 e02 e10 e11
  ring_nf at e00 e02 e10 e11
  simp only [CharTwo.ofNat_eq_mod] at e00 e02 e10 e11
  norm_num at e00 e02 e10 e11
  obtain ⟨hz4, hz5, hz6⟩ := z_pow_reduce hz
  simp only [hz, hz4, hz5, hz6] at e00 e02 e10 e11
  linear_combination (norm := grind) (z ^ 2 + z) * e00 + e02 + (z ^ 2 + z) * e10 + (z + 1) * e11

private lemma inv_pow_val (x : (F 1)ˣ) {k m : ℕ} (h : 7 ∣ k + m) :
    ((x : F 1) ^ k)⁻¹ = (x : F 1) ^ m := by
  rw [← Units.val_pow_eq_pow_val, ← Units.val_pow_eq_pow_val, ← Units.val_inv_eq_inv_val]
  exact congrArg (fun w : (F 1)ˣ => (w : F 1)) (inv_pow_eq_pow x h)

private lemma szJ_symmetry (X : Matrix (Fin 4) (Fin 4) (F 1))
    (hXJ : szJ * X = X * szJ) :
    X 2 0 = X 1 3 ∧ X 2 1 = X 1 2 ∧ X 2 2 = X 1 1 ∧ X 2 3 = X 1 0 ∧
      X 3 0 = X 0 3 ∧ X 3 1 = X 0 2 ∧ X 3 2 = X 0 1 ∧ X 3 3 = X 0 0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa using eq_of_szJ_mul_eq hXJ 1 3
  · simpa using eq_of_szJ_mul_eq hXJ 1 2
  · simpa using eq_of_szJ_mul_eq hXJ 1 1
  · simpa using eq_of_szJ_mul_eq hXJ 1 0
  · simpa using eq_of_szJ_mul_eq hXJ 0 3
  · simpa using eq_of_szJ_mul_eq hXJ 0 2
  · simpa using eq_of_szJ_mul_eq hXJ 0 1
  · simpa using eq_of_szJ_mul_eq hXJ 0 0

private lemma inv_pow_facts (x : (F 1)ˣ) :
    ((x : F 1) ^ 2)⁻¹ = (x : F 1) ^ 5 ∧
      ((x : F 1) ^ 3)⁻¹ = (x : F 1) ^ 4 ∧
        ((x : F 1) ^ 4)⁻¹ = (x : F 1) ^ 3 ∧
          ((x : F 1) ^ 5)⁻¹ = (x : F 1) ^ 2 ∧
            ((x : F 1) ^ 6)⁻¹ = (x : F 1) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact inv_pow_val x (k := 2) (m := 5) (by norm_num)
  · exact inv_pow_val x (k := 3) (m := 4) (by norm_num)
  · exact inv_pow_val x (k := 4) (m := 3) (by norm_num)
  · exact inv_pow_val x (k := 5) (m := 2) (by norm_num)
  · simpa using inv_pow_val x (k := 6) (m := 1) (by norm_num)

private lemma unit_pow_seven_val (x : (F 1)ˣ) : (x : F 1) ^ 7 = 1 := by
  simpa using congrArg (fun w : (F 1)ˣ => (w : F 1)) (unit_pow_seven x)

private lemma torus_zero (X : Matrix (Fin 4) (Fin 4) (F 1)) (hXJ : szJ * X = X * szJ)
    (h1 : X 0 1 = 0) (h2 : X 0 2 = 0) (h3 : X 0 3 = 0) (h4 : X 1 0 = 0)
    (h6 : X 1 2 = 0) (h7 : X 1 3 = 0) :
    ∀ x : (F 1)ˣ, torusMat 1 x * (X - X 0 0 • (1 : Matrix (Fin 4) (Fin 4) (F 1))) =
      (X - X 0 0 • (1 : Matrix (Fin 4) (Fin 4) (F 1))) * torusMat 1 x := by
  intro x
  obtain ⟨e20, e21, e22, e23, e30, e31, e32, e33⟩ := szJ_symmetry X hXJ
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.sub_apply, Matrix.smul_apply, torusMat, Matrix.mul_apply, Fin.sum_univ_four,
      CharTwo.sub_eq_add, CharTwo.neg_eq, CharTwo.add_self_eq_zero,
      h1, h2, h3, h4, h6, h7, e20, e21, e22, e23, e30, e31, e32, e33]
  all_goals ring

private lemma torus_one (X : Matrix (Fin 4) (Fin 4) (F 1)) (hXJ : szJ * X = X * szJ)
    (h1 : X 0 1 = 0) (h3 : X 0 3 = 0) (h4 : X 1 0 = 0) (h6 : X 1 2 = 0)
    (h7 : X 1 3 = 0) (h05 : X 0 0 + X 1 1 = 0) :
    ∀ x : (F 1)ˣ, torusMat 1 x * (X - X 0 0 • (1 : Matrix (Fin 4) (Fin 4) (F 1))) =
      (X - X 0 0 • (1 : Matrix (Fin 4) (Fin 4) (F 1))) * torusMat 1 (x ^ 2 ^ 1) := by
  intro x
  have h05' : X 1 1 + X 0 0 = 0 := by rw [add_comm]; exact h05
  obtain ⟨e20, e21, e22, e23, e30, e31, e32, e33⟩ := szJ_symmetry X hXJ
  obtain ⟨hx2, hx3, hx4, hx5, hx6⟩ := inv_pow_facts x
  have hx7 := unit_pow_seven_val x
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.sub_apply, Matrix.smul_apply, torusMat, Matrix.mul_apply, Fin.sum_univ_four,
      CharTwo.sub_eq_add, CharTwo.neg_eq, CharTwo.add_self_eq_zero,
      h1, h3, h4, h6, h7, h05, h05', e20, e21, e22, e23, e30, e31, e32, e33,
      hx2, hx3, hx4, hx5, hx6, ← inv_pow]
  all_goals grind

private lemma torus_two (X : Matrix (Fin 4) (Fin 4) (F 1)) (hXJ : szJ * X = X * szJ)
    (h1 : X 0 1 = 0) (h2 : X 0 2 = 0) (h3 : X 0 3 = 0) (h4 : X 1 0 = 0)
    (h6 : X 1 2 = 0) (h05 : X 0 0 + X 1 1 = 0) :
    ∀ x : (F 1)ˣ, torusMat 1 x * (X - X 0 0 • (1 : Matrix (Fin 4) (Fin 4) (F 1))) =
      (X - X 0 0 • (1 : Matrix (Fin 4) (Fin 4) (F 1))) * torusMat 1 (x ^ 2 ^ 2) := by
  intro x
  have h05' : X 1 1 + X 0 0 = 0 := by rw [add_comm]; exact h05
  obtain ⟨e20, e21, e22, e23, e30, e31, e32, e33⟩ := szJ_symmetry X hXJ
  obtain ⟨hx2, hx3, hx4, hx5, hx6⟩ := inv_pow_facts x
  have hx7 := unit_pow_seven_val x
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.sub_apply, Matrix.smul_apply, torusMat, Matrix.mul_apply, Fin.sum_univ_four,
      CharTwo.sub_eq_add, CharTwo.neg_eq, CharTwo.add_self_eq_zero,
      h1, h2, h3, h4, h6, h05, h05', e20, e21, e22, e23, e30, e31, e32, e33,
      hx2, hx3, hx4, hx5, hx6, ← inv_pow]
  all_goals grind

private lemma units_pow_two_pow_mod_three (x : (F 1)ˣ) (c : ℕ) :
    x ^ 2 ^ c = x ^ 2 ^ (c % 3) := Units.ext (pow_two_pow_mod_three (x : F 1) c)

theorem IsTwistedCocycle.exists_diag_one
    (hY : IsTwistedCocycle (natHom 1) (twHom 1 c) Y)
    (hT : ∀ x, Y (torusSz 1 x) = 0) {X : Matrix (Fin 4) (Fin 4) (F 1)}
    (hXJ : wMat 1 * X = X * wMat 1)
    (hA : Y (rootSz 1 1 0) = rootMat 1 1 0 * X + X * rootMat 1 1 0) :
    ∃ D : Matrix (Fin 4) (Fin 4) (F 1),
      (∀ x : (F 1)ˣ, torusMat 1 x * D = D * torusMat 1 (x ^ 2 ^ c)) ∧
        wMat 1 * D = D * wMat 1 ∧
          Y (rootSz 1 1 0) = rootMat 1 1 0 * D + D * rootMat 1 1 0 := by
  obtain ⟨z, hz⟩ :=
    CFSG.SeitzReduction.RankOne.SzEight.exists_pow_three_eq_add_one (K := F 1) natCard_F_one
  have hXJ' : szJ * X = X * szJ := by simpa [szJ, wMat] using hXJ
  have hAmat : Y (rootSz 1 1 0) = AOf (X 0 0) (X 0 1) (X 0 2) (X 0 3)
      (X 1 0) (X 1 1) (X 1 2) (X 1 3) := by
    rw [show rootMat 1 1 0 = szX₀ from by rw [rootMat_one_zero]; rfl] at hA
    rw [hA]
    simpa [AOf] using szX₀_mul_add_mul_szX₀ hXJ'
  have hY' : IsTwistedCocycle (natHom 1) (twHom 1 (c % 3)) Y := by
    rw [← twHom_one_mod_three c]
    exact hY
  let D : Matrix (Fin 4) (Fin 4) (F 1) := X - X 0 0 • (1 : Matrix (Fin 4) (Fin 4) (F 1))
  refine ⟨D, ?_, ?_, ?_⟩
  · intro x
    have hc : c % 3 = 0 ∨ c % 3 = 1 ∨ c % 3 = 2 := by omega
    rcases hc with h0 | h1 | h2
    · have hY0 : IsTwistedCocycle (natHom 1) (twHom 1 0) Y := by simpa [h0] using hY'
      obtain ⟨h02, h03, h10, h13⟩ := relations_zero_a hY0 hT hz hAmat
      obtain ⟨h01, h12⟩ := relations_zero_b hY0 hT hz hAmat
      rw [units_pow_two_pow_mod_three x c, h0]
      simpa [D] using torus_zero X hXJ' h01 h02 h03 h10 h12 h13 x
    · have hY1 : IsTwistedCocycle (natHom 1) (twHom 1 1) Y := by simpa [h1] using hY'
      obtain h10 := relations_one_a hY1 hT hz hAmat
      obtain ⟨h01, h03, h12⟩ := relations_one_b hY1 hT hz hAmat
      obtain ⟨h13, h05⟩ := relations_one_c hY1 hT hz hAmat
      rw [units_pow_two_pow_mod_three x c, h1]
      simpa [D] using torus_one X hXJ' h01 h03 h10 h12 h13 h05 x
    · have hY2 : IsTwistedCocycle (natHom 1) (twHom 1 2) Y := by simpa [h2] using hY'
      obtain ⟨h02, h03, h10, h12⟩ := relations_two_a hY2 hT hz hAmat
      obtain h01 := relations_two_b hY2 hT hz hAmat
      obtain h05 := relations_two_c hY2 hT hz hAmat
      rw [units_pow_two_pow_mod_three x c, h2]
      simpa [D] using torus_two X hXJ' h01 h02 h03 h10 h12 h05 x
  · simp [D, Matrix.mul_sub, Matrix.sub_mul, hXJ]
  · rw [hA]
    symm
    have hs : X 0 0 • rootMat 1 1 0 + X 0 0 • rootMat 1 1 0 = 0 :=
      CharTwo.add_self_eq_zero _
    calc
      rootMat 1 1 0 * D + D * rootMat 1 1 0
          = rootMat 1 1 0 * X - X 0 0 • rootMat 1 1 0 +
              (X * rootMat 1 1 0 - X 0 0 • rootMat 1 1 0) := by
            simp [D, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul]
      _ = rootMat 1 1 0 * X + X * rootMat 1 1 0 -
            (X 0 0 • rootMat 1 1 0 + X 0 0 • rootMat 1 1 0) := by
            abel
      _ = rootMat 1 1 0 * X + X * rootMat 1 1 0 := by rw [hs, sub_zero]

end CFSG.RepresentationTheory.SzMartineau

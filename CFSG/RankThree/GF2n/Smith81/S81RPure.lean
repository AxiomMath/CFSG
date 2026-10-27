module

public import CFSG.RankThree.GF2n.Smith81.S81A5Root

open exteriorPower Matrix

public section

namespace CFSG.RankThree.GF2n.Smith81.A5Cube

variable {K : Type*} [Field K]

private theorem m3_shift_snd_fst (c : K) (x y w : Fin 6 → K) :
    ιMulti K 3 ![x, y + c • x, w] = ιMulti K 3 ![x, y, w] := by
  simp only [ι3_add_snd, ι3_smul_snd, ι3_eq_fst_snd, smul_zero, add_zero]

private theorem m3_shift_thd_fst (c : K) (x y w : Fin 6 → K) :
    ιMulti K 3 ![x, y, w + c • x] = ιMulti K 3 ![x, y, w] := by
  simp only [ι3_add_thd, ι3_smul_thd, ι3_eq_fst_thd, smul_zero, add_zero]

private theorem m3_shift_fst_snd (c : K) (x y w : Fin 6 → K) :
    ιMulti K 3 ![x + c • y, y, w] = ιMulti K 3 ![x, y, w] := by
  simp only [ι3_add_fst, ι3_smul_fst, ι3_eq_fst_snd, smul_zero, add_zero]

private theorem m3_shift_thd_snd (c : K) (x y w : Fin 6 → K) :
    ιMulti K 3 ![x, y, w + c • y] = ιMulti K 3 ![x, y, w] := by
  simp only [ι3_add_thd, ι3_smul_thd, ι3_eq_snd_thd, smul_zero, add_zero]

private theorem m3_shift_fst_thd (c : K) (x y z : Fin 6 → K) :
    ιMulti K 3 ![x + c • z, y, z] = ιMulti K 3 ![x, y, z] := by
  simp only [ι3_add_fst, ι3_smul_fst, ι3_eq_fst_thd, smul_zero, add_zero]

private theorem m3_shift_snd_thd (c : K) (x y z : Fin 6 → K) :
    ιMulti K 3 ![x, y + c • z, z] = ιMulti K 3 ![x, y, z] := by
  simp only [ι3_add_snd, ι3_smul_snd, ι3_eq_snd_thd, smul_zero, add_zero]

private theorem m3_formula {g : GL (Fin 6) K} {a f : Fin 6 → K}
    (hN : (g : Matrix (Fin 6) (Fin 6) K) = 1 + vecMulVec a f) (x0 x1 x2 : Fin 6 → K) :
    (rho K g - 1) (ιMulti K 3 ![x0, x1, x2]) =
      (f ⬝ᵥ x0) • ιMulti K 3 ![a, x1, x2] + (f ⬝ᵥ x1) • ιMulti K 3 ![x0, a, x2] +
        (f ⬝ᵥ x2) • ιMulti K 3 ![x0, x1, a] := by
  rw [LinearMap.sub_apply, Module.End.one_apply]
  exact rho_sub_one_ιMulti hN x0 x1 x2

private theorem m3_core0 {g : GL (Fin 6) K} {a f : Fin 6 → K}
    (hN : (g : Matrix (Fin 6) (Fin 6) K) = 1 + vecMulVec a f) {x0 x1 x2 : Fin 6 → K}
    (h1 : f ⬝ᵥ x1 = 0) (h2 : f ⬝ᵥ x2 = 0) :
    (rho K g - 1) (ιMulti K 3 ![x0, x1, x2]) = (f ⬝ᵥ x0) • ιMulti K 3 ![a, x1, x2] := by
  rw [m3_formula hN, h1, h2]
  simp

private theorem m3_core1 {g : GL (Fin 6) K} {a f : Fin 6 → K}
    (hN : (g : Matrix (Fin 6) (Fin 6) K) = 1 + vecMulVec a f) {x0 x1 x2 : Fin 6 → K}
    (h0 : f ⬝ᵥ x0 = 0) (h2 : f ⬝ᵥ x2 = 0) :
    (rho K g - 1) (ιMulti K 3 ![x0, x1, x2]) = (f ⬝ᵥ x1) • ιMulti K 3 ![x0, a, x2] := by
  rw [m3_formula hN, h0, h2]
  simp

private theorem m3_core2 {g : GL (Fin 6) K} {a f : Fin 6 → K}
    (hN : (g : Matrix (Fin 6) (Fin 6) K) = 1 + vecMulVec a f) {x0 x1 x2 : Fin 6 → K}
    (h0 : f ⬝ᵥ x0 = 0) (h1 : f ⬝ᵥ x1 = 0) :
    (rho K g - 1) (ιMulti K 3 ![x0, x1, x2]) = (f ⬝ᵥ x2) • ιMulti K 3 ![x0, x1, a] := by
  rw [m3_formula hN, h0, h1]
  simp

private theorem m3_dot_shift (f x y : Fin 6 → K) (h : f ⬝ᵥ x ≠ 0) :
    f ⬝ᵥ (y + (-((f ⬝ᵥ y) / (f ⬝ᵥ x))) • x) = 0 := by
  rw [dotProduct_add, dotProduct_smul, smul_eq_mul, neg_mul, div_mul_cancel₀ _ h]
  ring

private theorem m3_exists_pivot0 {f x0 : Fin 6 → K} (x1 x2 : Fin 6 → K) (h0 : f ⬝ᵥ x0 ≠ 0) :
    ∃ y1 y2 : Fin 6 → K, f ⬝ᵥ y1 = 0 ∧ f ⬝ᵥ y2 = 0 ∧
      ιMulti K 3 ![x0, x1, x2] = ιMulti K 3 ![x0, y1, y2] :=
  ⟨x1 + (-((f ⬝ᵥ x1) / (f ⬝ᵥ x0))) • x0, x2 + (-((f ⬝ᵥ x2) / (f ⬝ᵥ x0))) • x0,
    m3_dot_shift f x0 x1 h0, m3_dot_shift f x0 x2 h0,
    by rw [m3_shift_snd_fst, m3_shift_thd_fst]⟩

private theorem m3_exists_pivot1 {f x1 : Fin 6 → K} (x0 x2 : Fin 6 → K) (h1 : f ⬝ᵥ x1 ≠ 0) :
    ∃ y0 y2 : Fin 6 → K, f ⬝ᵥ y0 = 0 ∧ f ⬝ᵥ y2 = 0 ∧
      ιMulti K 3 ![x0, x1, x2] = ιMulti K 3 ![y0, x1, y2] :=
  ⟨x0 + (-((f ⬝ᵥ x0) / (f ⬝ᵥ x1))) • x1, x2 + (-((f ⬝ᵥ x2) / (f ⬝ᵥ x1))) • x1,
    m3_dot_shift f x1 x0 h1, m3_dot_shift f x1 x2 h1,
    by rw [m3_shift_fst_snd, m3_shift_thd_snd]⟩

private theorem m3_exists_pivot2 {f x2 : Fin 6 → K} (x0 x1 : Fin 6 → K) (h2 : f ⬝ᵥ x2 ≠ 0) :
    ∃ y0 y1 : Fin 6 → K, f ⬝ᵥ y0 = 0 ∧ f ⬝ᵥ y1 = 0 ∧
      ιMulti K 3 ![x0, x1, x2] = ιMulti K 3 ![y0, y1, x2] :=
  ⟨x0 + (-((f ⬝ᵥ x0) / (f ⬝ᵥ x2))) • x2, x1 + (-((f ⬝ᵥ x1) / (f ⬝ᵥ x2))) • x2,
    m3_dot_shift f x2 x0 h2, m3_dot_shift f x2 x1 h2,
    by rw [m3_shift_fst_thd, m3_shift_snd_thd]⟩

private theorem m3_pure_pivot0 {g : GL (Fin 6) K} {a f : Fin 6 → K}
    (hN : (g : Matrix (Fin 6) (Fin 6) K) = 1 + vecMulVec a f) {x0 : Fin 6 → K}
    (x1 x2 : Fin 6 → K) (h0 : f ⬝ᵥ x0 ≠ 0) :
    IsPure K ((rho K g - 1) (ιMulti K 3 ![x0, x1, x2])) := by
  obtain ⟨y1, y2, hy1, hy2, hι⟩ := m3_exists_pivot0 x1 x2 h0
  rw [hι, m3_core0 hN hy1 hy2]
  exact ⟨![(f ⬝ᵥ x0) • a, y1, y2], (ι3_smul_fst _ _ _ _).symm⟩

private theorem m3_pure_pivot1 {g : GL (Fin 6) K} {a f : Fin 6 → K}
    (hN : (g : Matrix (Fin 6) (Fin 6) K) = 1 + vecMulVec a f) {x1 : Fin 6 → K}
    (x0 x2 : Fin 6 → K) (h1 : f ⬝ᵥ x1 ≠ 0) :
    IsPure K ((rho K g - 1) (ιMulti K 3 ![x0, x1, x2])) := by
  obtain ⟨y0, y2, hy0, hy2, hι⟩ := m3_exists_pivot1 x0 x2 h1
  rw [hι, m3_core1 hN hy0 hy2]
  exact ⟨![y0, (f ⬝ᵥ x1) • a, y2], (ι3_smul_snd _ _ _ _).symm⟩

private theorem m3_pure_pivot2 {g : GL (Fin 6) K} {a f : Fin 6 → K}
    (hN : (g : Matrix (Fin 6) (Fin 6) K) = 1 + vecMulVec a f) {x2 : Fin 6 → K}
    (x0 x1 : Fin 6 → K) (h2 : f ⬝ᵥ x2 ≠ 0) :
    IsPure K ((rho K g - 1) (ιMulti K 3 ![x0, x1, x2])) := by
  obtain ⟨y0, y1, hy0, hy1, hι⟩ := m3_exists_pivot2 x0 x1 h2
  rw [hι, m3_core2 hN hy0 hy1]
  exact ⟨![y0, y1, (f ⬝ᵥ x2) • a], (ι3_smul_thd _ _ _ _).symm⟩

theorem isPure_rho_sub_one {g : GL (Fin 6) K} (hg : IsTransvec K g) {p : Cube K}
    (hp : IsPure K p) : IsPure K ((rho K g - 1) p) := by
  obtain ⟨a, f, -, -, -, hN⟩ := IsTransvec.exists hg
  obtain ⟨v, rfl⟩ := hp
  obtain ⟨x0, x1, x2, rfl⟩ : ∃ x0 x1 x2 : Fin 6 → K, v = ![x0, x1, x2] :=
    ⟨v 0, v 1, v 2, by funext i; fin_cases i <;> rfl⟩
  by_cases h0 : f ⬝ᵥ x0 = 0
  · by_cases h1 : f ⬝ᵥ x1 = 0
    · by_cases h2 : f ⬝ᵥ x2 = 0
      · rw [m3_core0 hN h1 h2, h0, zero_smul]
        exact isPure_zero
      · exact m3_pure_pivot2 hN x0 x1 h2
    · exact m3_pure_pivot1 hN x0 x2 h1
  · exact m3_pure_pivot0 hN x1 x2 h0

end CFSG.RankThree.GF2n.Smith81.A5Cube

module

public import CFSG.RankThree.PartTwo.Sec4.LThreePiDefs

public section

namespace CFSG.RankThree.PartTwo.Sec14.Ronan148W

open CFSG.RankThree.PartTwo.Sec4 Matrix CFSG.LocalAnalysis.ComponentInitial

variable {K : Type} [Field K]

@[expose] def TrOne {p f : ℕ} (h : UnitaryFieldData p f K) : Set (Matrix (Fin 2) (Fin 2) K) :=
  {X | (X.map h.bar)ᵀ * X = 1 ∧ X.det = 1 ∧ X.trace = 1}

theorem eta_fin_two' (X : Matrix (Fin 2) (Fin 2) K) : X = !![X 0 0, X 0 1; X 1 0, X 1 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

theorem TrOne.pow_three [CharP K 2] {p f : ℕ} {h : UnitaryFieldData p f K}
    {X : Matrix (Fin 2) (Fin 2) K} (hX : X ∈ TrOne h) : X ^ 3 = 1 := by
  obtain ⟨-, hdet, htr⟩ := hX
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  rw [Matrix.det_fin_two] at hdet
  rw [Matrix.trace_fin_two] at htr
  have hsq : X * X = X + 1 := by
    rw [eta_fin_two' X]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
    · linear_combination X 0 0 * htr - hdet - h2
    · linear_combination X 0 1 * htr
    · linear_combination X 1 0 * htr
    · linear_combination X 1 1 * htr - hdet - h2
  have hXX : X + X = 0 := by rw [← two_smul K X, h2, zero_smul]
  calc X ^ 3 = X * X * X := pow_three' X
    _ = (X + 1) * X := by rw [hsq]
    _ = X * X + X := by rw [add_mul, one_mul]
    _ = X + 1 + X := by rw [hsq]
    _ = 1 := by rw [add_comm X 1, add_assoc, hXX, add_zero]

theorem bar_cube_root (h : UnitaryFieldData 2 3 K) {ε : K} (hε3 : ε ^ 3 = 1) :
    h.bar ε = ε ^ 2 := by
  rw [h.bar_apply, show (2 : ℕ) ^ 3 = 3 * 2 + 2 from rfl, pow_add, pow_mul, hε3, one_pow, one_mul]

theorem not_three_dvd_card_trOne [Finite K] [CharP K 2] (h : UnitaryFieldData 2 3 K) {ε : K}
    (hε3 : ε ^ 3 = 1) (hε1 : ε ≠ 1) : ¬ 3 ∣ Nat.card (TrOne h) := by
  classical
  have := Fintype.ofFinite (TrOne h)
  have hε0 : ε ≠ 0 := by rintro rfl; simp at hε3
  have hbar := bar_cube_root h hε3
  have hbar2 : h.bar (ε ^ 2) = ε := by
    rw [map_pow, hbar, ← pow_mul, show 2 * 2 = 3 + 1 from rfl, pow_add, hε3, one_mul, pow_one]
  have hsum : ε ^ 2 + ε + 1 = 0 := by
    have : (ε - 1) * (ε ^ 2 + ε + 1) = 0 := by linear_combination hε3
    exact (mul_eq_zero.mp this).resolve_left (sub_ne_zero.mpr hε1)
  set D : Matrix (Fin 2) (Fin 2) K := diagonal ![1, ε] with hD
  set D' : Matrix (Fin 2) (Fin 2) K := diagonal ![1, ε ^ 2] with hD'
  have hDD' : D * D' = 1 := by
    rw [hD, hD', diagonal_mul_diagonal, ← diagonal_one]
    congr 1
    funext i
    fin_cases i <;> simp [← pow_succ', hε3]
  have hD'D : D' * D = 1 := by
    rw [hD, hD', diagonal_mul_diagonal, ← diagonal_one]
    congr 1
    funext i
    fin_cases i <;> simp [← pow_succ, hε3]
  have hDbar : (D.map h.bar)ᵀ = D' := by
    rw [hD, hD', diagonal_map (map_zero _), diagonal_transpose]
    congr 1
    funext i
    fin_cases i <;> simp [hbar]
  have hD'bar : (D'.map h.bar)ᵀ = D := by
    rw [hD, hD', diagonal_map (map_zero _), diagonal_transpose]
    congr 1
    funext i
    fin_cases i <;> simp [hbar2]
  have hdetD : D.det * D'.det = 1 := by rw [← det_mul, hDD', det_one]
  have hmaps : ∀ X ∈ TrOne h, D * X * D' ∈ TrOne h := by
    rintro X ⟨hu, hdet, htr⟩
    refine ⟨?_, ?_, ?_⟩
    · rw [Matrix.map_mul, Matrix.map_mul, Matrix.transpose_mul, Matrix.transpose_mul, hD'bar,
        hDbar]
      calc D * ((X.map h.bar)ᵀ * D') * (D * X * D') =
          D * ((X.map h.bar)ᵀ * (D' * D) * X) * D' := by simp only [Matrix.mul_assoc]
        _ = 1 := by rw [hD'D, Matrix.mul_one, hu, Matrix.mul_one, hDD']
    · rw [det_mul, det_mul, hdet, mul_one, hdetD]
    · rw [Matrix.trace_mul_cycle, hD'D, Matrix.one_mul, htr]
  let π₀ : Function.End (TrOne h) := fun X => ⟨D * X * D', hmaps X X.2⟩
  have hπ₀3 : π₀ ^ 3 ^ 1 = 1 := by
    funext X
    apply Subtype.ext
    change D * (D * (D * (X : Matrix (Fin 2) (Fin 2) K) * D') * D') * D' = X
    have hD3 : D * (D * D) = 1 := by
      rw [hD, diagonal_mul_diagonal, diagonal_mul_diagonal, ← diagonal_one]
      congr 1
      funext i
      fin_cases i <;> simp [← pow_succ, ← pow_succ', hε3]
      · rw [← pow_two, ← pow_succ', hε3]
    have hD'eq : D' = D * D := by
      calc D' = D' * (D * (D * D)) := by rw [hD3, Matrix.mul_one]
        _ = (D' * D) * (D * D) := by simp only [Matrix.mul_assoc]
        _ = D * D := by rw [hD'D, Matrix.one_mul]
    have hD'3 : D' * (D' * D') = 1 := by
      rw [hD'eq]
      calc D * D * (D * D * (D * D)) = (D * (D * D)) * (D * (D * D)) := by
            simp only [Matrix.mul_assoc]
        _ = 1 := by rw [hD3, Matrix.one_mul]
    calc D * (D * (D * (X : Matrix (Fin 2) (Fin 2) K) * D') * D') * D' =
        (D * (D * D)) * X * (D' * (D' * D')) := by simp only [Matrix.mul_assoc]
      _ = X := by rw [hD3, hD'3, Matrix.one_mul, Matrix.mul_one]
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have hdiag : ∀ x : K, x ^ 2 + x + 1 = 0 → !![x, 0; 0, x ^ 2] ∈ TrOne h := by
    intro x hx
    have hx3 : x ^ 3 = 1 := by linear_combination (x - 1) * hx
    have hbx : h.bar x = x ^ 2 := bar_cube_root h hx3
    have hbx2 : h.bar (x ^ 2) = x := by
      rw [map_pow, hbx, ← pow_mul, show 2 * 2 = 3 + 1 from rfl, pow_add, hx3, one_mul, pow_one]
    refine ⟨?_, ?_, ?_⟩
    · ext i j
      fin_cases i <;> fin_cases j <;>
        simp [Matrix.mul_apply, Fin.sum_univ_two, hbx, hbx2, ← pow_succ, ← pow_succ', hx3]
    · rw [Matrix.det_fin_two_of, ← pow_succ', hx3, mul_zero, sub_zero]
    · rw [Matrix.trace_fin_two_of]
      linear_combination hx - h2
  have hεroot : ε ^ 2 + ε + 1 = 0 := hsum
  have hε2root : (ε ^ 2) ^ 2 + ε ^ 2 + 1 = 0 := by
    linear_combination hsum + ε * hε3
  set X₁ : TrOne h := ⟨!![ε, 0; 0, ε ^ 2], hdiag ε hεroot⟩ with hX₁
  set X₂ : TrOne h := ⟨!![ε ^ 2, 0; 0, (ε ^ 2) ^ 2], hdiag (ε ^ 2) hε2root⟩ with hX₂
  have hfix_iff : ∀ X : TrOne h, Function.IsFixedPt π₀ X ↔ X = X₁ ∨ X = X₂ := by
    intro X
    constructor
    · intro hX
      have hm : D * (X : Matrix (Fin 2) (Fin 2) K) * D' = X := congrArg Subtype.val hX
      have hcomm : D * (X : Matrix (Fin 2) (Fin 2) K) = X * D := by
        calc D * (X : Matrix (Fin 2) (Fin 2) K) = D * X * (D' * D) := by
              rw [hD'D, Matrix.mul_one]
          _ = (D * X * D') * D := by simp only [Matrix.mul_assoc]
          _ = X * D := by rw [hm]
      have h01 := congrFun (congrFun hcomm 0) 1
      have h10 := congrFun (congrFun hcomm 1) 0
      rw [hD, Matrix.diagonal_mul, Matrix.mul_diagonal] at h01 h10
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, one_mul,
        mul_one] at h01 h10
      have hb : (X : Matrix (Fin 2) (Fin 2) K) 0 1 = 0 := by
        have : (X : Matrix (Fin 2) (Fin 2) K) 0 1 * (ε - 1) = 0 := by linear_combination -h01
        exact (mul_eq_zero.mp this).resolve_right (sub_ne_zero.mpr hε1)
      have hc : (X : Matrix (Fin 2) (Fin 2) K) 1 0 = 0 := by
        have : (X : Matrix (Fin 2) (Fin 2) K) 1 0 * (ε - 1) = 0 := by linear_combination h10
        exact (mul_eq_zero.mp this).resolve_right (sub_ne_zero.mpr hε1)
      obtain ⟨-, hdet, htr⟩ := X.2
      rw [Matrix.det_fin_two, hb, hc] at hdet
      rw [Matrix.trace_fin_two] at htr
      set a := (X : Matrix (Fin 2) (Fin 2) K) 0 0 with ha
      set d := (X : Matrix (Fin 2) (Fin 2) K) 1 1 with hd
      have hd' : d = a + 1 := by linear_combination htr - h2 * a
      have hroot : (a - ε) * (a - ε ^ 2) = 0 := by
        rw [hd'] at hdet
        linear_combination hdet + (a + 1) * h2 - a * h2 + hε3 - a * hsum
      have hXe : (X : Matrix (Fin 2) (Fin 2) K) = !![a, 0; 0, d] := by
        rw [eta_fin_two' (X : Matrix (Fin 2) (Fin 2) K), hb, hc]
      have hdsq : ∀ x : K, x ^ 2 + x + 1 = 0 → x + 1 = x ^ 2 := fun x hx => by
        linear_combination -hx + h2 * (x + 1)
      rcases mul_eq_zero.mp hroot with h1 | h1
      · left
        apply Subtype.ext
        change (X : Matrix (Fin 2) (Fin 2) K) = !![ε, 0; 0, ε ^ 2]
        rw [hXe, hd', sub_eq_zero.mp h1, hdsq ε hsum]
      · right
        apply Subtype.ext
        change (X : Matrix (Fin 2) (Fin 2) K) = !![ε ^ 2, 0; 0, (ε ^ 2) ^ 2]
        rw [hXe, hd', sub_eq_zero.mp h1, hdsq (ε ^ 2) hε2root]
    · rintro (rfl | rfl)
      · apply Subtype.ext
        change D * !![ε, 0; 0, ε ^ 2] * D' = !![ε, 0; 0, ε ^ 2]
        rw [hD, hD']
        ext i j
        fin_cases i <;> fin_cases j <;>
          simp [Matrix.mul_apply, Fin.sum_univ_two, ← pow_succ, ← pow_succ', hε3]
      · apply Subtype.ext
        change D * !![ε ^ 2, 0; 0, (ε ^ 2) ^ 2] * D' = !![ε ^ 2, 0; 0, (ε ^ 2) ^ 2]
        rw [hD, hD']
        have e11 : ε * (ε ^ 2) ^ 2 * ε ^ 2 = (ε ^ 2) ^ 2 := by
          linear_combination (ε ^ 2) ^ 2 * hε3
        ext i j
        fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, e11]
  have hne : X₁ ≠ X₂ := by
    intro h12
    have := congrFun (congrFun (congrArg Subtype.val h12) 0) 0
    change ε = ε ^ 2 at this
    apply hε1
    have h' : ε * (ε - 1) = 0 := by linear_combination -this
    exact sub_eq_zero.mp ((mul_eq_zero.mp h').resolve_left hε0)
  have hset : Function.fixedPoints π₀ = {X₁, X₂} := by
    ext X
    rw [Function.mem_fixedPoints, Set.mem_insert_iff, Set.mem_singleton_iff]
    exact hfix_iff X
  have hcard2 : Fintype.card (Function.fixedPoints π₀) = 2 := by
    rw [← Nat.card_eq_fintype_card, hset, Nat.card_coe_set_eq, Set.ncard_pair hne]
  have hmod := Equiv.Perm.card_fixedPoints_modEq (p := 3) (n := 1) (hp := ⟨Nat.prime_three⟩) hπ₀3
  rw [hcard2] at hmod
  rw [Nat.card_eq_fintype_card]
  intro h3
  have := Nat.ModEq.symm hmod
  unfold Nat.ModEq at this
  omega

end CFSG.RankThree.PartTwo.Sec14.Ronan148W

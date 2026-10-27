module

public import CFSG.RankThree.PartTwo.Sec19.Item19Res6ProofSeitzExact
public import CFSG.LieType.SeitzGeneration.UnitaryOuterB12

public section

namespace CFSG.RankThree.PartTwo.Sec19

open Matrix CFSG.LieType.SeitzGeneration CFSG.LocalAnalysis.ComponentInitial
  CFSG.ClassicalGroups.UnitaryFlag

theorem pow_mul_eq_smul_mul_pow {K : Type} [Field K] {X M : Matrix (Fin 3) (Fin 3) K} {d : K}
    (hXM : X * M = d • (M * X)) (m : ℕ) : X ^ m * M = d ^ m • (M * X ^ m) := by
  induction m with
  | zero => simp
  | succ m ih =>
    calc X ^ (m + 1) * M = X ^ m * (X * M) := by rw [pow_succ, Matrix.mul_assoc]
      _ = X ^ m * (d • (M * X)) := by rw [hXM]
      _ = d • (X ^ m * (M * X)) := by rw [Matrix.mul_smul]
      _ = d • ((X ^ m * M) * X) := by rw [Matrix.mul_assoc]
      _ = d • ((d ^ m • (M * X ^ m)) * X) := by rw [ih]
      _ = d • (d ^ m • (M * X ^ m * X)) := by rw [Matrix.smul_mul]
      _ = d ^ (m + 1) • (M * X ^ (m + 1)) := by
          rw [smul_smul, pow_succ' d m, pow_succ X m, ← Matrix.mul_assoc]

theorem mul_comm_of_smul {K : Type} [Field K] {g X M : Matrix (Fin 3) (Fin 3) K} {c d : K}
    (hgM : g * M = c • (M * g)) (hXM : X * M = d • (M * X)) (hcd : c * d = 1) :
    (g * X) * M = M * (g * X) := by
  calc (g * X) * M = g * (X * M) := by rw [Matrix.mul_assoc]
    _ = g * (d • (M * X)) := by rw [hXM]
    _ = d • (g * (M * X)) := by rw [Matrix.mul_smul]
    _ = d • ((g * M) * X) := by rw [Matrix.mul_assoc]
    _ = d • ((c • (M * g)) * X) := by rw [hgM]
    _ = d • (c • ((M * g) * X)) := by rw [Matrix.smul_mul]
    _ = (c * d) • (M * (g * X)) := by rw [smul_smul, mul_comm d c, Matrix.mul_assoc]
    _ = M * (g * X) := by rw [hcd, one_smul]

theorem fixU_le_exactClosure_of_shift {ℓ f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData ℓ f K)
    (hq3 : 3 ∣ ℓ ^ f + 1) {ω α : K} (hω : IsPrimitiveRoot ω 3) (hα : α ^ (ℓ ^ f + 1) = 1)
    {s : unitarySU ℓ f K 3} (hs : ((s : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = hS)
    (hsQ : s ∈ Subgroup.closure (outerHeisExactFix ℓ f K ω α)) :
    outerHeisClosure ℓ f K ω α ≤ Subgroup.closure (outerHeisExactFix ℓ f K ω α) := by
  have hω3 : ω ^ 3 = 1 := hω.pow_eq_one
  have hω0 : ω ≠ 0 := hω.ne_zero (by norm_num)
  have h3 : ω * ω ^ 2 = 1 := by rw [show ω * ω ^ 2 = ω ^ 3 by ring]; exact hω3
  have hα0 : α ≠ 0 := by
    rintro rfl
    have hq1 : ℓ ^ f + 1 ≠ 0 := by omega
    rw [zero_pow hq1] at hα
    exact zero_ne_one hα
  have hdetL : ∀ M ∈ outerHeisLines ω α, M.det ≠ 0 := by
    intro M hM
    simp only [outerHeisLines, Set.mem_insert_iff, Set.mem_singleton_iff] at hM
    rcases hM with rfl | rfl | rfl | rfl
    · rw [det_heisC_gen]; exact hα0
    · rw [det_heisD]; exact pow_ne_zero _ hω0
    · rw [Matrix.det_mul, det_heisC_gen, det_heisD]
      exact mul_ne_zero hα0 (pow_ne_zero _ hω0)
    · rw [Matrix.det_mul, det_heisC_gen, Matrix.det_pow, det_heisD]
      exact mul_ne_zero hα0 (pow_ne_zero _ (pow_ne_zero _ hω0))
  have hc3 : ∀ (A M : Matrix (Fin 3) (Fin 3) K) (c : K), A.det = 1 → M.det ≠ 0 →
      A * M = c • (M * A) → c ^ 3 = 1 := by
    intro A M c hA hM hAM
    have h1 := congrArg Matrix.det hAM
    rw [Matrix.det_mul, Matrix.det_smul, Matrix.det_mul, hA, Fintype.card_fin] at h1
    apply mul_left_cancel₀ hM
    linear_combination -h1
  have hdet1 : ∀ g : unitarySU ℓ f K 3,
      ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).det = 1 :=
    fun g => ((mem_unitarySU_iff h).1 g.2).1
  have hD' : heisD ω = !![1, 0, 0; 0, ω, 0; 0, 0, ω ^ 2] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [heisD]
  have hDC : heisD ω * heisC α = ω • (heisC α * heisD ω) := by
    rw [hD']
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [heisC, Matrix.mul_apply, Fin.sum_univ_three] <;> grind
  have hDCD : heisD ω * (heisC α * heisD ω) = ω • ((heisC α * heisD ω) * heisD ω) := by
    rw [← Matrix.mul_assoc, hDC, Matrix.smul_mul]
  have hDD2 : heisD ω * heisD ω ^ 2 = heisD ω ^ 2 * heisD ω :=
    (Commute.self_pow (heisD ω) 2).eq
  have hDCD2 : heisD ω * (heisC α * heisD ω ^ 2) =
      ω • ((heisC α * heisD ω ^ 2) * heisD ω) := by
    rw [← Matrix.mul_assoc, hDC, Matrix.smul_mul]
    simp only [Matrix.mul_assoc, hDD2]
  have hSD : hS * heisD ω = (ω ^ 2) • (heisD ω * hS) := by
    rw [hD']
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [hS, Matrix.mul_apply, Fin.sum_univ_three] <;> grind
  have hmC : heisC α ∈ outerHeisLines ω α := by simp [outerHeisLines]
  have hmD : heisD ω ∈ outerHeisLines ω α := by simp [outerHeisLines]
  have hmCD : heisC α * heisD ω ∈ outerHeisLines ω α := by simp [outerHeisLines]
  have hmCD2 : heisC α * heisD ω ^ 2 ∈ outerHeisLines ω α := by simp [outerHeisLines]
  obtain ⟨Ds, hDs⟩ := CFSG.RankThree.PartTwo.Sec19.exists_heisD_su h hq3 hω
  have hDQ : Ds ∈ Subgroup.closure (outerHeisExactFix ℓ f K ω α) :=
    Subgroup.subset_closure ⟨heisD ω, hmD, by rw [hDs]⟩
  have hDpow : ∀ m : ℕ, (((Ds ^ m : unitarySU ℓ f K 3) : GL (Fin 3) K) :
      Matrix (Fin 3) (Fin 3) K) = heisD ω ^ m := by
    intro m
    rw [Subgroup.coe_pow, Units.val_pow_eq_pow_val, hDs]
  have hfin : ∀ (g X : unitarySU ℓ f K 3) (M : Matrix (Fin 3) (Fin 3) K) (c d : K),
      M ∈ outerHeisLines ω α → X ∈ Subgroup.closure (outerHeisExactFix ℓ f K ω α) →
      ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * M =
        c • (M * ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) →
      ((X : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * M =
        d • (M * ((X : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) →
      c * d = 1 → g ∈ Subgroup.closure (outerHeisExactFix ℓ f K ω α) := by
    intro g X M c d hM hX hgM hXM hcd
    have ht : (((g * X : unitarySU ℓ f K 3) : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
        ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
          ((X : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) := by
      rw [Subgroup.coe_mul, Units.val_mul]
    have htQ : g * X ∈ Subgroup.closure (outerHeisExactFix ℓ f K ω α) := by
      apply Subgroup.subset_closure
      refine ⟨M, hM, ?_⟩
      rw [ht]
      exact mul_comm_of_smul hgM hXM hcd
    have hgX := mul_mem htQ (inv_mem hX)
    rwa [mul_inv_cancel_right] at hgX
  have hcdA : ∀ i : ℕ, i < 3 → ω ^ i * ω ^ (3 - i) = 1 := by
    intro i hi
    rw [← pow_add, show i + (3 - i) = 3 by omega, hω3]
  have hcdD : ∀ m : ℕ, ω ^ m * (ω ^ 2) ^ m = 1 := by
    intro m
    rw [← mul_pow, h3, one_pow]
  have hsPow : ∀ m : ℕ, (((s ^ m : unitarySU ℓ f K 3) : GL (Fin 3) K) :
      Matrix (Fin 3) (Fin 3) K) = hS ^ m := by
    intro m
    rw [Subgroup.coe_pow, Units.val_pow_eq_pow_val, hs]
  have hpowD : ∀ m : ℕ, Ds ^ m ∈ Subgroup.closure (outerHeisExactFix ℓ f K ω α) :=
    fun m => pow_mem hDQ m
  have hpows : ∀ m : ℕ, s ^ m ∈ Subgroup.closure (outerHeisExactFix ℓ f K ω α) :=
    fun m => pow_mem hsQ m
  unfold outerHeisClosure
  rw [Subgroup.closure_le]
  rintro g ⟨M, hM, hgF⟩
  obtain ⟨c, hgM⟩ := hgF
  have hc3' : c ^ 3 = 1 := hc3 _ _ _ (hdet1 g) (hdetL M hM) hgM
  obtain ⟨i, hi, hci⟩ := hω.eq_pow_of_pow_eq_one hc3'
  subst hci
  simp only [outerHeisLines, Set.mem_insert_iff, Set.mem_singleton_iff] at hM
  rcases hM with rfl | rfl | rfl | rfl
  · exact hfin g (Ds ^ (3 - i)) (heisC α) (ω ^ i) (ω ^ (3 - i)) hmC (hpowD _) hgM
      (by rw [hDpow]; exact pow_mul_eq_smul_mul_pow hDC (3 - i)) (hcdA i hi)
  · exact hfin g (s ^ i) (heisD ω) (ω ^ i) ((ω ^ 2) ^ i) hmD (hpows i) hgM
      (by rw [hsPow]; exact pow_mul_eq_smul_mul_pow hSD i) (hcdD i)
  · exact hfin g (Ds ^ (3 - i)) (heisC α * heisD ω) (ω ^ i) (ω ^ (3 - i)) hmCD (hpowD _) hgM
      (by rw [hDpow]; exact pow_mul_eq_smul_mul_pow hDCD (3 - i)) (hcdA i hi)
  · exact hfin g (Ds ^ (3 - i)) (heisC α * heisD ω ^ 2) (ω ^ i) (ω ^ (3 - i)) hmCD2
      (hpowD _) hgM (by rw [hDpow]; exact pow_mul_eq_smul_mul_pow hDCD2 (3 - i)) (hcdA i hi)

end CFSG.RankThree.PartTwo.Sec19

end

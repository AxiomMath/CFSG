module

public import CFSG.Quasithin.Background.SmithB45LnL5Adj
public import CFSG.Quasithin.Background.SmithB45LnL5Cells

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Quasithin.B45L5

open Matrix CFSG.Quasithin.JonesParshall CFSG.Quasithin.JonesParshall.Curtis
open CFSG.Quasithin.B45Ln (le_rank_of_submatrix)

local notation "𝕄" => Matrix (Fin 5) (Fin 5) (ZMod 2)

@[expose] def codRows_t0 : Fin 8 → Fin 24 :=
  ![0, 1, 2, 3, 9, 13, 17, 20]

@[expose] def codCols_t0 : Fin 8 → Fin 24 :=
  ![4, 5, 6, 7, 8, 12, 16, 20]

@[expose] def codY_t0 : Matrix (Fin 8) (Fin 8) (ZMod 2) :=
  !![0, 0, 0, 0, 0, 0, 0, 1;
    0, 1, 0, 0, 0, 0, 0, 0;
    0, 0, 1, 0, 0, 0, 0, 0;
    0, 0, 0, 1, 0, 0, 0, 0;
    0, 0, 0, 0, 1, 0, 0, 0;
    0, 0, 0, 0, 0, 1, 0, 0;
    0, 0, 0, 0, 0, 0, 1, 0;
    1, 0, 0, 0, 0, 0, 0, 1]

@[expose] def codRows_s0 : Fin 12 → Fin 24 :=
  ![0, 1, 2, 3, 4, 5, 6, 7, 18, 19, 20, 21]

@[expose] def codCols_s0 : Fin 12 → Fin 24 :=
  ![0, 4, 8, 9, 11, 12, 13, 15, 16, 17, 20, 21]

@[expose] def codY_s0 : Matrix (Fin 12) (Fin 12) (ZMod 2) :=
  !![1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0;
    1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1;
    0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0;
    0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0;
    0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1]

theorem rank24_t0 : 8 ≤ (mat24 (toMat tB) - 1).rank :=
  le_rank_of_submatrix _ codRows_t0 codCols_t0 codY_t0 (by decide +kernel)

theorem rank24_s0 : 12 ≤ (mat24 (toMat sB0) - 1).rank :=
  le_rank_of_submatrix _ codRows_s0 codCols_s0 codY_s0 (by decide +kernel)

@[expose] def vecM (B : 𝕄) : Fin 5 × Fin 5 → ZMod 2 := fun p => B p.1 p.2

@[expose] def psiMat {k : ℕ} (Z : Fin k → 𝕄) :
    Matrix (Fin k × Fin 5 × Fin 5) (Fin 5 × Fin 5) (ZMod 2) :=
  Matrix.of fun r c => (if r.2.1 = c.1 then Z r.1 c.2 r.2.2 else 0) +
    (if c.2 = r.2.2 then Z r.1 r.2.1 c.1 else 0)

theorem psiMat_mulVec {k : ℕ} (Z : Fin k → 𝕄) (B : 𝕄) (r : Fin k × Fin 5 × Fin 5) :
    (psiMat Z *ᵥ vecM B) r = (B * Z r.1 + Z r.1 * B) r.2.1 r.2.2 := by
  obtain ⟨l, i, j⟩ := r
  simp only [mulVec, dotProduct, psiMat, vecM, Matrix.of_apply, Fintype.sum_prod_type,
    Matrix.add_apply, Matrix.mul_apply, add_mul, Finset.sum_add_distrib, ite_mul, zero_mul]
  congr 1
  · rw [Finset.sum_comm]
    simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true]
    exact Finset.sum_congr rfl fun q _ => mul_comm _ _
  · simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true]

theorem psiMat_mulVec_eq_zero {k : ℕ} (Z : Fin k → 𝕄) {B : 𝕄} (h : ∀ l, B * Z l = Z l * B) :
    psiMat Z *ᵥ vecM B = 0 := by
  funext r
  rw [psiMat_mulVec, h, CharTwo.add_self_eq_zero, Pi.zero_apply, Matrix.zero_apply]

theorem mem_span_of_comm {k : ℕ} (Z : Fin k → 𝕄) (hr : 23 ≤ (psiMat Z).rank) {a : 𝕄}
    (ha1 : a ≠ 1) (ha0 : a ≠ 0) (h1 : psiMat Z *ᵥ vecM 1 = 0) (h2 : psiMat Z *ᵥ vecM a = 0)
    {B : 𝕄} (hB : psiMat Z *ᵥ vecM B = 0) : B = 0 ∨ B = 1 ∨ B = a ∨ B = 1 + a := by
  classical
  have hdim : Module.finrank (ZMod 2) (LinearMap.ker (psiMat Z).mulVecLin) ≤ 2 := by
    have h := LinearMap.finrank_range_add_finrank_ker (psiMat Z).mulVecLin
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_prod, Fintype.card_fin] at h
    have : (psiMat Z).rank = Module.finrank (ZMod 2) (LinearMap.range (psiMat Z).mulVecLin) :=
      rfl
    omega
  have hinj : Function.Injective vecM := fun X Y h => Matrix.ext fun i j => congrFun h (i, j)
  have hv1 : vecM 1 ≠ 0 := fun h => by
    have := hinj (h.trans (by funext p; rfl : (0 : Fin 5 × Fin 5 → ZMod 2) = vecM 0))
    exact one_ne_zero this
  have hli : LinearIndependent (ZMod 2) ![vecM 1, vecM a] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    rcases (by decide : ∀ c : ZMod 2, c = 0 ∨ c = 1) s with rfl | rfl <;>
      rcases (by decide : ∀ c : ZMod 2, c = 0 ∨ c = 1) t with rfl | rfl
    · exact ⟨rfl, rfl⟩
    · rw [zero_smul, zero_add, one_smul] at hst
      exact absurd (hinj (hst.trans (by funext p; rfl))) ha0
    · rw [zero_smul, add_zero, one_smul] at hst
      exact absurd hst hv1
    · rw [one_smul, one_smul] at hst
      have : vecM 1 = vecM a := by
        have h' := congrArg (· + vecM a) hst
        simp only [add_assoc, CharTwo.add_self_eq_zero, add_zero, zero_add] at h'
        exact h'
      exact absurd (hinj this).symm ha1
  have hspan : Submodule.span (ZMod 2) (Set.range ![vecM 1, vecM a]) =
      LinearMap.ker (psiMat Z).mulVecLin := by
    refine Submodule.eq_of_le_of_finrank_le ?_ ?_
    · rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      fin_cases i
      · exact h1
      · exact h2
    · rw [finrank_span_eq_card hli, Fintype.card_fin]
      exact hdim
  have hBK : vecM B ∈ LinearMap.ker (psiMat Z).mulVecLin := hB
  rw [← hspan, Matrix.range_cons, Matrix.range_cons, Matrix.range_empty, Set.union_empty,
    Set.union_singleton, Submodule.mem_span_pair] at hBK
  obtain ⟨s, t, hst⟩ := hBK
  have key : ∀ X : 𝕄, vecM X = vecM B → X = B := fun X h => hinj h
  rcases (by decide : ∀ c : ZMod 2, c = 0 ∨ c = 1) s with rfl | rfl <;>
    rcases (by decide : ∀ c : ZMod 2, c = 0 ∨ c = 1) t with rfl | rfl
  · left
    refine (key 0 ?_).symm
    rw [← hst, zero_smul, zero_smul, add_zero]
    rfl
  · right; left
    refine (key 1 ?_).symm
    rw [← hst, zero_smul, zero_add, one_smul]
  · right; right; left
    refine (key a ?_).symm
    rw [← hst, zero_smul, add_zero, one_smul]
  · right; right; right
    refine (key (1 + a) ?_).symm
    rw [← hst, one_smul, one_smul, add_comm]
    rfl

@[expose] def ctrZ_t0 : Fin 7 → 𝕄 :=
  ![toMat tB,
    toMat ![4, 0, 0, 0, 0],
    toMat ![8, 0, 0, 0, 0],
    toMat ![16, 0, 0, 0, 0],
    toMat ![0, 0, 2, 0, 0],
    toMat ![0, 0, 0, 2, 0],
    toMat ![0, 0, 0, 0, 2]]

@[expose] def ctrZ_s0 : Fin 6 → 𝕄 :=
  ![toMat sB0,
    toMat ![4, 0, 0, 0, 0],
    toMat ![8, 0, 0, 0, 0],
    toMat ![16, 0, 0, 0, 0],
    toMat ![2, 0, 8, 0, 0],
    toMat ![0, 1, 0, 4, 0]]

@[expose] def ctrRows_t0 : Fin 23 → Fin 7 × Fin 5 × Fin 5 :=
  ![(0, 0, 0), (0, 0, 1), (0, 0, 2), (0, 0, 3), (0, 0, 4), (0, 2, 1), (0, 3, 1), (0, 4, 1),
    (1, 0, 1), (1, 0, 2), (1, 0, 3), (1, 0, 4), (2, 0, 1), (2, 0, 2), (2, 0, 3), (2, 0, 4),
    (3, 0, 1), (3, 0, 2), (3, 0, 3), (3, 0, 4), (4, 0, 1), (5, 0, 1), (6, 0, 1)]

@[expose] def ctrCols_t0 : Fin 23 → Fin 5 × Fin 5 :=
  ![(0, 0), (0, 2), (0, 3), (0, 4), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (2, 0), (2, 1), (2, 2),
    (2, 3), (2, 4), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (4, 0), (4, 1), (4, 2), (4, 3)]

@[expose] def ctrY_t0 : Matrix (Fin 23) (Fin 23) (ZMod 2) :=
  !![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1;
    1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0;
    0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0]

@[expose] def ctrRows_s0 : Fin 23 → Fin 6 × Fin 5 × Fin 5 :=
  ![(0, 0, 0), (0, 0, 1), (0, 0, 2), (0, 0, 3), (0, 0, 4), (0, 1, 0), (0, 1, 1), (0, 1, 2),
    (0, 1, 3), (0, 1, 4), (0, 4, 2), (0, 4, 3), (1, 0, 3), (1, 1, 2), (2, 0, 3), (3, 0, 2),
    (3, 0, 3), (3, 0, 4), (4, 0, 2), (4, 0, 3), (4, 0, 4), (5, 0, 2), (5, 1, 4)]

@[expose] def ctrCols_s0 : Fin 23 → Fin 5 × Fin 5 :=
  ![(0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (1, 0), (1, 1), (1, 2), (1, 4), (2, 0), (2, 1), (2, 2),
    (2, 3), (2, 4), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (4, 0), (4, 1), (4, 2), (4, 3)]

@[expose] def ctrY_s0 : Matrix (Fin 23) (Fin 23) (ZMod 2) :=
  !![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0;
    0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0;
    1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0]

theorem rank_psi_t0 : 23 ≤ (psiMat ctrZ_t0).rank :=
  le_rank_of_submatrix _ ctrRows_t0 ctrCols_t0 ctrY_t0 (by decide +kernel)

theorem rank_psi_s0 : 23 ≤ (psiMat ctrZ_s0).rank :=
  le_rank_of_submatrix _ ctrRows_s0 ctrCols_s0 ctrY_s0 (by decide +kernel)

theorem ctrZ_t0_spec : ctrZ_t0 0 = toMat tB ∧
    (∀ l, l ≠ 0 → (ctrZ_t0 l).trace = 0 ∧ mat24 (toMat tB) *ᵥ c24v (ctrZ_t0 l) = c24v (ctrZ_t0 l)) ∧
    psiMat ctrZ_t0 *ᵥ vecM 1 = 0 ∧ psiMat ctrZ_t0 *ᵥ vecM (toMat tB) = 0 := by
  decide +kernel

theorem ctrZ_s0_spec : ctrZ_s0 0 = toMat sB0 ∧
    (∀ l, l ≠ 0 → (ctrZ_s0 l).trace = 0 ∧
      mat24 (toMat sB0) *ᵥ c24v (ctrZ_s0 l) = c24v (ctrZ_s0 l)) ∧
    psiMat ctrZ_s0 *ᵥ vecM 1 = 0 ∧ psiMat ctrZ_s0 *ᵥ vecM (toMat sB0) = 0 := by
  decide +kernel

noncomputable abbrev fix24 (g : G5) : Submodule (ZMod 2) (Fin 24 → ZMod 2) :=
  LinearMap.ker (rep24 g - 1)

theorem mem_fix24 {g : G5} {v : Fin 24 → ZMod 2} : v ∈ fix24 g ↔ rep24 g v = v := by
  rw [LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero]

theorem t0_sq : B42Ln.t0 * B42Ln.t0 = 1 := Subtype.ext B42Ln.t0M_mul_self

theorem s0_sq : B42Ln.s0 * B42Ln.s0 = 1 := Subtype.ext B42Ln.s0M_mul_self

theorem finrank_fix24_le {a : G5} {A : 𝕄} (hA : (a : 𝕄) = A) (ha : a * a = 1) {r : ℕ}
    (hr : r ≤ (mat24 A - 1).rank) : Module.finrank (ZMod 2) (fix24 a) ≤ 24 - r := by
  have e : fix24 a = LinearMap.ker (mat24 A - 1).mulVecLin := by
    ext v
    rw [mem_fix24, LinearMap.mem_ker, Matrix.mulVecLin_apply, sub_mulVec, one_mulVec,
      sub_eq_zero, rep24_of_inv hA ha]
  have h := LinearMap.finrank_range_add_finrank_ker (mat24 A - 1).mulVecLin
  rw [Module.finrank_fin_fun] at h
  have : (mat24 A - 1).rank =
      Module.finrank (ZMod 2) (LinearMap.range (mat24 A - 1).mulVecLin) := rfl
  rw [e]
  omega

theorem finrank_fix_t0 : Module.finrank (ZMod 2) (fix24 B42Ln.t0) ≤ 16 :=
  finrank_fix24_le coe_t0 t0_sq rank24_t0

theorem finrank_fix_s0 : Module.finrank (ZMod 2) (fix24 B42Ln.s0) ≤ 12 :=
  finrank_fix24_le coe_s0 s0_sq rank24_s0

theorem fix_pair_lt {a₀ b : G5} {k : ℕ} (Z : Fin (k + 1) → 𝕄) (hZ0 : Z 0 = (a₀ : 𝕄))
    (hZl : ∀ l, l ≠ 0 → (Z l).trace = 0 ∧ rep24 a₀ (c24v (Z l)) = c24v (Z l))
    (hr : 23 ≤ (psiMat Z).rank) (h1 : psiMat Z *ᵥ vecM 1 = 0)
    (h2 : psiMat Z *ᵥ vecM (a₀ : 𝕄) = 0) (ha1 : (a₀ : 𝕄) ≠ 1) (ha0 : (a₀ : 𝕄) ≠ 0)
    (ha2 : a₀ * a₀ = 1) (hab : a₀ * b = b * a₀) (hb1 : b ≠ 1) (hba : b ≠ a₀) :
    fix24 a₀ ⊓ fix24 b < fix24 a₀ := by
  refine lt_of_le_of_ne inf_le_left fun heq => ?_
  have hle : fix24 a₀ ≤ fix24 b := by
    rw [← heq]
    exact inf_le_right
  have hcomm : ∀ l, (b : 𝕄) * Z l = Z l * (b : 𝕄) := by
    intro l
    by_cases hl : l = 0
    · rw [hl, hZ0, ← Matrix.SpecialLinearGroup.coe_mul, ← hab,
        Matrix.SpecialLinearGroup.coe_mul]
    · obtain ⟨htr, hfix⟩ := hZl l hl
      have hb := mem_fix24.mp (hle (mem_fix24.mpr hfix))
      rw [rep24_apply] at hb
      have hs := congrArg s24 hb
      change s24 (c24 ((b : 𝕄) * s24 (c24 (Z l)) * ((b⁻¹ : G5) : 𝕄))) = s24 (c24 (Z l)) at hs
      rw [s24_c24 htr] at hs
      have htr' : ((b : 𝕄) * Z l * ((b⁻¹ : G5) : 𝕄)).trace = 0 := by
        rw [← conj5_apply, trace_conj5, htr]
      rw [s24_c24 htr'] at hs
      calc (b : 𝕄) * Z l = (b : 𝕄) * Z l * ((b⁻¹ : G5) : 𝕄) * (b : 𝕄) := by
            rw [Matrix.mul_assoc _ ((b⁻¹ : G5) : 𝕄), ← Matrix.SpecialLinearGroup.coe_mul,
              inv_mul_cancel, Matrix.SpecialLinearGroup.coe_one, Matrix.mul_one]
        _ = Z l * (b : 𝕄) := by rw [hs]
  have hB := psiMat_mulVec_eq_zero Z hcomm
  have hbb : ((b : 𝕄) * ((b⁻¹ : G5) : 𝕄)) = 1 := by
    rw [← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel, Matrix.SpecialLinearGroup.coe_one]
  rcases mem_span_of_comm Z hr ha1 ha0 h1 h2 hB with h | h | h | h
  · rw [h, Matrix.zero_mul] at hbb
    exact zero_ne_one hbb
  · exact hb1 (Subtype.ext h)
  · exact hba (Subtype.ext h)
  · have hsq : (b : 𝕄) * (b : 𝕄) = 0 := by
      have ha2' : (a₀ : 𝕄) * (a₀ : 𝕄) = 1 := by
        rw [← Matrix.SpecialLinearGroup.coe_mul, ha2, Matrix.SpecialLinearGroup.coe_one]
      have e : ((1 : 𝕄) + (a₀ : 𝕄)) * (1 + (a₀ : 𝕄)) =
          ((1 : 𝕄) + (a₀ : 𝕄) * (a₀ : 𝕄)) + ((a₀ : 𝕄) + (a₀ : 𝕄)) := by
        noncomm_ring
      rw [h, e, ha2', CharTwo.add_self_eq_zero, CharTwo.add_self_eq_zero, add_zero]
    have hb0 : (b : 𝕄) = 0 := by
      calc (b : 𝕄) = (b : 𝕄) * ((b : 𝕄) * ((b⁻¹ : G5) : 𝕄)) := by rw [hbb, Matrix.mul_one]
        _ = (b : 𝕄) * (b : 𝕄) * ((b⁻¹ : G5) : 𝕄) := (Matrix.mul_assoc _ _ _).symm
        _ = 0 := by rw [hsq, Matrix.zero_mul]
    rw [hb0, Matrix.zero_mul] at hbb
    exact zero_ne_one hbb

theorem tB_ne : toMat tB ≠ 1 ∧ toMat tB ≠ 0 := by decide

theorem sB0_ne : toMat sB0 ≠ 1 ∧ toMat sB0 ≠ 0 := by decide

theorem finrank_fix_pair_t0 {b : G5} (hab : B42Ln.t0 * b = b * B42Ln.t0) (hb1 : b ≠ 1)
    (hbt : b ≠ B42Ln.t0) : Module.finrank (ZMod 2) ↥(fix24 B42Ln.t0 ⊓ fix24 b) ≤ 15 := by
  obtain ⟨hZ0, hZl, h1, h2⟩ := ctrZ_t0_spec
  have hlt := fix_pair_lt ctrZ_t0 (hZ0.trans coe_t0.symm)
    (fun l hl => ⟨(hZl l hl).1, by rw [rep24_of_inv coe_t0 t0_sq]; exact (hZl l hl).2⟩)
    rank_psi_t0 h1 (by rw [coe_t0]; exact h2) (by rw [coe_t0]; exact tB_ne.1)
    (by rw [coe_t0]; exact tB_ne.2) t0_sq hab hb1 hbt
  have h3 := Submodule.finrank_lt_finrank_of_lt hlt
  have h4 := finrank_fix_t0
  omega

theorem finrank_fix_pair_s0 {b : G5} (hab : B42Ln.s0 * b = b * B42Ln.s0) (hb1 : b ≠ 1)
    (hbs : b ≠ B42Ln.s0) : Module.finrank (ZMod 2) ↥(fix24 B42Ln.s0 ⊓ fix24 b) ≤ 11 := by
  obtain ⟨hZ0, hZl, h1, h2⟩ := ctrZ_s0_spec
  have hlt := fix_pair_lt ctrZ_s0 (hZ0.trans coe_s0.symm)
    (fun l hl => ⟨(hZl l hl).1, by rw [rep24_of_inv coe_s0 s0_sq]; exact (hZl l hl).2⟩)
    rank_psi_s0 h1 (by rw [coe_s0]; exact h2) (by rw [coe_s0]; exact sB0_ne.1)
    (by rw [coe_s0]; exact sB0_ne.2) s0_sq hab hb1 hbs
  have h3 := Submodule.finrank_lt_finrank_of_lt hlt
  have h4 := finrank_fix_s0
  omega

section Transport

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] {ρ : Representation (ZMod 2) G5 V}
  {β : V ≃ₗ[ZMod 2] (Fin 24 → ZMod 2)}

noncomputable def conjEquiv (c : G5) : (Fin 24 → ZMod 2) ≃ₗ[ZMod 2] (Fin 24 → ZMod 2) where
  toFun := rep24 c
  invFun := rep24 c⁻¹
  map_add' := map_add _
  map_smul' := map_smul _
  left_inv v := by
    rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
  right_inv v := by
    rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]

noncomputable def isoConj (β : V ≃ₗ[ZMod 2] (Fin 24 → ZMod 2)) (c : G5) :
    V ≃ₗ[ZMod 2] (Fin 24 → ZMod 2) :=
  β.trans (conjEquiv c)

theorem isoConj_act (hβ : ∀ g v, β (ρ g v) = rep24 g (β v)) (c g : G5) (v : V) :
    isoConj β c (ρ g v) = rep24 (c * g * c⁻¹) (isoConj β c v) := by
  change rep24 c (β (ρ g v)) = rep24 (c * g * c⁻¹) (rep24 c (β v))
  rw [hβ, ← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul,
    inv_mul_cancel_right]

theorem map_ker_eq (hβ : ∀ g v, β (ρ g v) = rep24 g (β v)) (c g : G5) :
    (LinearMap.ker (ρ g - 1)).map (isoConj β c).toLinearMap = fix24 (c * g * c⁻¹) := by
  ext w
  constructor
  · rintro ⟨v, hv, rfl⟩
    rw [SetLike.mem_coe, LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply,
      sub_eq_zero] at hv
    rw [mem_fix24]
    change rep24 (c * g * c⁻¹) (isoConj β c v) = isoConj β c v
    rw [← isoConj_act hβ, hv]
  · intro hw
    refine ⟨(isoConj β c).symm w, ?_, (isoConj β c).apply_symm_apply w⟩
    rw [SetLike.mem_coe, LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply,
      sub_eq_zero]
    apply (isoConj β c).injective
    rw [isoConj_act hβ, LinearEquiv.apply_symm_apply]
    exact mem_fix24.mp hw

theorem finrank_ker_eq (hβ : ∀ g v, β (ρ g v) = rep24 g (β v)) (c g : G5) :
    Module.finrank (ZMod 2) (LinearMap.ker (ρ g - 1)) =
      Module.finrank (ZMod 2) (fix24 (c * g * c⁻¹)) := by
  rw [← map_ker_eq hβ c g, LinearEquiv.finrank_map_eq]

theorem finrank_ker_inf_eq (hβ : ∀ g v, β (ρ g v) = rep24 g (β v)) (c a b : G5) :
    Module.finrank (ZMod 2) ↥(LinearMap.ker (ρ a - 1) ⊓ LinearMap.ker (ρ b - 1)) =
      Module.finrank (ZMod 2) ↥(fix24 (c * a * c⁻¹) ⊓ fix24 (c * b * c⁻¹)) := by
  rw [← map_ker_eq hβ c a, ← map_ker_eq hβ c b,
    ← Submodule.map_inf _ (isoConj β c).injective, LinearEquiv.finrank_map_eq]

end Transport

end CFSG.Quasithin.B45L5

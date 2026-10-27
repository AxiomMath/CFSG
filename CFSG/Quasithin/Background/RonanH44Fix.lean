module

public import CFSG.Quasithin.Background.HFL3Four

public section

namespace CFSG.Quasithin.RonanH44

open CFSG.Quasithin CFSG.Quasithin.H CFSG.Quasithin.H.L3Nine CFSG.Quasithin.H.SU3 Matrix
open scoped MatrixGroups

variable {K : Type} [Field K] [Finite K] [CharP K 2] {n : ℕ}

@[expose] def QWs (K : Type) [Field K] : Subgroup SL(3, K) :=
  Subgroup.closure {g | ∃ c : K,
    g = SpecialLinearGroup.transvection (by decide : (0 : Fin 3) ≠ 2) c ∨
    g = SpecialLinearGroup.transvection (by decide : (1 : Fin 3) ≠ 2) c}

@[expose] def QZs (K : Type) [Field K] : Subgroup SL(3, K) :=
  Subgroup.closure {g | ∃ c : K,
    g = SpecialLinearGroup.transvection (by decide : (0 : Fin 3) ≠ 1) c ∨
    g = SpecialLinearGroup.transvection (by decide : (0 : Fin 3) ≠ 2) c}

omit [Finite K] [CharP K 2] in
theorem transvection12_mem_Q2 (a : K) :
    SpecialLinearGroup.transvection (by decide : (1 : Fin 3) ≠ 2) a ∈ Q2 K := by
  refine ⟨CFSG.LocalAnalysis.ComponentInitial.LinearFlag.mem_unitriangular.2
    ⟨fun i k hik => ?_, fun i => ?_⟩, ?_⟩ <;>
    rw [Matrix.SpecialLinearGroup.transvection_coe]
  · fin_cases i <;> fin_cases k <;> simp_all [Matrix.single_apply]
  · fin_cases i <;> simp [Matrix.single_apply]
  · simp [Matrix.single_apply]

theorem QWs_eq_Q2 : QWs K = Q2 K := by
  apply le_antisymm
  · refine (Subgroup.closure_le _).2 ?_
    rintro _ ⟨c, rfl | rfl⟩
    · exact transvection02_mem_Q2 c
    · exact transvection12_mem_Q2 c
  · intro x hx
    obtain ⟨x00, x11, x22, x10, x20, x21⟩ := uni3_entries hx.1
    have x01 : (x : Matrix (Fin 3) (Fin 3) K) 0 1 = 0 := hx.2
    have hx' : x = SpecialLinearGroup.transvection (by decide : (0 : Fin 3) ≠ 2)
        ((x : Matrix (Fin 3) (Fin 3) K) 0 2) * SpecialLinearGroup.transvection
        (by decide : (1 : Fin 3) ≠ 2) ((x : Matrix (Fin 3) (Fin 3) K) 1 2) := by
      apply Subtype.ext
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_three,
          Matrix.SpecialLinearGroup.transvection_coe, Matrix.one_apply, Matrix.single_apply,
          x00, x11, x22, x10, x20, x21, x01]
    rw [hx']
    exact mul_mem (Subgroup.subset_closure ⟨_, Or.inl rfl⟩)
      (Subgroup.subset_closure ⟨_, Or.inr rfl⟩)

theorem QZs_eq_Q1 : QZs K = Q1 K := by
  apply le_antisymm
  · refine (Subgroup.closure_le _).2 ?_
    rintro _ ⟨c, rfl | rfl⟩
    · exact transvection_mem_Q1 (by decide) c
    · exact transvection_mem_Q1 (by decide) c
  · intro x hx
    obtain ⟨x00, x11, x22, x10, x20, x21⟩ := uni3_entries hx.1
    have x12 : (x : Matrix (Fin 3) (Fin 3) K) 1 2 = 0 := hx.2
    have hx' : x = SpecialLinearGroup.transvection (by decide : (0 : Fin 3) ≠ 1)
        ((x : Matrix (Fin 3) (Fin 3) K) 0 1) * SpecialLinearGroup.transvection
        (by decide : (0 : Fin 3) ≠ 2) ((x : Matrix (Fin 3) (Fin 3) K) 0 2) := by
      apply Subtype.ext
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_three,
          Matrix.SpecialLinearGroup.transvection_coe, Matrix.one_apply, Matrix.single_apply,
          x00, x11, x22, x10, x20, x21, x12]
    rw [hx']
    exact mul_mem (Subgroup.subset_closure ⟨_, Or.inl rfl⟩)
      (Subgroup.subset_closure ⟨_, Or.inr rfl⟩)

theorem fixed_QW (hn : 1 ≤ n) (hK : Nat.card K = (2 ^ n) ^ 2) :
    {X : Matrix (Fin 3) (Fin 3) K |
        ∀ g ∈ QWs K, tw n (g : Matrix (Fin 3) (Fin 3) K) X = X} =
      {X | ∀ i j, (i = 2 ∨ j = 2) → X i j = 0} := by
  ext X
  simp only [Set.mem_setOf_eq]
  constructor
  · intro hX
    have g1 : SpecialLinearGroup.transvection (by decide : (0 : Fin 3) ≠ 2) (1 : K) ∈ QWs K :=
      Subgroup.subset_closure ⟨1, Or.inl rfl⟩
    have g2 : SpecialLinearGroup.transvection (by decide : (1 : Fin 3) ≠ 2) (1 : K) ∈ QWs K :=
      Subgroup.subset_closure ⟨1, Or.inr rfl⟩
    have e1 := hX _ g1
    have e2 := hX _ g2
    have x22 : X 2 2 = 0 := by
      have h := congrFun (congrFun e1 0) 2
      simpa [tw, conjM, Matrix.mul_apply, Fin.sum_univ_three,
        Matrix.SpecialLinearGroup.transvection_coe, Matrix.one_apply, Matrix.single_apply] using h
    have x21 : X 2 1 = 0 := by
      have h := congrFun (congrFun e1 0) 1
      simpa [tw, conjM, Matrix.mul_apply, Fin.sum_univ_three,
        Matrix.SpecialLinearGroup.transvection_coe, Matrix.one_apply, Matrix.single_apply] using h
    have x12 : X 1 2 = 0 := by
      have h := congrFun (congrFun e1 1) 0
      simpa [tw, conjM, Matrix.mul_apply, Fin.sum_univ_three,
        Matrix.SpecialLinearGroup.transvection_coe, Matrix.one_apply, Matrix.single_apply] using h
    have x20 : X 2 0 = 0 := by
      have h := congrFun (congrFun e2 1) 0
      simpa [tw, conjM, Matrix.mul_apply, Fin.sum_univ_three,
        Matrix.SpecialLinearGroup.transvection_coe, Matrix.one_apply, Matrix.single_apply] using h
    have x02 : X 0 2 = 0 := by
      have h := congrFun (congrFun e2 0) 1
      simpa [tw, conjM, Matrix.mul_apply, Fin.sum_univ_three,
        Matrix.SpecialLinearGroup.transvection_coe, Matrix.one_apply, Matrix.single_apply] using h
    intro i j hij
    fin_cases i <;> fin_cases j <;> first | assumption | exact absurd hij (by decide)
  · intro hX g hg
    have hrow : ∀ j, X 2 j = 0 := fun j => hX 2 j (Or.inl rfl)
    have hcol : ∀ i, X i 2 = 0 := fun i => hX i 2 (Or.inr rfl)
    let S : Subgroup (SpecialLinearGroup (Fin 3) K) :=
      { carrier := {g | tw n (g : Matrix (Fin 3) (Fin 3) K) X = X}
        one_mem' := by
          show tw n ((1 : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) X = X
          rw [Matrix.SpecialLinearGroup.coe_one, tw_one]
        mul_mem' := fun {a b} (ha : tw n (a : Matrix (Fin 3) (Fin 3) K) X = X)
            (hb : tw n (b : Matrix (Fin 3) (Fin 3) K) X = X) => by
          show tw n ((a * b : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) X = X
          rw [Matrix.SpecialLinearGroup.coe_mul, ← tw_tw, hb, ha]
        inv_mem' := fun {a} (ha : tw n (a : Matrix (Fin 3) (Fin 3) K) X = X) => by
          show tw n ((a⁻¹ : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) X = X
          have hinv : ((a⁻¹ : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
              (a : Matrix (Fin 3) (Fin 3) K) = 1 := by
            rw [← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel,
              Matrix.SpecialLinearGroup.coe_one]
          calc tw n ((a⁻¹ : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) X
              = tw n ((a⁻¹ : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)
                  (tw n (a : Matrix (Fin 3) (Fin 3) K) X) := by rw [ha]
            _ = tw n (((a⁻¹ : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
                  (a : Matrix (Fin 3) (Fin 3) K)) X := tw_tw _ _ _
            _ = X := by rw [hinv, tw_one] }
    have hS : QWs K ≤ S := by
      refine (Subgroup.closure_le _).2 ?_
      rintro _ ⟨c, rfl | rfl⟩
      · show tw n ((SpecialLinearGroup.transvection (by decide : (0 : Fin 3) ≠ 2) c :
            SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) X = X
        ext i j
        fin_cases i <;> fin_cases j <;>
          simp [tw, conjM, Matrix.mul_apply, Fin.sum_univ_three,
            Matrix.SpecialLinearGroup.transvection_coe, Matrix.one_apply, Matrix.single_apply,
            hrow, hcol]
      · show tw n ((SpecialLinearGroup.transvection (by decide : (1 : Fin 3) ≠ 2) c :
            SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) X = X
        ext i j
        fin_cases i <;> fin_cases j <;>
          simp [tw, conjM, Matrix.mul_apply, Fin.sum_univ_three,
            Matrix.SpecialLinearGroup.transvection_coe, Matrix.one_apply, Matrix.single_apply,
            hrow, hcol]
    exact hS hg

theorem fixV_QW (hn : 1 ≤ n) (hK : Nat.card K = (2 ^ n) ^ 2) :
    fixV ((QWs K).map (rho hK)) = blkW n K := by
  rw [QWs_eq_Q2]
  exact fixV_rhoQ2 hn hK

theorem mem_fixV_QZ (hn : 1 ≤ n) (hK : Nat.card K = (2 ^ n) ^ 2) {X : HMod n K} :
    X ∈ fixV ((QZs K).map (rho hK)) ↔ ∀ i j : Fin 3, ¬ (i = 0 ∧ j = 0) → mat X i j = 0 := by
  rw [QZs_eq_Q1]
  constructor
  · intro hX
    refine eq_zero_of_fix hn hK (fun a => ?_) (fun a => ?_)
    · rw [← rho_transvection]
      exact hX _ ⟨_, transvection_mem_Q1 (by decide) a, rfl⟩
    · rw [← rho_transvection]
      exact hX _ ⟨_, transvection_mem_Q1 (by decide) a, rfl⟩
  · intro h
    rw [mem_fixV]
    rintro _ ⟨x, hx, rfl⟩
    have h01 : mat X 0 1 = 0 := h 0 1 (by decide)
    have h02 : mat X 0 2 = 0 := h 0 2 (by decide)
    have h10 : mat X 1 0 = 0 := h 1 0 (by decide)
    have h11 : mat X 1 1 = 0 := h 1 1 (by decide)
    have h12 : mat X 1 2 = 0 := h 1 2 (by decide)
    have h20 : mat X 2 0 = 0 := h 2 0 (by decide)
    have h21 : mat X 2 1 = 0 := h 2 1 (by decide)
    have h22 : mat X 2 2 = 0 := h 2 2 (by decide)
    obtain ⟨x00, x11, x22, x10, x20, x21⟩ := uni3_entries hx.1
    have x12 : (x : Matrix (Fin 3) (Fin 3) K) 1 2 = 0 := hx.2
    apply mat_injective
    rw [mat_rho]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [tw, conjM, Matrix.mul_apply, Fin.sum_univ_three, x00, x11, x22, x10, x20, x21,
        x12, h01, h02, h10, h11, h12, h20, h21, h22]

end CFSG.Quasithin.RonanH44

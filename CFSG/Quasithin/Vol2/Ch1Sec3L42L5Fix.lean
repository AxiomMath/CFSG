module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListFlag3

public section

namespace CFSG.Quasithin.L139L42

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.QuasithinUnique.Vol2Native.A312L (stabilizer_entries
  mem_stabilizer_flagSpace_of_entries eq_zero_or_eq_one_of_card_two)

variable {F : Type*} [Field F]

theorem tv_mulVec {i j : Fin 5} (h : i ≠ j) (v : Fin 5 → F) :
    ((SpecialLinearGroup.transvection h (1 : F) : SpecialLinearGroup (Fin 5) F) :
      Matrix (Fin 5) (Fin 5) F) *ᵥ v = v + Function.update (0 : Fin 5 → F) i (v j) := by
  rw [SpecialLinearGroup.transvection_coe, Matrix.add_mulVec, Matrix.one_mulVec,
    Matrix.single_mulVec, one_mul]

theorem eq_zero_of_tv_fix {i j : Fin 5} (h : i ≠ j) {v : Fin 5 → F}
    (hv : ((SpecialLinearGroup.transvection h (1 : F) : SpecialLinearGroup (Fin 5) F) :
      Matrix (Fin 5) (Fin 5) F) *ᵥ v = v) : v j = 0 := by
  rw [tv_mulVec] at hv
  have := congrFun hv i
  simpa using this

theorem tv_transpose {i j : Fin 5} (h : i ≠ j) :
    ((SpecialLinearGroup.transvection h (1 : F) : SpecialLinearGroup (Fin 5) F) :
      Matrix (Fin 5) (Fin 5) F)ᵀ =
    ((SpecialLinearGroup.transvection h.symm (1 : F) : SpecialLinearGroup (Fin 5) F) :
      Matrix (Fin 5) (Fin 5) F) := by
  rw [SpecialLinearGroup.transvection_coe, SpecialLinearGroup.transvection_coe,
    Matrix.transpose_add, Matrix.transpose_one, Matrix.transpose_single]

theorem tv_mem_stabilizer {i j : Fin 5} (h : i ≠ j) {d : ℕ}
    (hd : ¬ ((j : ℕ) < d ∧ d ≤ (i : ℕ))) :
    SpecialLinearGroup.transvection h (1 : F) ∈ stabilizer (flagSpace 5 F d) := by
  refine mem_stabilizer_flagSpace_of_entries fun k l hl hk => ?_
  rw [SpecialLinearGroup.transvection_coe, Matrix.add_apply, Matrix.one_apply,
    Matrix.single_apply]
  have hkl : k ≠ l := fun e => by subst e; omega
  have hne : ¬ (i = k ∧ j = l) := by
    rintro ⟨rfl, rfl⟩
    exact hd ⟨hl, hk⟩
  simp [hkl, hne]

section Card

variable [Finite F] (hF : Nat.card F = 2)
include hF

theorem mulVec_e0_of_mem {g : SpecialLinearGroup (Fin 5) F}
    (hg : g ∈ stabilizer (flagSpace 5 F 1)) :
    (g : Matrix (Fin 5) (Fin 5) F) *ᵥ Pi.single 0 1 = Pi.single 0 1 := by
  have hcol : ∀ k : Fin 5, k ≠ 0 → (g : Matrix (Fin 5) (Fin 5) F) k 0 = 0 := fun k hk =>
    stabilizer_entries hg (l := 0) (by simp) (Nat.one_le_iff_ne_zero.mpr (by
      intro h; exact hk (Fin.ext h)))
  have h00 : (g : Matrix (Fin 5) (Fin 5) F) 0 0 = 1 := by
    rcases eq_zero_or_eq_one_of_card_two hF ((g : Matrix (Fin 5) (Fin 5) F) 0 0) with h | h
    · have hdet := Matrix.det_eq_zero_of_column_eq_zero (A := (g : Matrix (Fin 5) (Fin 5) F)) 0
        (fun k => by
          by_cases hk : k = 0
          · rw [hk, h]
          · exact hcol k hk)
      rw [g.2] at hdet
      exact absurd hdet one_ne_zero
    · exact h
  ext k
  rw [Matrix.mulVec_single_one]
  change (g : Matrix (Fin 5) (Fin 5) F) k 0 = _
  by_cases hk : k = 0
  · subst hk
    simp [h00]
  · rw [hcol k hk, Pi.single_eq_of_ne hk]

omit [Finite F] hF in
theorem apply_eq_zero_of_fix_one {v : Fin 5 → F}
    (hv : ∀ g ∈ stabilizer (flagSpace 5 F 1), (g : Matrix (Fin 5) (Fin 5) F) *ᵥ v = v)
    {k : Fin 5} (hk : k ≠ 0) : v k = 0 :=
  eq_zero_of_tv_fix (Ne.symm hk) (hv _ (tv_mem_stabilizer (Ne.symm hk) (by omega)))

omit [Finite F] hF in
theorem eq_zero_of_fixT_one {v : Fin 5 → F}
    (hv : ∀ g ∈ stabilizer (flagSpace 5 F 1), (g : Matrix (Fin 5) (Fin 5) F)ᵀ *ᵥ v = v) :
    v = 0 := by
  have key : ∀ i j : Fin 5, (h : i ≠ j) → j ≠ 0 → v i = 0 := fun i j h hj => by
    have h1 := hv _ (tv_mem_stabilizer (F := F) h (d := 1) (by
      rintro ⟨hlt, -⟩
      exact hj (Fin.ext (by omega))))
    rw [tv_transpose] at h1
    exact eq_zero_of_tv_fix h.symm h1
  funext i
  fin_cases i
  · exact key 0 1 (by decide) (by decide)
  · exact key 1 2 (by decide) (by decide)
  · exact key 2 1 (by decide) (by decide)
  · exact key 3 1 (by decide) (by decide)
  · exact key 4 1 (by decide) (by decide)

theorem mulVecT_e4_of_mem {g : SpecialLinearGroup (Fin 5) F}
    (hg : g ∈ stabilizer (flagSpace 5 F 4)) :
    (g : Matrix (Fin 5) (Fin 5) F)ᵀ *ᵥ Pi.single 4 1 = Pi.single 4 1 := by
  have hrow : ∀ l : Fin 5, l ≠ 4 → (g : Matrix (Fin 5) (Fin 5) F) 4 l = 0 := fun l hl =>
    stabilizer_entries hg (k := 4) (by
      have := l.isLt
      have : (l : ℕ) ≠ 4 := fun h => hl (Fin.ext h)
      omega) (by simp)
  have h44 : (g : Matrix (Fin 5) (Fin 5) F) 4 4 = 1 := by
    rcases eq_zero_or_eq_one_of_card_two hF ((g : Matrix (Fin 5) (Fin 5) F) 4 4) with h | h
    · have hdet := Matrix.det_eq_zero_of_row_eq_zero (A := (g : Matrix (Fin 5) (Fin 5) F)) 4
        (fun l => by
          by_cases hl : l = 4
          · rw [hl, h]
          · exact hrow l hl)
      rw [g.2] at hdet
      exact absurd hdet one_ne_zero
    · exact h
  ext l
  rw [Matrix.mulVec_single_one]
  change (g : Matrix (Fin 5) (Fin 5) F) 4 l = _
  by_cases hl : l = 4
  · subst hl
    simp [h44]
  · rw [hrow l hl, Pi.single_eq_of_ne hl]

omit [Finite F] hF in
theorem eq_zero_of_fix_four {v : Fin 5 → F}
    (hv : ∀ g ∈ stabilizer (flagSpace 5 F 4), (g : Matrix (Fin 5) (Fin 5) F) *ᵥ v = v) :
    v = 0 := by
  have key : ∀ i j : Fin 5, (h : i ≠ j) → i ≠ 4 → v j = 0 := fun i j h hi =>
    eq_zero_of_tv_fix h (hv _ (tv_mem_stabilizer (F := F) h (d := 4) (by
      rintro ⟨-, hle⟩
      exact hi (Fin.ext (by omega)))))
  funext j
  fin_cases j
  · exact key 1 0 (by decide) (by decide)
  · exact key 0 1 (by decide) (by decide)
  · exact key 0 2 (by decide) (by decide)
  · exact key 0 3 (by decide) (by decide)
  · exact key 0 4 (by decide) (by decide)

omit [Finite F] hF in
theorem apply_eq_zero_of_fixT_four {v : Fin 5 → F}
    (hv : ∀ g ∈ stabilizer (flagSpace 5 F 4), (g : Matrix (Fin 5) (Fin 5) F)ᵀ *ᵥ v = v)
    {k : Fin 5} (hk : k ≠ 4) : v k = 0 := by
  have h1 := hv _ (tv_mem_stabilizer (F := F) (i := k) (j := 4) hk (d := 4) (by simp))
  rw [tv_transpose] at h1
  exact eq_zero_of_tv_fix hk.symm h1

end Card

end CFSG.Quasithin.L139L42

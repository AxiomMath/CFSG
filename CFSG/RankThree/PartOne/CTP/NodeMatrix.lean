module

public import CFSG.RankThree.PartOne.CTP.Spectrum

public section

namespace CFSG.RankThree.PartOne.CTP

open Matrix
open scoped MatrixGroups

section Helpers

variable {F : Type*} [Field F]

private theorem mem_plane_iff_eigen' (b : Module.Basis (Fin 3) F (Fin 3 → F)) (d : Fin 3 → F)
    (M : Matrix (Fin 3) (Fin 3) F) (hb : ∀ i, M.mulVec (b i) = d i • b i) (h01 : d 0 = d 1)
    (h02 : d 0 ≠ d 2) (v : Fin 3 → F) :
    v ∈ Submodule.span F {b 0, b 1} ↔ M.mulVec v = d 0 • v := by
  rw [mem_span_pair_iff_repr, mulVec_eq_smul_iff b d M hb]
  constructor
  · intro h i
    fin_cases i
    · rfl
    · simp [h01]
    · simp [h]
  · intro h
    have h3 : (d 2 - d 0) * b.repr v 2 = 0 := by linear_combination h 2
    exact (mul_eq_zero.mp h3).resolve_left (sub_ne_zero.mpr (Ne.symm h02))

private theorem mem_line_iff_eigen' (b : Module.Basis (Fin 3) F (Fin 3 → F)) (d : Fin 3 → F)
    (M : Matrix (Fin 3) (Fin 3) F) (hb : ∀ i, M.mulVec (b i) = d i • b i) (h01 : d 0 = d 1)
    (h02 : d 0 ≠ d 2) (v : Fin 3 → F) :
    v ∈ Submodule.span F {b 2} ↔ M.mulVec v = d 2 • v := by
  rw [mem_span_single_iff_repr, mulVec_eq_smul_iff b d M hb]
  constructor
  · rintro ⟨h0, h1⟩ i
    fin_cases i
    · simp [h0]
    · simp [h1]
    · rfl
  · intro h
    have h0 : (d 0 - d 2) * b.repr v 0 = 0 := by linear_combination h 0
    have h1 : (d 0 - d 2) * b.repr v 1 = 0 := by
      have := h 1
      rw [← h01] at this
      linear_combination this
    exact ⟨(mul_eq_zero.mp h0).resolve_left (sub_ne_zero.mpr h02),
      (mul_eq_zero.mp h1).resolve_left (sub_ne_zero.mpr h02)⟩

private theorem eq_smul_basis_of_eigen_distinct' (b : Module.Basis (Fin 3) F (Fin 3 → F))
    (d : Fin 3 → F) (M : Matrix (Fin 3) (Fin 3) F) (hb : ∀ i, M.mulVec (b i) = d i • b i)
    (hd : Function.Injective d) (i : Fin 3) {v : Fin 3 → F} (hv : M.mulVec v = d i • v) :
    ∃ c : F, v = c • b i := by
  refine ⟨b.repr v i, ?_⟩
  apply b.repr.injective
  ext j
  have h := (mulVec_eq_smul_iff b d M hb (d i) v).mp hv j
  by_cases hji : j = i
  · subst hji; simp
  · have h0 : b.repr v j = 0 := by
      have h3 : (d j - d i) * b.repr v j = 0 := by linear_combination h
      exact (mul_eq_zero.mp h3).resolve_left (sub_ne_zero.mpr fun h => hji (hd h))
    simp [h0, Module.Basis.repr_self, Ne.symm hji]

private theorem eq_bot_of_distinct' (H : Subgroup SL(3, F)) [Group.IsPerfect H]
    (M : Matrix (Fin 3) (Fin 3) F) (b : Module.Basis (Fin 3) F (Fin 3 → F)) (d : Fin 3 → F)
    (hb : ∀ i, M.mulVec (b i) = d i • b i) (hd : Function.Injective d)
    (hcomm : ∀ h ∈ H, (h : Matrix (Fin 3) (Fin 3) F) * M = M * (h : Matrix (Fin 3) (Fin 3) F)) :
    H = ⊥ := by
  rw [eq_bot_iff]
  intro g hg
  have hfix : ∀ i, ∀ g ∈ H, (g : Matrix (Fin 3) (Fin 3) F).mulVec (b i) = b i := fun i =>
    perfect_fixes_line H (b.ne_zero i) fun g hg => by
      have hm : M.mulVec ((g : Matrix (Fin 3) (Fin 3) F).mulVec (b i)) =
          d i • (g : Matrix (Fin 3) (Fin 3) F).mulVec (b i) := by
        rw [Matrix.mulVec_mulVec, ← hcomm g hg, ← Matrix.mulVec_mulVec, hb i,
          Matrix.mulVec_smul]
      exact eq_smul_basis_of_eigen_distinct' b d M hb hd i hm
  rw [Subgroup.mem_bot]
  have h1 : (g : Matrix (Fin 3) (Fin 3) F) = 1 := by
    refine Matrix.ext_iff_mulVec.mpr fun v => ?_
    have : Matrix.mulVecLin (g : Matrix (Fin 3) (Fin 3) F) = Matrix.mulVecLin 1 :=
      b.ext fun i => by simpa using hfix i g hg
    exact LinearMap.congr_fun this v
  exact Matrix.SpecialLinearGroup.ext _ _ fun i j => by
    have := congrFun (congrFun h1 i) j
    exact this

private theorem exists_le_blkGroup_aux (H : Subgroup SL(3, F)) [Group.IsPerfect H]
    (M : Matrix (Fin 3) (Fin 3) F)
    (b : Module.Basis (Fin 3) F (Fin 3 → F)) (d : Fin 3 → F)
    (hb : ∀ i, M.mulVec (b i) = d i • b i) (h01 : d 0 = d 1) (h02 : d 0 ≠ d 2)
    (hcomm : ∀ h ∈ H, (h : Matrix (Fin 3) (Fin 3) F) * M = M * (h : Matrix (Fin 3) (Fin 3) F)) :
    ∃ (W ℓ : Submodule F (Fin 3 → F)) (a₀ c₀ : F), IsCompl W ℓ ∧ Module.finrank F W = 2 ∧
      a₀ ≠ c₀ ∧ (∀ w ∈ W, M.mulVec w = a₀ • w) ∧ (∀ u ∈ ℓ, M.mulVec u = c₀ • u) ∧
      H ≤ blkGroup F W ℓ :=
  ⟨Submodule.span F {b 0, b 1}, Submodule.span F {b 2}, d 0, d 2,
    isCompl_span_pair_single b, finrank_span_pair_basis b, h02,
    fun w hw => (mem_plane_iff_eigen' b d M hb h01 h02 w).mp hw,
    fun u hu => (mem_line_iff_eigen' b d M hb h01 h02 u).mp hu,
    le_blkGroup_of_comm H M b d hb h01 h02 hcomm⟩

end Helpers

theorem exists_le_blkGroup {F : Type} [Field F]
    (H : Subgroup SL(3, F)) [Group.IsPerfect H] (hH : H ≠ ⊥) (M : Matrix (Fin 3) (Fin 3) F)
    (hdiag : ∃ (b : Module.Basis (Fin 3) F (Fin 3 → F)) (d : Fin 3 → F),
      ∀ i, M.mulVec (b i) = d i • b i)
    (hns : ¬ ∃ c : F, M = c • (1 : Matrix (Fin 3) (Fin 3) F))
    (hcomm : ∀ h ∈ H, (h : Matrix (Fin 3) (Fin 3) F) * M = M * (h : Matrix (Fin 3) (Fin 3) F)) :
    ∃ (W ℓ : Submodule F (Fin 3 → F)) (a b : F), IsCompl W ℓ ∧ Module.finrank F W = 2 ∧
      a ≠ b ∧ (∀ w ∈ W, M.mulVec w = a • w) ∧ (∀ u ∈ ℓ, M.mulVec u = b • u) ∧
      H ≤ blkGroup F W ℓ := by
  obtain ⟨b, d, hb⟩ := hdiag
  have hnotconst : ¬ (d 0 = d 1 ∧ d 0 = d 2) := by
    rintro ⟨h1, h2⟩
    apply hns
    refine ⟨d 0, ?_⟩
    refine Matrix.ext_iff_mulVec.mpr fun v => ?_
    have h : Matrix.mulVecLin M = Matrix.mulVecLin (d 0 • (1 : Matrix (Fin 3) (Fin 3) F)) :=
      b.ext fun i => by
        fin_cases i
        · simpa using hb 0
        · simpa [h1] using hb 1
        · simpa [h2] using hb 2
    exact LinearMap.congr_fun h v
  have transfer : ∀ e : Equiv.Perm (Fin 3), d (e 0) = d (e 1) → d (e 0) ≠ d (e 2) →
      ∃ (W ℓ : Submodule F (Fin 3 → F)) (a b : F), IsCompl W ℓ ∧ Module.finrank F W = 2 ∧
        a ≠ b ∧ (∀ w ∈ W, M.mulVec w = a • w) ∧ (∀ u ∈ ℓ, M.mulVec u = b • u) ∧
        H ≤ blkGroup F W ℓ := fun e h01 h02 =>
    exists_le_blkGroup_aux H M (b.reindex e.symm) (d ∘ e)
      (fun i => by simpa using hb (e i)) h01 h02 hcomm
  by_cases h01 : d 0 = d 1
  · exact transfer 1 h01 fun h => hnotconst ⟨h01, h⟩
  by_cases h02 : d 0 = d 2
  · have e0 : (Equiv.swap (1 : Fin 3) 2) 0 = 0 := by decide
    have e1 : (Equiv.swap (1 : Fin 3) 2) 1 = 2 := by decide
    have e2 : (Equiv.swap (1 : Fin 3) 2) 2 = 1 := by decide
    exact transfer (Equiv.swap 1 2) (by rw [e0, e1]; exact h02) (by rw [e0, e2]; exact h01)
  by_cases h12 : d 1 = d 2
  · have e0 : (finRotate 3) 0 = 1 := by decide
    have e1 : (finRotate 3) 1 = 2 := by decide
    have e2 : (finRotate 3) 2 = 0 := by decide
    exact transfer (finRotate 3) (by rw [e0, e1]; exact h12)
      (by rw [e0, e2]; exact fun h => h01 h.symm)
  exfalso
  have hd : Function.Injective d := by
    intro i j hij
    fin_cases i <;> fin_cases j
    · rfl
    · exact absurd hij h01
    · exact absurd hij h02
    · exact absurd hij.symm h01
    · rfl
    · exact absurd hij h12
    · exact absurd hij.symm h02
    · exact absurd hij.symm h12
    · rfl
  exact hH (eq_bot_of_distinct' H M b d hb hd hcomm)

end CFSG.RankThree.PartOne.CTP

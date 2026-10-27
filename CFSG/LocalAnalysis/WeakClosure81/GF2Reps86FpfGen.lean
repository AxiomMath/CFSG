module

public import Mathlib.GroupTheory.SpecificGroups.Alternating
import CFSG.LocalAnalysis.ComponentInitial.GroupAlternatingCoverPerm

public section

namespace CFSG.LocalAnalysis.WeakClosure81.GF2Reps86

open Equiv Equiv.Perm CFSG.LocalAnalysis.ComponentInitial

@[expose] def fpfT : Perm (Fin 10) := swap 0 4 * swap 1 5 * swap 2 6 * swap 3 7 * swap 8 9

@[expose] def fpfP : Perm (Fin 10) := swap 0 5 * swap 1 6 * swap 2 7 * swap 3 4 * swap 8 9

theorem fpfT_mul_self : fpfT * fpfT = 1 := by decide +kernel

theorem fpfP_mul_self : fpfP * fpfP = 1 := by decide +kernel

theorem fpfT_apply_ne (i : Fin 10) : fpfT i ≠ i := by
  revert i
  decide +kernel

theorem fpfT_mul_fpfP_pow_four : (fpfT * fpfP) ^ 4 = 1 := by decide +kernel

theorem fpfT_mul_fpfP_sq_ne_one : (fpfT * fpfP) ^ 2 ≠ 1 := by decide +kernel

theorem exists_conj_fpfT_eq_fpfP : ∃ g ∈ alternatingGroup (Fin 10), g * fpfT * g⁻¹ = fpfP :=
  ⟨swap 4 5 * swap 5 6 * swap 6 7 * swap 8 9, mem_alternatingGroup.mpr (by decide +kernel),
    by decide +kernel⟩

private theorem cycleType_eq_replicate_five {s : Perm (Fin 10)} (hs : s * s = 1)
    (hsf : ∀ i, s i ≠ i) : s.cycleType = Multiset.replicate 5 2 := by
  have hord : orderOf s ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [sq, hs])
  have hall : ∀ n ∈ s.cycleType, n = 2 := fun n hn =>
    (Nat.le_of_dvd two_pos ((dvd_of_mem_cycleType hn).trans hord)).antisymm
      (two_le_of_mem_cycleType hn)
  have hsupp : s.support = Finset.univ :=
    Finset.eq_univ_of_forall fun i => mem_support.mpr (hsf i)
  have hsum : s.cycleType.sum = 10 := by
    rw [sum_cycleType, hsupp]
    simp
  have hrep := Multiset.eq_replicate_of_mem hall
  have hcard : Multiset.card s.cycleType = 5 := by
    rw [hrep] at hsum
    simp only [Multiset.sum_replicate, smul_eq_mul] at hsum
    omega
  rw [hrep, hcard]

theorem exists_conj_eq_fpfT {s : Perm (Fin 10)} (hs : s * s = 1) (hsf : ∀ i, s i ≠ i) :
    ∃ g ∈ alternatingGroup (Fin 10), g * s * g⁻¹ = fpfT := by
  obtain ⟨c, hc⟩ := isConj_iff.mp (isConj_iff_cycleType_eq.mpr
    ((cycleType_eq_replicate_five hs hsf).trans
      (cycleType_eq_replicate_five fpfT_mul_self fpfT_apply_ne).symm))
  rcases Int.units_eq_one_or (sign c) with h | h
  · exact ⟨c, mem_alternatingGroup.mpr h, hc⟩
  · refine ⟨swap 8 9 * c, ?_, ?_⟩
    · rw [mem_alternatingGroup, sign_mul, sign_swap (by decide), h]
      rfl
    · have h89 : swap 8 9 * fpfT * (swap 8 9)⁻¹ = fpfT := by decide +kernel
      calc swap 8 9 * c * s * (swap 8 9 * c)⁻¹
          = swap 8 9 * (c * s * c⁻¹) * (swap 8 9)⁻¹ := by group
        _ = fpfT := by rw [hc, h89]

@[expose] def diagHom (e : Fin 5 ⊕ Fin 5 ≃ Fin 10) : Perm (Fin 5) →* Perm (Fin 10) :=
  e.permCongrHom.toMonoidHom.comp
    ((sumCongrHom (Fin 5) (Fin 5)).comp ((MonoidHom.id _).prod (MonoidHom.id _)))

theorem diagHom_apply (e : Fin 5 ⊕ Fin 5 ≃ Fin 10) (σ : Perm (Fin 5)) :
    diagHom e σ = e.permCongr (Perm.sumCongr σ σ) :=
  rfl

theorem diagHom_mem_alternatingGroup (e : Fin 5 ⊕ Fin 5 ≃ Fin 10) {σ : Perm (Fin 5)}
    (hσ : σ ∈ alternatingGroup (Fin 5)) : diagHom e σ ∈ alternatingGroup (Fin 10) := by
  rw [mem_alternatingGroup, diagHom_apply, sign_permCongr, sign_sumCongr,
    mem_alternatingGroup.mp hσ, mul_one]

theorem diagHom_commute (e : Fin 5 ⊕ Fin 5 ≃ Fin 10) (σ : Perm (Fin 5)) :
    diagHom e σ * e.permCongr (Equiv.sumComm (Fin 5) (Fin 5)) =
      e.permCongr (Equiv.sumComm (Fin 5) (Fin 5)) * diagHom e σ := by
  rw [diagHom_apply, ← permCongr_mul, ← permCongr_mul]
  congr 1
  ext x
  rcases x with x | x <;> simp

@[expose] def fpfLab₁ : Fin 5 ⊕ Fin 5 ≃ Fin 10 where
  toFun := Sum.elim ![0, 1, 2, 3, 8] ![4, 5, 6, 7, 9]
  invFun := ![.inl 0, .inl 1, .inl 2, .inl 3, .inr 0, .inr 1, .inr 2, .inr 3, .inl 4, .inr 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

@[expose] def fpfLab₂ : Fin 5 ⊕ Fin 5 ≃ Fin 10 where
  toFun := Sum.elim ![6, 1, 2, 3, 8] ![0, 7, 4, 5, 9]
  invFun := ![.inr 0, .inl 1, .inl 2, .inl 3, .inr 2, .inr 3, .inl 0, .inr 1, .inl 4, .inr 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

@[expose] def fpfLab₃ : Fin 5 ⊕ Fin 5 ≃ Fin 10 where
  toFun := Sum.elim ![0, 1, 2, 3, 8] ![5, 6, 7, 4, 9]
  invFun := ![.inl 0, .inl 1, .inl 2, .inl 3, .inr 3, .inr 0, .inr 1, .inr 2, .inl 4, .inr 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

@[expose] def fpfLab₄ : Fin 5 ⊕ Fin 5 ≃ Fin 10 where
  toFun := Sum.elim ![7, 1, 2, 3, 8] ![0, 4, 5, 6, 9]
  invFun := ![.inr 0, .inl 1, .inl 2, .inl 3, .inr 1, .inr 2, .inr 3, .inl 0, .inl 4, .inr 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem fpfLab₁_swap : fpfLab₁.permCongr (Equiv.sumComm (Fin 5) (Fin 5)) = fpfT := by
  decide +kernel

theorem fpfLab₂_swap :
    fpfLab₂.permCongr (Equiv.sumComm (Fin 5) (Fin 5)) = fpfT * (fpfT * fpfP) ^ 2 := by
  decide +kernel

theorem fpfLab₃_swap : fpfLab₃.permCongr (Equiv.sumComm (Fin 5) (Fin 5)) = fpfP := by
  decide +kernel

theorem fpfLab₄_swap :
    fpfLab₄.permCongr (Equiv.sumComm (Fin 5) (Fin 5)) = fpfP * (fpfT * fpfP) ^ 2 := by
  decide +kernel

private def c₃ : Perm (Fin 5) := swap 0 2 * swap 0 1

private def c₅ : Perm (Fin 5) := swap 0 1 * swap 1 2 * swap 2 3 * swap 3 4

private theorem c₃_mem : c₃ ∈ alternatingGroup (Fin 5) :=
  mem_alternatingGroup.mpr (by decide +kernel)

private theorem c₅_mem : c₅ ∈ alternatingGroup (Fin 5) :=
  mem_alternatingGroup.mpr (by decide +kernel)

private def diagGens (e e' : Fin 5 ⊕ Fin 5 ≃ Fin 10) : Fin 8 → Perm (Fin 10) :=
  ![diagHom e c₃, diagHom e c₅, diagHom e' c₃, diagHom e' c₅,
    (diagHom e c₃)⁻¹, (diagHom e c₅)⁻¹, (diagHom e' c₃)⁻¹, (diagHom e' c₅)⁻¹]

private theorem alternatingGroup_le_closure_diag (e e' : Fin 5 ⊕ Fin 5 ≃ Fin 10)
    (w : Fin 8 → List (Fin 8))
    (hw : ∀ i : Fin 8, altThreeCyclePerm i = ((w i).map (diagGens e e')).prod) :
    alternatingGroup (Fin 10) ≤ Subgroup.closure
      (diagHom e '' (alternatingGroup (Fin 5) : Set (Perm (Fin 5))) ∪
        diagHom e' '' (alternatingGroup (Fin 5) : Set (Perm (Fin 5)))) := by
  set K := Subgroup.closure
    (diagHom e '' (alternatingGroup (Fin 5) : Set (Perm (Fin 5))) ∪
      diagHom e' '' (alternatingGroup (Fin 5) : Set (Perm (Fin 5))))
  have h₁ : diagHom e c₃ ∈ K := Subgroup.subset_closure (Or.inl ⟨c₃, c₃_mem, rfl⟩)
  have h₂ : diagHom e c₅ ∈ K := Subgroup.subset_closure (Or.inl ⟨c₅, c₅_mem, rfl⟩)
  have h₃ : diagHom e' c₃ ∈ K := Subgroup.subset_closure (Or.inr ⟨c₃, c₃_mem, rfl⟩)
  have h₄ : diagHom e' c₅ ∈ K := Subgroup.subset_closure (Or.inr ⟨c₅, c₅_mem, rfl⟩)
  have hg : ∀ j, diagGens e e' j ∈ K := by
    intro j
    fin_cases j
    · exact h₁
    · exact h₂
    · exact h₃
    · exact h₄
    · exact K.inv_mem h₁
    · exact K.inv_mem h₂
    · exact K.inv_mem h₃
    · exact K.inv_mem h₄
  refine (closure_altThreeCyclePerm (n := 8)).symm.le.trans ?_
  rw [Subgroup.closure_le]
  rintro _ ⟨i, rfl⟩
  rw [hw i]
  exact list_prod_mem fun x hx => by
    obtain ⟨j, -, rfl⟩ := List.mem_map.mp hx
    exact hg j

private def words₁₂ : Fin 8 → List (Fin 8) :=
  ![[4, 7, 1, 6, 5, 3], [7, 2, 5, 6, 7, 6, 4], [0, 2, 4, 3, 3, 5, 7], [7, 6, 0, 1, 1, 7],
    [4, 6, 4, 3, 1, 7, 7, 4], [0, 2, 3, 4, 1, 2, 0, 1], [5, 6, 7, 6, 4, 7, 2],
    [2, 0, 1, 1, 7, 7, 2]]

private def words₃₄ : Fin 8 → List (Fin 8) :=
  ![[4, 7, 1, 6, 5, 3], [7, 2, 5, 6, 7, 6, 4], [0, 2, 3, 4, 1, 2, 0, 1], [0, 2, 4, 3, 3, 5, 7],
    [7, 6, 0, 1, 1, 7], [4, 6, 4, 3, 1, 7, 7, 4], [5, 6, 7, 6, 4, 7, 2],
    [2, 0, 1, 1, 7, 7, 2]]

private theorem words₁₂_spec : ∀ i : Fin 8,
    altThreeCyclePerm i = ((words₁₂ i).map (diagGens fpfLab₁ fpfLab₂)).prod := by
  decide +kernel

private theorem words₃₄_spec : ∀ i : Fin 8,
    altThreeCyclePerm i = ((words₃₄ i).map (diagGens fpfLab₃ fpfLab₄)).prod := by
  decide +kernel

theorem alternatingGroup_le_closure_diag₁₂ : alternatingGroup (Fin 10) ≤ Subgroup.closure
    (diagHom fpfLab₁ '' (alternatingGroup (Fin 5) : Set (Perm (Fin 5))) ∪
      diagHom fpfLab₂ '' (alternatingGroup (Fin 5) : Set (Perm (Fin 5)))) :=
  alternatingGroup_le_closure_diag fpfLab₁ fpfLab₂ words₁₂ words₁₂_spec

theorem alternatingGroup_le_closure_diag₃₄ : alternatingGroup (Fin 10) ≤ Subgroup.closure
    (diagHom fpfLab₃ '' (alternatingGroup (Fin 5) : Set (Perm (Fin 5))) ∪
      diagHom fpfLab₄ '' (alternatingGroup (Fin 5) : Set (Perm (Fin 5)))) :=
  alternatingGroup_le_closure_diag fpfLab₃ fpfLab₄ words₃₄ words₃₄_spec

end CFSG.LocalAnalysis.WeakClosure81.GF2Reps86

end

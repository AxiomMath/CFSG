module

public import CFSG.RankThree.PartOne.KFCL.L4Block

public section

namespace CFSG.RankThree.PartOne.KFCL.L4

open Matrix CFSG.RankThree.PartOne.KFCL.BlockSL
open scoped MatrixGroups

variable {K : Type} [Field K] [CharP K 2]

theorem det_permMatrixHom (σ : Equiv.Perm (Fin 4)) : (Matrix.permMatrixHom (R := K) σ).det = 1 := by
  rw [Matrix.permMatrixHom_apply, Matrix.det_permutation]
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ⁻¹) with h | h
  · rw [h]
    simp
  · rw [h]
    simp [CharTwo.neg_eq]

@[expose] def permSL (K : Type) [Field K] [CharP K 2] : Equiv.Perm (Fin 4) →* SL(4, K) where
  toFun σ := ⟨Matrix.permMatrixHom σ, det_permMatrixHom σ⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' _ _ := Subtype.ext (map_mul _ _ _)

theorem coe_permSL (σ : Equiv.Perm (Fin 4)) :
    ((permSL K σ : SL(4, K)) : Matrix (Fin 4) (Fin 4) K) = Matrix.permMatrixHom σ := rfl

omit [CharP K 2] in
theorem permMat_conj_apply (σ : Equiv.Perm (Fin 4)) (M : Matrix (Fin 4) (Fin 4) K) (a b : Fin 4) :
    (Matrix.permMatrixHom (R := K) σ⁻¹ * M * Matrix.permMatrixHom (R := K) σ) a b = M (σ a) (σ b) := by
  simp only [Matrix.permMatrixHom_apply, inv_inv]
  rw [PEquiv.toMatrix_toPEquiv_mul, PEquiv.mul_toMatrix_toPEquiv]
  simp [Matrix.submatrix_apply, Equiv.Perm.inv_def]

theorem permSL_conj_apply (σ : Equiv.Perm (Fin 4)) (x : SL(4, K)) (a b : Fin 4) :
    ((permSL K σ)⁻¹ * x * permSL K σ).1 a b = x.1 (σ a) (σ b) := by
  have : (permSL K σ)⁻¹ = permSL K σ⁻¹ := (map_inv (permSL K) σ).symm
  rw [this, Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, coe_permSL, coe_permSL]
  exact permMat_conj_apply σ x.1 a b

@[expose] def cj (σ : Equiv.Perm (Fin 4)) (x : SL(4, K)) : SL(4, K) :=
  (permSL K σ)⁻¹ * x * permSL K σ

theorem cj_apply (σ : Equiv.Perm (Fin 4)) (x : SL(4, K)) (a b : Fin 4) :
    (cj σ x).1 a b = x.1 (σ a) (σ b) := permSL_conj_apply σ x a b

theorem cj_cj (σ : Equiv.Perm (Fin 4)) (x : SL(4, K)) : cj σ⁻¹ (cj σ x) = x := by
  unfold cj
  rw [map_inv (permSL K) σ]
  group

section Mem

variable {p : ℕ}

theorem cj_mem_torus {σ : Equiv.Perm (Fin 4)} {x : SL(4, K)} (hx : x ∈ torus p K) : cj σ x ∈ torus p K := by
  obtain ⟨d, hd, hdp⟩ := hx
  refine ⟨d ∘ σ, ?_, fun i => hdp (σ i)⟩
  ext a b
  rw [cj_apply, hd]
  by_cases hab : a = b
  · subst hab
    simp
  · have : σ a ≠ σ b := fun h => hab (σ.injective h)
    simp [diagonal_apply_ne _ hab, diagonal_apply_ne _ this]

theorem cj_mem_torus_iff (σ : Equiv.Perm (Fin 4)) (x : SL(4, K)) :
    cj σ x ∈ torus p K ↔ x ∈ torus p K :=
  ⟨fun h => cj_cj σ x ▸ cj_mem_torus h, cj_mem_torus⟩

theorem cj_mem_pairBlock_iff (σ : Equiv.Perm (Fin 4)) (x : SL(4, K)) (s : Finset (Fin 4)) :
    cj σ x ∈ pairBlock K s ↔ x ∈ pairBlock K (s.map σ.toEmbedding) := by
  rw [mem_pairBlock_iff, mem_pairBlock_iff]
  constructor
  · intro h a' b' hab'
    have := h (σ.symm a') (σ.symm b') (by
      intro ⟨ha, hb⟩
      exact hab' ⟨Finset.mem_map_equiv.2 (by simpa using ha), Finset.mem_map_equiv.2 (by simpa using hb)⟩)
    rw [cj_apply] at this
    simpa [Matrix.one_apply] using this
  · intro h a b hab
    have := h (σ a) (σ b) (by
      intro ⟨ha, hb⟩
      exact hab ⟨by simpa using Finset.mem_map_equiv.1 ha, by simpa using Finset.mem_map_equiv.1 hb⟩)
    rw [cj_apply]
    simpa [Matrix.one_apply] using this

theorem cj_mem_hypSub_iff (σ : Equiv.Perm (Fin 4)) (x : SL(4, K)) (s : Finset (Fin 4)) :
    cj σ x ∈ hypSub p K s ↔ x ∈ hypSub p K (s.map σ.toEmbedding) := by
  rw [mem_hypSub_iff, mem_hypSub_iff, cj_mem_torus_iff]
  refine and_congr_right fun _ => ?_
  constructor
  · intro h a' ha' b' hb'
    have ha := Finset.mem_map_equiv.1 ha'
    have hb := Finset.mem_map_equiv.1 hb'
    have := h _ ha _ hb
    rw [cj_apply, cj_apply] at this
    simpa using this
  · intro h a ha b hb
    rw [cj_apply, cj_apply]
    exact h (σ a) (Finset.mem_map_equiv.2 (by simpa using ha)) (σ b)
      (Finset.mem_map_equiv.2 (by simpa using hb))

theorem mem_map_conj_iff {Γ : Type*} [Group Γ] {H : Subgroup Γ} {w x : Γ} :
    x ∈ H.map (MulAut.conj w).toMonoidHom ↔ w⁻¹ * x * w ∈ H := by
  rw [Subgroup.mem_map_equiv, MulAut.conj_symm_apply]

theorem map_conj_pairBlock (σ : Equiv.Perm (Fin 4)) (s : Finset (Fin 4)) :
    (pairBlock K s).map (MulAut.conj (permSL K σ)).toMonoidHom = pairBlock K (s.map σ.toEmbedding) := by
  ext x
  rw [mem_map_conj_iff]
  exact cj_mem_pairBlock_iff σ x s

theorem map_conj_hypSub (σ : Equiv.Perm (Fin 4)) (s : Finset (Fin 4)) :
    (hypSub p K s).map (MulAut.conj (permSL K σ)).toMonoidHom = hypSub p K (s.map σ.toEmbedding) := by
  ext x
  rw [mem_map_conj_iff]
  exact cj_mem_hypSub_iff σ x s

theorem permSL_mem_normalizer_torus (σ : Equiv.Perm (Fin 4)) :
    permSL K σ ∈ Subgroup.normalizer ((torus p K : Subgroup (SL(4, K))) : Set (SL(4, K))) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  have h1 : permSL K σ * x * (permSL K σ)⁻¹ = cj σ⁻¹ x := by
    unfold cj
    rw [map_inv (permSL K) σ]
    simp
  rw [h1, cj_mem_torus_iff]

end Mem

end CFSG.RankThree.PartOne.KFCL.L4

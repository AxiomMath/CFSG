module

public import CFSG.RankThree.PartOne.CTP.Su4Coord
public import CFSG.CharacterTheory.Semidihedral.DihedralQuaternion
public import CFSG.LieType.Steinberg.CentralExt.SUTwo
public import CFSG.RankThree.PartOne.CTP.SpNode
public import CFSG.RankThree.PartOne.CTP.SpPos
public import CFSG.RankThree.PartOne.CTP.Su4Geom

public section

namespace CFSG.RankThree.PartOne.CTP

open Matrix CFSG.ClassicalGroups.Unitary CFSG.LieType.Universal.Unitary
open scoped MatrixGroups

variable {K : Type} [Field K] {σ : K ≃+* K}

theorem ulBlock_mul_of_blk (M N : Matrix (Fin 4) (Fin 4) K) (h02 : M 0 2 = 0) (h03 : M 0 3 = 0)
    (h12 : M 1 2 = 0) (h13 : M 1 3 = 0) : ulBlock (M * N) = ulBlock M * ulBlock N := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [ulBlock, Matrix.mul_apply, Fin.sum_univ_four, Fin.sum_univ_two, h02, h03, h12, h13]

section Conj

variable {Q : GL (Fin 4) K}
  (hQ : conjTr σ (Q : Matrix (Fin 4) (Fin 4) K) * (Q : Matrix (Fin 4) (Fin 4) K) = antidiag 4)

local notation "qv" i => (Q : Matrix (Fin 4) (Fin 4) K) *ᵥ (Pi.single i 1 : Fin 4 → K)

theorem coord_eq_zero_of_mem_span_low {y : Fin 4 → K}
    (hy : (Q : Matrix (Fin 4) (Fin 4) K) *ᵥ y ∈
      Submodule.span K {qv 0, qv 1}) (i : Fin 4) (hi : 2 ≤ i.val) : y i = 0 := by
  obtain ⟨s, t, hst⟩ := Submodule.mem_span_pair.mp hy
  have hy' : y = s • (Pi.single 0 1 : Fin 4 → K) + t • (Pi.single 1 1 : Fin 4 → K) := by
    apply mulVec_injective_of_unit Q
    rw [Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul, hst]
  have hi0 : i ≠ 0 := fun h => by subst h; simp at hi
  have hi1 : i ≠ 1 := fun h => by subst h; simp at hi
  rw [hy']
  simp [hi0, hi1]

theorem coord_eq_zero_of_mem_span_high {y : Fin 4 → K}
    (hy : (Q : Matrix (Fin 4) (Fin 4) K) *ᵥ y ∈
      Submodule.span K {qv 2, qv 3}) (i : Fin 4) (hi : i.val < 2) : y i = 0 := by
  obtain ⟨s, t, hst⟩ := Submodule.mem_span_pair.mp hy
  have hy' : y = s • (Pi.single 2 1 : Fin 4 → K) + t • (Pi.single 3 1 : Fin 4 → K) := by
    apply mulVec_injective_of_unit Q
    rw [Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul, hst]
  have hi2 : i ≠ 2 := fun h => by subst h; simp at hi
  have hi3 : i ≠ 3 := fun h => by subst h; simp at hi
  rw [hy']
  simp [hi2, hi3]

include hQ in
theorem blk_of_stab {B : Subgroup (SUid σ 4)}
    (hL : ∀ b ∈ B, ∀ v ∈ Submodule.span K {qv 0, qv 1}, b • v ∈ Submodule.span K {qv 0, qv 1})
    (hL' : ∀ b ∈ B, ∀ v ∈ Submodule.span K {qv 2, qv 3}, b • v ∈ Submodule.span K {qv 2, qv 3})
    {b : SUid σ 4} (hb : b ∈ B) (i j : Fin 4) (hij : i.val < 2 ↔ ¬ j.val < 2) :
    matS σ ((conjEquiv Q hQ).symm b) i j = 0 := by
  have hs : conjEquiv Q hQ ((conjEquiv Q hQ).symm b) = b := (conjEquiv Q hQ).apply_symm_apply b
  have hcol : matS σ ((conjEquiv Q hQ).symm b) i j =
      (matS σ ((conjEquiv Q hQ).symm b) *ᵥ (Pi.single j 1 : Fin 4 → K)) i := by
    simp
  have hact : b • ((Q : Matrix (Fin 4) (Fin 4) K) *ᵥ (Pi.single j 1 : Fin 4 → K)) =
      (Q : Matrix (Fin 4) (Fin 4) K) *ᵥ
        (matS σ ((conjEquiv Q hQ).symm b) *ᵥ (Pi.single j 1 : Fin 4 → K)) := by
    rw [← smul_conjEquiv hQ, hs]
  rw [hcol]
  by_cases hj : j.val < 2
  · have hi : 2 ≤ i.val := by omega
    have hj' : j = 0 ∨ j = 1 := by fin_cases j <;> simp at hj ⊢
    have hmem : (Q : Matrix (Fin 4) (Fin 4) K) *ᵥ (Pi.single j 1 : Fin 4 → K) ∈
        Submodule.span K {qv 0, qv 1} := by
      rcases hj' with rfl | rfl
      · exact Submodule.subset_span (Set.mem_insert _ _)
      · exact Submodule.subset_span (Set.mem_insert_of_mem _ (Set.mem_singleton _))
    have := hL b hb _ hmem
    rw [hact] at this
    exact coord_eq_zero_of_mem_span_low this i hi
  · have hi : i.val < 2 := by omega
    have hj' : j = 2 ∨ j = 3 := by fin_cases j <;> simp at hj ⊢
    have hmem : (Q : Matrix (Fin 4) (Fin 4) K) *ᵥ (Pi.single j 1 : Fin 4 → K) ∈
        Submodule.span K {qv 2, qv 3} := by
      rcases hj' with rfl | rfl
      · exact Submodule.subset_span (Set.mem_insert _ _)
      · exact Submodule.subset_span (Set.mem_insert_of_mem _ (Set.mem_singleton _))
    have := hL' b hb _ hmem
    rw [hact] at this
    exact coord_eq_zero_of_mem_span_high this i hi

@[expose] noncomputable def ulDet (B : Subgroup (SUid σ 4))
    (hblk : ∀ b ∈ B, ∀ i j : Fin 4, (i.val < 2 ↔ ¬ j.val < 2) →
      matS σ ((conjEquiv Q hQ).symm b) i j = 0) : B →* K where
  toFun b := (ulBlock (matS σ ((conjEquiv Q hQ).symm (b : SUid σ 4)))).det
  map_one' := by
    simp [matS_one, ulBlock]
  map_mul' b b' := by
    have h1 : (conjEquiv Q hQ).symm ((b * b' : B) : SUid σ 4) =
        (conjEquiv Q hQ).symm (b : SUid σ 4) * (conjEquiv Q hQ).symm (b' : SUid σ 4) := by
      rw [Subgroup.coe_mul, map_mul]
    rw [h1, matS_mul, ulBlock_mul_of_blk _ _ (hblk b b.2 0 2 (by decide))
      (hblk b b.2 0 3 (by decide)) (hblk b b.2 1 2 (by decide)) (hblk b b.2 1 3 (by decide)),
      Matrix.det_mul]

include hQ in
theorem eq_map_sbEmb_of_stab [Finite K] (hσ : ∀ c, σ (σ c) = c) {B : Subgroup (SUid σ 4)}
    [Group.IsPerfect B] (hcard : Nat.card B = Nat.card SL(2, K))
    (hL : ∀ b ∈ B, ∀ v ∈ Submodule.span K {qv 0, qv 1}, b • v ∈ Submodule.span K {qv 0, qv 1})
    (hL' : ∀ b ∈ B, ∀ v ∈ Submodule.span K {qv 2, qv 3}, b • v ∈ Submodule.span K {qv 2, qv 3}) :
    B = (sbEmb σ hσ).range.map (conjEquiv Q hQ).toMonoidHom := by
  have hblk : ∀ b ∈ B, ∀ i j : Fin 4, (i.val < 2 ↔ ¬ j.val < 2) →
      matS σ ((conjEquiv Q hQ).symm b) i j = 0 := fun b hb i j hij =>
    blk_of_stab hQ hL hL' hb i j hij
  have hdet : ∀ b ∈ B, (ulBlock (matS σ ((conjEquiv Q hQ).symm b))).det = 1 := fun b hb =>
    perfect_hom_eq_one (ulDet hQ B hblk) ⟨b, hb⟩
  have hle : B ≤ (sbEmb σ hσ).range.map (conjEquiv Q hQ).toMonoidHom := by
    intro b hb
    exact ⟨(conjEquiv Q hQ).symm b, mem_range_sbEmb_of_blk σ hσ _ (hblk b hb) (hdet b hb),
      (conjEquiv Q hQ).apply_symm_apply b⟩
  refine Subgroup.eq_of_le_of_card_ge hle ?_
  rw [Subgroup.card_map_of_injective (conjEquiv Q hQ).injective, natCard_range_sbEmb hσ, hcard]

end Conj

end CFSG.RankThree.PartOne.CTP

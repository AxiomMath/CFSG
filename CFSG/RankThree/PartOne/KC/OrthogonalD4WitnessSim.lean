module

public import CFSG.RankThree.PartOne.KC.OrthogonalD4WitnessBridge
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSemilinearDataEmbedding

public section

namespace CFSG.RankThree.PartOne.KCOrthogonalD4

open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear

section Isometry

variable {K : Type} [Field K] {d : ℕ}

theorem exists_mem_projectiveImage_apply_eq (Q : QuadraticForm K (Fin d → K)) {k : GL (Fin d) K}
    (hk : k ∈ matrixIsometries Q) {g g₀ : matrixDerived Q} (h : k * g.val * k⁻¹ = g₀.val) :
    ∃ β ∈ matrixProjectiveImage Q,
      β (matrixProjectiveProjection Q g) = matrixProjectiveProjection Q g₀ := by
  refine ⟨matrixProjectiveConjugationHom Q (matrixIsometryInclusion Q ⟨k, hk⟩), ⟨_, rfl⟩, ?_⟩
  change matrixProjectiveConjugation Q (matrixIsometryInclusion Q ⟨k, hk⟩)
    (matrixProjectiveProjection Q g) = _
  rw [matrixProjectiveConjugation_mk]
  congr 1
  exact Subtype.ext h

end Isometry

section Centralizer

variable {T : Type*} [Group T]

theorem centralizer_conj_le_of_apply_eq (E : Subgroup (MulAut T)) {β : MulAut T} (hβ : β ∈ E)
    {c c₀ : T} (h : β c = c₀)
    (hE : Subgroup.centralizer ({MulAut.conj c₀} : Set (MulAut T)) ≤ E) :
    Subgroup.centralizer ({MulAut.conj c} : Set (MulAut T)) ≤ E := by
  intro α hα
  have hconj : β * MulAut.conj c * β⁻¹ = MulAut.conj c₀ := by rw [mulAut_conj_conj, h]
  have hα' : α * MulAut.conj c = MulAut.conj c * α :=
    Subgroup.mem_centralizer_singleton_iff.mp hα
  have h1 : β * α * β⁻¹ ∈ Subgroup.centralizer ({MulAut.conj c₀} : Set (MulAut T)) := by
    rw [Subgroup.mem_centralizer_singleton_iff, ← hconj]
    calc β * α * β⁻¹ * (β * MulAut.conj c * β⁻¹) = β * (α * MulAut.conj c) * β⁻¹ := by group
      _ = β * (MulAut.conj c * α) * β⁻¹ := by rw [hα']
      _ = β * MulAut.conj c * β⁻¹ * (β * α * β⁻¹) := by group
  have h2 := hE h1
  have : α = β⁻¹ * (β * α * β⁻¹) * β := by group
  rw [this]
  exact mul_mem (mul_mem (inv_mem hβ) h2) hβ

theorem orderOf_conj_eq_of_apply_eq (β : MulAut T) (c : T) :
    orderOf (MulAut.conj (β c)) = orderOf (MulAut.conj c) := by
  have h : MulAut.conj (β c) = (MulAut.conj β).toMonoidHom (MulAut.conj c) := by
    rw [← mulAut_conj_conj]
    rfl
  rw [h]
  exact orderOf_injective _ (MulAut.conj β).injective _

end Centralizer

end CFSG.RankThree.PartOne.KCOrthogonalD4

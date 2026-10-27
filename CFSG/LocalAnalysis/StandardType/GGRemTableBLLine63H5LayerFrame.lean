module

public import CFSG.LocalAnalysis.StandardType.GGRemTableBLLine63H5LayerDiag
public import CFSG.LocalAnalysis.StandardType.GGTableBUnitaryDvdCodimOne

public section

namespace CFSG.StandardType.Line63.H5

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag CFSG.SectionRank.OddCover CFSG.RankThree.PartOne.KCUnitaryModel
  CFSG.StandardType.TableBUE CFSG.StandardType.TableBUD CFSG.Assembly CFSG.StandardType

section Abstract

variable {R : Type*} [Group R]

theorem map_ggFix_conj (σ a : MulAut R) :
    (ggFix a).map (σ⁻¹ : MulAut R).toMonoidHom = ggFix (σ⁻¹ * a * σ) := by
  ext r
  constructor
  · rintro ⟨x, hx, rfl⟩
    have hx' : a x = x := hx
    show (σ⁻¹ * a * σ) (σ⁻¹ x) = σ⁻¹ x
    rw [MulAut.mul_apply, MulAut.mul_apply, MulAut.apply_inv_self, hx']
  · intro hr
    have h1 : σ⁻¹ (a (σ r)) = r := hr
    refine ⟨σ r, ?_, MulAut.inv_apply_self R σ r⟩
    have h2 := congrArg σ h1
    rwa [MulAut.apply_inv_self] at h2

theorem not_isComponentOf_layer_ggFix_conj (σ a : MulAut R)
    (h : ¬ IsComponentOf (LargeEvenLayer (ggFix (σ⁻¹ * a * σ))) (ggFix (σ⁻¹ * a * σ))) :
    ¬ IsComponentOf (LargeEvenLayer (ggFix a)) (ggFix a) := by
  intro hc
  apply h
  have hf : Function.Injective (σ⁻¹ : MulAut R).toMonoidHom := (σ⁻¹ : MulAut R).injective
  rw [← map_ggFix_conj σ a, largeEvenLayer_map_of_injective _ hf]
  exact isComponentOf_map_of_injective _ hf hc

end Abstract

variable {K : Type} [Field K] {n d : ℕ}

theorem not_isComponentOf_layer_ggFix_of_conj (hKd : UnitaryFieldData 2 n K) {M P D : GL (Fin d) K}
    (hM : M ∈ Subgroup.normalizer (unitarySU 2 n K d : Set (GL (Fin d) K)))
    (hP : P ∈ primeFormUnitary hKd (idGram K d)) (hMP : P⁻¹ * M * P = D)
    (hD : D ∈ Subgroup.normalizer (unitarySU 2 n K d : Set (GL (Fin d) K)))
    (h : ¬ IsComponentOf (LargeEvenLayer (ggFix (TableB.projConj (unitarySU 2 n K d) ⟨D, hD⟩)))
      (ggFix (TableB.projConj (unitarySU 2 n K d) ⟨D, hD⟩))) :
    ¬ IsComponentOf (LargeEvenLayer (ggFix (TableB.projConj (unitarySU 2 n K d) ⟨M, hM⟩)))
      (ggFix (TableB.projConj (unitarySU 2 n K d) ⟨M, hM⟩)) := by
  have hPN : P ∈ Subgroup.normalizer (unitarySU 2 n K d : Set (GL (Fin d) K)) :=
    gu_subset_normalizer hKd (mem_guSet_of_mem_primeFormUnitary hKd hP)
  have e : TableB.projConj (unitarySU 2 n K d) ⟨D, hD⟩ =
      (TableB.projConj (unitarySU 2 n K d) ⟨P, hPN⟩)⁻¹ *
        TableB.projConj (unitarySU 2 n K d) ⟨M, hM⟩ *
        TableB.projConj (unitarySU 2 n K d) ⟨P, hPN⟩ := by
    rw [← map_inv, ← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext hMP.symm
  refine not_isComponentOf_layer_ggFix_conj (TableB.projConj (unitarySU 2 n K d) ⟨P, hPN⟩) _ ?_
  rw [← e]
  exact h

theorem not_isComponentOf_layer_ggFix_of_conj_diag (hKd : UnitaryFieldData 2 n K) (hn : 2 ≤ n)
    {M P : GL (Fin d) K}
    (hM : M ∈ Subgroup.normalizer (unitarySU 2 n K d : Set (GL (Fin d) K)))
    (hP : P ∈ primeFormUnitary hKd (idGram K d)) {τ : Fin d → Kˣ}
    (hMP : P⁻¹ * M * P = diagHom d τ) {v₁ v₂ : Kˣ} (hv : v₁ ≠ v₂) {S₁ S₂ : Finset (Fin d)}
    (hS₁ : ∀ i, i ∈ S₁ ↔ τ i = v₁) (hS₂ : ∀ i, i ∈ S₂ ↔ τ i = v₂) (h₁ : 2 ≤ S₁.card)
    (h₂ : 2 ≤ S₂.card) :
    ¬ IsComponentOf (LargeEvenLayer (ggFix (TableB.projConj (unitarySU 2 n K d) ⟨M, hM⟩)))
      (ggFix (TableB.projConj (unitarySU 2 n K d) ⟨M, hM⟩)) := by
  have hPN : P ∈ Subgroup.normalizer (unitarySU 2 n K d : Set (GL (Fin d) K)) :=
    gu_subset_normalizer hKd (mem_guSet_of_mem_primeFormUnitary hKd hP)
  have hD : P⁻¹ * M * P ∈ Subgroup.normalizer (unitarySU 2 n K d : Set (GL (Fin d) K)) :=
    mul_mem (mul_mem (inv_mem hPN) hM) hPN
  exact not_isComponentOf_layer_ggFix_of_conj hKd hM hP rfl hD
    (not_isComponentOf_layer_ggFix_diag hKd hn hD hMP hv hS₁ hS₂ h₁ h₂)

end CFSG.StandardType.Line63.H5

end

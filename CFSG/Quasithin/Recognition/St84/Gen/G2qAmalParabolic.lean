module

public import CFSG.Quasithin.Recognition.St84.Gen.G2qAmalModel
import all CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X6ResidualG2
import CFSG.Quasithin.H13.NQCatLieCartanG2

public noncomputable section

namespace CFSG.Quasithin.F112R.St84

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.Open

namespace G2q

open CFSG.QuasithinUnique.Vol2Native.L239.Lie.G2 (i0 i1)
open CFSG.QuasithinUnique.Setup.X6 (g2Index inf_eq_of_covBy)

theorem g2Index_zero : g2Index 0 = i0 := Fin.ext rfl

theorem g2Index_one : g2Index 1 = i1 := Fin.ext rfl

section Intersection

variable {K : Type} [Field K]

theorem parabolicSubgroup_one_inf_zero :
    parabolicSubgroup Tag.G2 K {i1} ⊓ parabolicSubgroup Tag.G2 K {i0} = borelGroup Tag.G2 K := by
  obtain ⟨hcov, hinj, -⟩ := exceptional_ordinary_minimal_Borel_intersections Tag.G2 K
  have hc : ∀ i, borelGroup Tag.G2 K ⋖ parabolicSubgroup Tag.G2 K {i} := fun i =>
    (hcov _ (parabolicSubgroup_le_adjointGroup _ _ _)).2 ⟨i, rfl⟩
  exact inf_eq_of_covBy (hc i1) (hc i0) fun h => absurd (hinj h) (by decide)

theorem g2ParA_inf_g2ParB : g2ParA K ⊓ g2ParB K = borelSub Tag.G2 K := by
  ext y
  change (y : ModGL Tag.G2 K) ∈ parabolicSubgroup Tag.G2 K {g2Index 1} ∧
      (y : ModGL Tag.G2 K) ∈ parabolicSubgroup Tag.G2 K {g2Index 0} ↔
    (y : ModGL Tag.G2 K) ∈ borelGroup Tag.G2 K
  rw [g2Index_one, g2Index_zero, ← Subgroup.mem_inf, parabolicSubgroup_one_inf_zero]

theorem mem_g2ParA_inf_g2ParB {y : ↥(adjointGroup Tag.G2 K)} :
    y ∈ g2ParA K ⊓ g2ParB K ↔ (y : ModGL Tag.G2 K) ∈ borelGroup Tag.G2 K := by
  rw [g2ParA_inf_g2ParB]
  exact Subgroup.mem_subgroupOf

end Intersection

section Entrywise

variable {K : Type} [Field K]

theorem entrywise_mem_parabolicSubgroup {τ : Tag} (ρ : K ≃+* K) {J : Set (Fin τ.rank)}
    {g : ModGL τ K} (hg : g ∈ parabolicSubgroup τ K J) :
    Units.map (entrywiseHom ρ.toRingHom) g ∈ parabolicSubgroup τ K J := by
  have hle : parabolicSubgroup τ K J ≤
      (parabolicSubgroup τ K J).comap (Units.map (entrywiseHom ρ.toRingHom)) := by
    refine sup_le (fun b hb => Subgroup.mem_comap.2 ?_) ((Subgroup.closure_le _).2 ?_)
    · exact Subgroup.mem_sup_left (entrywise_mem_borelGroup (σ := ρ) hb)
    · rintro _ ⟨j, hj, rfl⟩
      rw [SetLike.mem_coe, Subgroup.mem_comap, entrywise_weylElt_one ρ j]
      exact Subgroup.mem_sup_right (Subgroup.subset_closure ⟨j, hj, rfl⟩)
  exact hle hg

theorem entrywise_mem_parabolicSubgroup_iff {τ : Tag} (ρ : K ≃+* K) {J : Set (Fin τ.rank)}
    {g : ModGL τ K} :
    Units.map (entrywiseHom ρ.toRingHom) g ∈ parabolicSubgroup τ K J ↔
      g ∈ parabolicSubgroup τ K J := by
  refine ⟨fun h => ?_, entrywise_mem_parabolicSubgroup ρ⟩
  have h' := entrywise_mem_parabolicSubgroup ρ.symm h
  rwa [exactEntrywiseAut_left_inv] at h'

end Entrywise

end G2q

section Normalizer

variable {K : Type} [Field K]

theorem G2q.normalizer_posUnipotentSub :
    Subgroup.normalizer (posUnipotentSub Tag.G2 K : Set ↥(adjointGroup Tag.G2 K)) =
      g2ParA K ⊓ g2ParB K := by
  ext y
  rw [G2q.mem_g2ParA_inf_g2ParB,
    ← CFSG.Quasithin.H13.NQCat.LieCartan.G2.normalizer_posUnipotent_inf_eq]
  constructor
  · intro hy
    refine ⟨Subgroup.mem_normalizer_iff.2 fun h => ⟨fun hh => ?_, fun hh => ?_⟩, y.2⟩
    · have := (Subgroup.mem_normalizer_iff.1 hy ⟨h, posUnipotent_le_adjointGroup hh⟩).1
        (Subgroup.mem_subgroupOf.2 hh)
      exact Subgroup.mem_subgroupOf.1 this
    · have hC : h ∈ adjointGroup Tag.G2 K := by
        have hm := (adjointGroup Tag.G2 K).mul_mem ((adjointGroup Tag.G2 K).mul_mem
          ((adjointGroup Tag.G2 K).inv_mem y.2) (posUnipotent_le_adjointGroup hh)) y.2
        simpa [mul_assoc] using hm
      have := (Subgroup.mem_normalizer_iff.1 hy ⟨h, hC⟩).2 (Subgroup.mem_subgroupOf.2 hh)
      exact Subgroup.mem_subgroupOf.1 this
  · intro hy
    rw [Subgroup.mem_normalizer_iff]
    intro h
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
    exact Subgroup.mem_normalizer_iff.1 hy.1 (h : ModGL Tag.G2 K)

end Normalizer

end CFSG.Quasithin.F112R.St84

end

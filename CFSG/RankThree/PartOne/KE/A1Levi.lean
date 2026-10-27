module

public import CFSG.LieType.Chevalley.LangStronglyOrthogonalCommute
public import CFSG.LieType.Ree.LargeReeSimplePairGeneration
public import CFSG.Adapters.ProjectiveSpecialLinear

public noncomputable section

namespace CFSG.RankThree.PartOne.KE

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
open CFSG.LieType.Ree (canonicalRep_mem_rootLevi)

section Levi

variable {τ : Tag} {L : Type} [Field L]

theorem iform_eq_sum_single (x y : Fin τ.rank → ℤ) :
    iform x y = ∑ i, x i * iform (Pi.single i 1 : Fin τ.rank → ℤ) y := by
  have h : ∀ i, iform (Pi.single i 1 : Fin τ.rank → ℤ) y = ∑ j, τ.symmetrizedCartan i j * y j := by
    intro i
    simp [iform, Pi.single_apply]
  calc iform x y = ∑ i, ∑ j, x i * τ.symmetrizedCartan i j * y j := rfl
    _ = ∑ i, x i * ∑ j, τ.symmetrizedCartan i j * y j := Finset.sum_congr rfl fun i _ => by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun j _ => by ring
    _ = ∑ i, x i * iform (Pi.single i 1 : Fin τ.rank → ℤ) y :=
        Finset.sum_congr rfl fun i _ => by rw [h i]

theorem not_isRoot_add_sub_of_iform_eq_zero (hsl : ∀ j, τ.symmetrizer j j = 1)
    {α θ : Fin τ.rank → ℤ} (hα : IsRoot τ α) (hθ : IsRoot τ θ) (h0 : iform α θ = 0) :
    ¬ IsRoot τ (α + θ) ∧ ¬ IsRoot τ (α - θ) := by
  have hself : ∀ γ : Fin τ.rank → ℤ, IsRoot τ γ → iform γ γ = 2 := fun γ hγ => by
    obtain ⟨j, hj⟩ := iform_self_of_isRoot hγ
    rw [hj, hsl j]
    ring
  have h0' : iform θ α = 0 := by rw [iform_comm, h0]
  refine ⟨fun hr => ?_, fun hr => ?_⟩
  · have h1 := hself _ hr
    rw [iform_add_left, iform_add_right, iform_add_right, h0, h0', hself α hα, hself θ hθ] at h1
    omega
  · have h1 := hself _ hr
    rw [sub_eq_add_neg, iform_add_left, iform_add_right, iform_add_right, iform_neg_left,
      iform_neg_right, iform_neg_right, iform_neg_left, h0, h0', hself α hα, hself θ hθ] at h1
    omega

theorem rootLevi_le_centralizer_rootRankOneGroup (hsl : ∀ j, τ.symmetrizer j j = 1)
    {J : Set (Fin τ.rank)} {θ : Fin τ.rank → ℤ} (hθ : IsRoot τ θ)
    (hJ : ∀ i ∈ J, iform (Pi.single i 1 : Fin τ.rank → ℤ) θ = 0) :
    rootLevi τ L J ≤ Subgroup.centralizer (rootRankOneGroup τ L θ : Set (ModGL τ L)) := by
  unfold rootLevi rootSpan
  refine iSup₂_le fun α hα => ?_
  obtain ⟨hαroot, hαJ⟩ := hα
  have h0 : iform α θ = 0 := by
    rw [iform_eq_sum_single]
    refine Finset.sum_eq_zero fun i _ => ?_
    by_cases hi : i ∈ J
    · rw [hJ i hi, mul_zero]
    · rw [hαJ i hi, zero_mul]
  obtain ⟨hp, hm⟩ := not_isRoot_add_sub_of_iform_eq_zero hsl hαroot hθ h0
  have hcomm := exceptional_Lang_strongly_orthogonal_root_rank_one_commutation τ L hαroot hθ h0 hp
    hm
  have hsub : rootSubgroup τ L α ≤ rootRankOneGroup τ L α := by
    rw [(exceptional_Lang_root_rank_one_torus_transport τ L hαroot).1]
    exact le_sup_left
  intro u hu
  rw [Subgroup.mem_centralizer_iff]
  intro g hg
  exact (hcomm u (hsub hu) g hg).symm

theorem canonicalRep_mem_centralizer_rootRankOneGroup (hsl : ∀ j, τ.symmetrizer j j = 1)
    {J : Set (Fin τ.rank)} {θ : Fin τ.rank → ℤ} (hθ : IsRoot τ θ)
    (hJ : ∀ i ∈ J, iform (Pi.single i 1 : Fin τ.rank → ℤ) θ = 0) {w : WeylGroup τ}
    (hw : w ∈ parabolicWeylGroup τ J) :
    canonicalRep (coxeterSystem τ) L w ∈
      Subgroup.centralizer (rootRankOneGroup τ L θ : Set (ModGL τ L)) :=
  rootLevi_le_centralizer_rootRankOneGroup hsl hθ hJ (canonicalRep_mem_rootLevi hw)

end Levi

end CFSG.RankThree.PartOne.KE

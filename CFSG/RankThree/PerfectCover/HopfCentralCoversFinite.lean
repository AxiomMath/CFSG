module

public import CFSG.RankThree.PerfectCover.HopfCover
import Mathlib.GroupTheory.Schreier

public section

namespace CFSG.RankThree.PerfectCover

universe u

open scoped commutatorElement

theorem finite_hopfCover {X : Type u} [Group X] [Finite X]
    (hX : Group.IsPerfect X) : Finite (HopfCover X) := by
  classical
  let : Group.IsPerfect X := hX
  let U := HopfCover X
  let π : U →* X := hopfCoverMap X
  have hπ : Function.Surjective π := hopfCoverMap_surjective
  let σ : X → U := Function.surjInv hπ
  have hσ : ∀ x, π (σ x) = x := Function.rightInverse_surjInv hπ
  have hdec : ∀ a : U, (σ (π a))⁻¹ * a ∈ Subgroup.center U := by
    intro a
    apply hopfMultiplier_le_center (S := X)
    change π ((σ (π a))⁻¹ * a) = 1
    rw [map_mul, map_inv, hσ, inv_mul_cancel]
  have he : ∀ a : U, a = σ (π a) * ((σ (π a))⁻¹ * a) := by
    intro a
    group
  let f : X × X → commutatorSet U := fun x ↦
    ⟨⁅σ x.1, σ x.2⁆, commutator_mem_commutatorSet _ _⟩
  have hf : Function.Surjective f := by
    rintro ⟨c, a, b, rfl⟩
    refine ⟨(π a, π b), Subtype.ext ?_⟩
    change ⁅σ (π a), σ (π b)⁆ = ⁅a, b⁆
    conv_rhs => rw [he a, he b]
    exact (CFSG.SectionRank.commutatorElement_mul_mem_center _ _ (hdec a) (hdec b)).symm
  let : Finite (commutatorSet U) := Finite.of_surjective f hf
  let : Group.IsPerfect U := hopfCover_isPerfect
  exact Finite.of_surjective (Subgroup.subtype (commutator U)) (fun a ↦
    ⟨⟨a, Group.IsPerfect.mem_commutator⟩, rfl⟩)

theorem finite_hopfMultiplier {X : Type u} [Group X] [Finite X]
    (hX : Group.IsPerfect X) : Finite (hopfMultiplier X) := by
  let : Finite (HopfCover X) := finite_hopfCover hX
  infer_instance

end CFSG.RankThree.PerfectCover

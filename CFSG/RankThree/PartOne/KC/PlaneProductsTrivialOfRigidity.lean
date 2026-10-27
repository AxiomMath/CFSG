module

public import CFSG.RankThree.PartOne.KC.PlaneReduction

public section

namespace CFSG.RankThree.PartOne.KCGeneric

open Subgroup CFSG CFSG.RankThree.LocalRank

variable {M : Type*} [Group M]

theorem commute_of_mem_autThetaT {p : ℕ} {B A : Subgroup M} {β : M} (hβ : β ∈ autThetaT p B A)
    {a : M} (haA : a ∈ A) (ha1 : a ≠ 1) :
    β ∈ inSubgroup (aschbacherSolvableCore p) (B ⊓ centralizer ({a} : Set M)) := by
  have h1 := Subgroup.mem_iInf.mp hβ a
  have h2 := Subgroup.mem_iInf.mp h1 haA
  exact Subgroup.mem_iInf.mp h2 ha1

theorem plane_products_trivial_of_rigidity {p : ℕ} (B A : Subgroup M) (J : M → Subgroup M)
    (hcomm : ∀ a ∈ A, a ≠ 1 →
      ⁅inSubgroup (aschbacherSolvableCore p) (B ⊓ centralizer ({a} : Set M)), A⁆ = ⊥)
    (hJ : ∀ a ∈ A, a ≠ 1 →
      ∀ s ∈ inSubgroup (aschbacherSolvableCore p) (B ⊓ centralizer ({a} : Set M)),
        ∀ j ∈ J a, s * j = j * s)
    (hrigid : ∀ β : M, (∀ a ∈ A, β * a = a * β) → (∀ a ∈ A, a ≠ 1 → ∀ j ∈ J a, β * j = j * β) →
      β = 1) :
    autThetaT p B A = ⊥ ∧ ∀ t ∈ A, t ≠ 1 → autPlaneProduct p B A t = ⊥ := by
  have hI : autThetaT p B A = ⊥ := by
    rw [eq_bot_iff]
    intro β hβ
    rw [Subgroup.mem_bot]
    refine hrigid β (fun a haA => ?_) (fun a haA ha1 j hj => hJ a haA ha1 β
      (commute_of_mem_autThetaT hβ haA ha1) j hj)
    by_cases ha1 : a = 1
    · rw [ha1, mul_one, one_mul]
    · have hS := commute_of_mem_autThetaT hβ haA ha1
      have hmem : β ∈ B ⊓ centralizer ({a} : Set M) := Subgroup.map_subtype_le _ hS
      exact Subgroup.mem_centralizer_singleton_iff.mp hmem.2
  refine ⟨hI, fun t htA ht1 => ?_⟩
  rw [autPlaneProduct, hI, hcomm t htA ht1, sup_bot_eq]

end CFSG.RankThree.PartOne.KCGeneric

module

public import CFSG.RankThree.PartTwo.Sec21.FF81F4Fusion
public import CFSG.RankThree.PartTwo.Sec21.FF81F4Clauses

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF81.F4

open CFSG CFSG.RankThree.PartTwo.Sec21 CFSG.RankThree.PartTwo.Sec21.FF79
  CFSG.RankThree.PartTwo.Sec21.FF79.L41 CFSG.RankThree.PartTwo.Sec21.FF81
open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
open CFSG.Assembly.LowTwoRank (StatedClassicalModel)

section Clause12


variable {X : Type} [Group X] {Y : Subgroup X}

theorem clause_K12 (e : ↥Y ≃* F42C) :
    ∀ x ∈ Y, orderOf x = 3 → ∀ K : Subgroup X, K ≤ Y → Subgroup.zpowers x ⊔ K = Y ⊓ Cen x →
      StatedClassicalModel K .PSp 3 2 1 → ∀ x₁ ∈ K, ∀ x₂ ∈ K, (∃ y ∈ Y, y * x * y⁻¹ = x₁) →
      (∃ y ∈ Y, y * x * y⁻¹ = x₂) → ∃ k ∈ K, k * x₁ * k⁻¹ = x₂ := by
  intro x hxY hx3 K hKY hKx hKm x₁ hx₁ x₂ hx₂ h₁ h₂
  have hx₁Y : x₁ ∈ Y := hKY hx₁
  have hx₂Y : x₂ ∈ Y := hKY hx₂
  have hc3 : orderOf (e ⟨x, hxY⟩) = 3 := by rw [orderOf_e e hxY]; exact hx3
  have hmap := map_toC e hKY
  have e2 : ↥(toC e K) ≃* ↥K :=
    (Subgroup.equivMapOfInjective (toC e K) (ιY e) (ιY_injective e)).trans
      (MulEquiv.subgroupCongr hmap)
  have hKm' : StatedClassicalModel ↥(toC e K) .PSp 3 2 1 :=
    CFSG.Open.StatedAPI.statedClassicalModel_of_mulEquiv e2.symm hKm
  have hsup : Subgroup.zpowers (e ⟨x, hxY⟩) ⊔ toC e K =
      Subgroup.centralizer ({e ⟨x, hxY⟩} : Set F42C) := by
    apply Subgroup.map_injective (ιY_injective e)
    have h1 := map_cen_ιY e (e ⟨x, hxY⟩)
    rw [ιY_e] at h1
    rw [Subgroup.map_sup, MonoidHom.map_zpowers, ιY_e, hmap, h1]
    exact hKx
  have hmem : ∀ z (hz : z ∈ K), e ⟨z, hKY hz⟩ ∈ toC e K := fun z hz => by
    rw [mem_toC, ιY_e]
    exact hz
  obtain ⟨k', hk', hkk⟩ := K12C hc3 (toC e K) hsup hKm'
    (e ⟨x₁, hx₁Y⟩) (hmem x₁ hx₁) (e ⟨x₂, hx₂Y⟩) (hmem x₂ hx₂)
    ((exists_conj_iff e hxY hx₁Y).1 h₁) ((exists_conj_iff e hxY hx₂Y).1 h₂)
  refine ⟨ιY e k', (mem_toC e).1 hk', ?_⟩
  have := congrArg (ιY e) hkk
  simpa [map_mul, map_inv, ιY_e] using this

end Clause12

end CFSG.RankThree.PartTwo.Sec21.FF81.F4

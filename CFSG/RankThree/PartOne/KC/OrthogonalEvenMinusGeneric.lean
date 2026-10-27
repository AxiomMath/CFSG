module

public import CFSG.RankThree.PartOne.KC.OrthogonalEvenMinusFour

public section

namespace CFSG.RankThree.PartOne.KCOrthogonal

open scoped commutatorElement

section Generic

variable {Γ H₀ : Type*} [Group Γ] [Group H₀]

theorem derived_of_index_two_model [Finite H₀] [IsSimpleGroup H₀] [Group.IsPerfect H₀]
    (O : Subgroup Γ) (ρ : H₀ →* Γ) (hρ : Function.Injective ρ) (hle : ρ.range ≤ O)
    (hcard : Nat.card O = 2 * Nat.card H₀) :
    IsSimpleGroup ρ.range ∧ Group.IsPerfect ρ.range ∧ (¬ ∀ x y : ρ.range, x * y = y * x) ∧
      Nat.card ρ.range = Nat.card H₀ ∧ (ρ.range.subgroupOf O).index = 2 ∧
      (ρ.range.subgroupOf O).Normal ∧ ⁅O, O⁆ = ρ.range ∧
      ∀ g ∈ O, Odd (orderOf g) → g ∈ ρ.range := by
  let e : H₀ ≃* ρ.range := MonoidHom.ofInjective hρ
  have hsimple : IsSimpleGroup ρ.range := e.symm.isSimpleGroup
  have hperf : Group.IsPerfect ρ.range := Group.IsPerfect.range ρ
  have hrange : Nat.card ρ.range = Nat.card H₀ := (Nat.card_congr e.toEquiv).symm
  have hpos : 0 < Nat.card H₀ := Nat.card_pos
  have hidx : (ρ.range.subgroupOf O).index = 2 := by
    have h1 := Subgroup.card_mul_index (ρ.range.subgroupOf O)
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv, hrange, hcard] at h1
    exact Nat.eq_of_mul_eq_mul_left hpos (h1.trans (mul_comm _ _))
  have hnormal : (ρ.range.subgroupOf O).Normal := Subgroup.normal_of_index_eq_two hidx
  refine ⟨hsimple, hperf, fun h => ?_, hrange, hidx, hnormal, ?_, ?_⟩
  · exact Group.IsPerfect.not_isMulCommutative (G := ρ.range) ⟨⟨h⟩⟩
  · apply le_antisymm
    · rw [Subgroup.commutator_le]
      intro a ha b hb
      exact Subgroup.mem_subgroupOf.mp
        (commutatorElement_mem_of_index_two _ hidx ⟨a, ha⟩ ⟨b, hb⟩)
    · calc ρ.range = ⁅ρ.range, ρ.range⁆ := Subgroup.commutator_eq_self.symm
        _ ≤ ⁅O, O⁆ := Subgroup.commutator_mono hle hle
  · intro g hg ho
    exact Subgroup.mem_subgroupOf.mp (mem_of_odd_orderOf_of_index_two _ hidx
      (g := (⟨g, hg⟩ : O)) (by rwa [Subgroup.orderOf_mk]))

end Generic

section Transport

variable {K : Type} [Field K] {W W' : Type*} [AddCommGroup W] [Module K W] [AddCommGroup W']
  [Module K W'] {Q : QuadraticForm K W} {Q' : QuadraticForm K W'}
  {H₀ : Type*} [Group H₀]

@[expose] noncomputable def transportHom (e : Q.IsometryEquiv Q') (ρ' : H₀ →* (W' ≃ₗ[K] W')) :
    H₀ →* (W ≃ₗ[K] W) :=
  ((LinearEquiv.autCongr e.toLinearEquiv).symm : (W' ≃ₗ[K] W') ≃* (W ≃ₗ[K] W)).toMonoidHom.comp
    ρ'

theorem transportHom_apply (e : Q.IsometryEquiv Q') (ρ' : H₀ →* (W' ≃ₗ[K] W')) (g : H₀)
    (w : W) : e.toLinearEquiv (transportHom e ρ' g w) = ρ' g (e.toLinearEquiv w) := by
  simp [transportHom, LinearEquiv.autCongr_symm_apply_apply]

theorem transportHom_injective (e : Q.IsometryEquiv Q') (ρ' : H₀ →* (W' ≃ₗ[K] W'))
    (hρ : Function.Injective ρ') : Function.Injective (transportHom e ρ') := by
  intro g₁ g₂ h
  apply hρ
  ext x
  obtain ⟨w, rfl⟩ := e.toLinearEquiv.surjective x
  rw [← transportHom_apply e ρ' g₁, ← transportHom_apply e ρ' g₂, h]

theorem transportHom_mem (e : Q.IsometryEquiv Q') (ρ' : H₀ →* (W' ≃ₗ[K] W'))
    (hρ : ∀ g, ρ' g ∈ TauCeti.QuadraticMap.orthogonalGroup Q') (g : H₀) :
    transportHom e ρ' g ∈ TauCeti.QuadraticMap.orthogonalGroup Q := by
  rw [TauCeti.QuadraticMap.mem_orthogonalGroup_iff]
  intro w
  rw [← e.map_app, ← e.map_app w]
  have h1 : e (transportHom e ρ' g w) = ρ' g (e w) := transportHom_apply e ρ' g w
  rw [h1]
  exact TauCeti.QuadraticMap.map_app_of_mem_orthogonalGroup (hρ g) (e w)

end Transport

end CFSG.RankThree.PartOne.KCOrthogonal

module

public import CFSG.LinearAlgebra.LinearGroups.TwoQuadraticsSolvableLinear
public import CFSG.RankThree.PGroups.SolvableConjugatePairCore

public section

namespace CFSG.RankThree.Coprime

open Subgroup CFSG

theorem solvable_linear_p_stability {p : ℕ} (hp : p.Prime) (hodd : Odd p) {K : Type*} [Field K]
    [CharP K p] {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    {G : Type*} [Group G] [Finite G] [Group.IsSolvable G]
    (ρ : G →* LinearMap.GeneralLinearGroup K V) (halt : 5 ≤ p ∨ Odd (Nat.card G)) {x : G}
    (hx : (((ρ x : LinearMap.GeneralLinearGroup K V) : V →ₗ[K] V) - 1) ^ 2 = 0) :
    (QuotientGroup.mk x : G ⧸ ρ.ker) ∈ pCore p (G ⧸ ρ.ker) := by
  have : Fact p.Prime := ⟨hp⟩
  set Γ := ρ.range with hΓ
  have : Group.IsSolvable Γ := Group.isSolvable_of_surjective ρ.rangeRestrict_surjective
  have : Finite Γ := Finite.of_surjective _ ρ.rangeRestrict_surjective
  set a : Γ := ⟨ρ x, x, rfl⟩ with ha
  obtain ⟨hγp, hconj⟩ := CFSG.LinearGroups.quadratic_linear_p_elements p (ρ x) hx
  have hord : ∃ k : ℕ, orderOf a = p ^ k := by
    have hap : a ^ p = 1 := Subtype.ext (by simpa [ha] using hγp)
    rcases (Nat.dvd_prime hp).mp (orderOf_dvd_of_pow_eq_one hap) with h | h
    · exact ⟨0, by rw [h, pow_zero]⟩
    · exact ⟨1, by rw [h, pow_one]⟩
  have hpair : ∀ g : Γ, IsPGroup p (closure ({a, g⁻¹ * a * g} : Set Γ)) := by
    intro g
    set δ : LinearMap.GeneralLinearGroup K V := (g : LinearMap.GeneralLinearGroup K V)⁻¹ * ρ x * g
    have hδ := hconj g
    set Hc := closure ({ρ x, δ} : Set (LinearMap.GeneralLinearGroup K V)) with hHc
    have hHcΓ : Hc ≤ Γ := by
      rw [hHc, closure_le]
      rintro _ (rfl | rfl)
      · exact ⟨x, rfl⟩
      · exact Γ.mul_mem (Γ.mul_mem (Γ.inv_mem g.2) ⟨x, rfl⟩) g.2
    have : Finite Hc := Finite.of_injective _ (Subgroup.inclusion_injective hHcΓ)
    have hHcs : Group.IsSolvable Hc :=
      Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hHcΓ)
    have hHcalt : 5 ≤ p ∨ Odd (Nat.card Hc) := by
      rcases halt with h | h
      · exact Or.inl h
      · exact Or.inr (h.of_dvd_nat ((Subgroup.card_dvd_of_le hHcΓ).trans
          (Subgroup.card_range_dvd ρ)))
    have hHcp : IsPGroup p Hc :=
      CFSG.LinearGroups.two_quadratics_solvable_linear hp hodd (ρ x) δ hx hδ hHcs hHcalt
    have hmap : (closure ({a, g⁻¹ * a * g} : Set Γ)).map Γ.subtype = Hc := by
      rw [MonoidHom.map_closure, Set.image_pair]
      rfl
    rw [← hmap] at hHcp
    exact hHcp.of_equiv ((closure ({a, g⁻¹ * a * g} : Set Γ)).equivMapOfInjective Γ.subtype
      Γ.subtype_injective).symm
  have haO : a ∈ pCore p Γ := CFSG.RankThree.PGroups.solvable_conjugate_pair_core hp hord hpair
  set e := QuotientGroup.quotientKerEquivRange ρ with he
  have hmap := pCore_map_iso p e.symm
  rw [← hmap]
  refine ⟨a, haO, ?_⟩
  change e.symm a = QuotientGroup.mk x
  rw [MulEquiv.symm_apply_eq]
  rfl

end CFSG.RankThree.Coprime

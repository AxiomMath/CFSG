module

public import CFSG.Permutation.BurnsideSchur.CompositeDegree
public import CFSG.Permutation.BurnsideSchur.PrimeDegree
public import CFSG.Permutation.BurnsideSchur.RegularCyclic

public section

namespace CFSG

open MulAction

open BurnsideSchur

private theorem subgroupOf_normal_of_affine {Ω : Type*} {p : ℕ} (e : Ω ≃ ZMod p)
    {G K : Subgroup (Equiv.Perm Ω)}
    (hK : e.permCongr '' (K : Set (Equiv.Perm Ω)) = {t | ∃ b, ∀ x, t x = x + b})
    (hG : ∀ g ∈ G, ∃ a, ∃ b, ∀ x, e (g x) = a * e x + b) : (K.subgroupOf G).Normal := by
  refine ⟨fun k hk g => ?_⟩
  rw [Subgroup.mem_subgroupOf] at hk ⊢
  obtain ⟨c, hc⟩ : e.permCongr k ∈ {t | ∃ b, ∀ x, t x = x + b} := hK ▸ ⟨k, hk, rfl⟩
  obtain ⟨a, b, hab⟩ := hG g g.2
  have : e.permCongr ((g * k * g⁻¹ : G) : Equiv.Perm Ω) ∈ e.permCongr '' K := by
    refine hK ▸ ⟨a * c, fun x => ?_⟩
    obtain ⟨y, rfl⟩ : ∃ y, e ((g : Equiv.Perm Ω) y) = x :=
      ⟨(g : Equiv.Perm Ω).symm (e.symm x), by simp⟩
    have hky : e ((k : Equiv.Perm Ω) y) = e y + c := by simpa using hc (e y)
    simp only [Equiv.permCongr_apply, Equiv.symm_apply_apply, Subgroup.coe_mul, Subgroup.coe_inv,
      Equiv.Perm.mul_apply, Equiv.Perm.inv_def]
    rw [hab, hab, hky]
    ring
  obtain ⟨k', hk', h⟩ := this
  exact e.permCongr.injective h ▸ hk'

theorem burnside_schur {Ω : Type*} [Finite Ω] (G K : Subgroup (Equiv.Perm Ω))
    (hΩ : 2 ≤ Nat.card Ω) (hKG : K ≤ G) [IsPreprimitive G Ω] [IsCyclic K]
    [IsPretransitive K Ω] (hK : ∀ x : Ω, stabilizer K x = ⊥) :
    IsMultiplyPretransitive G Ω 2 ∨
      ∃ p : ℕ, p.Prime ∧ Nat.card Ω = p ∧ ∃ e : Ω ≃ ZMod p,
        e.permCongr '' (K : Set (Equiv.Perm Ω)) = {t | ∃ b, ∀ x, t x = x + b} ∧
        (∀ g ∈ G, ∃ a ≠ 0, ∃ b, ∀ x, e (g x) = a * e x + b) ∧
        (K.subgroupOf G).Normal := by
  have : Nonempty Ω := (Nat.card_pos_iff.1 (by omega)).1
  have : NeZero (Nat.card Ω) := ⟨by omega⟩
  obtain ⟨e, he⟩ := exists_equiv_zmod_image_eq K hK
  set G' := G.map e.permCongrHom.toMonoidHom
  have hG' (c : ZMod (Nat.card Ω)) : Equiv.addRight c ∈ G' := by
    obtain ⟨k, hk, hke⟩ : Equiv.addRight c ∈ e.permCongr '' K := he ▸ ⟨c, fun x => rfl⟩
    exact ⟨k, hKG hk, hke⟩
  have : IsPreprimitive G' (ZMod (Nat.card Ω)) :=
    (isPreprimitive_map_permCongrHom_iff e G).2 inferInstance
  by_cases hp : (Nat.card Ω).Prime
  · by_cases h2 : IsMultiplyPretransitive G Ω 2
    · exact Or.inl h2
    have := Fact.mk hp
    have h2' : ¬ IsMultiplyPretransitive G' (ZMod (Nat.card Ω)) 2 := by
      rwa [isMultiplyPretransitive_map_permCongrHom_iff]
    have haff (g : Equiv.Perm Ω) (hg : g ∈ G) :
        ∃ a ≠ 0, ∃ b, ∀ x, e (g x) = a * e x + b := by
      obtain ⟨a, ha, b, hab⟩ := exists_affine_of_not_isMultiplyPretransitive hG' h2' ⟨g, hg, rfl⟩
      exact ⟨a, ha, b, fun x => by simpa using hab (e x)⟩
    refine Or.inr ⟨_, hp, rfl, e, he, haff, subgroupOf_normal_of_affine e he fun g hg => ?_⟩
    obtain ⟨a, -, b, hab⟩ := haff g hg
    exact ⟨a, b, hab⟩
  · refine Or.inl ((isMultiplyPretransitive_map_permCongrHom_iff e G 2).1 ?_)
    exact isMultiplyPretransitive_of_not_prime hG' (by rwa [Nat.card_zmod])

end CFSG

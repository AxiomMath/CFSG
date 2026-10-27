module

public import Mathlib.GroupTheory.Perm.Sign
public import Mathlib.GroupTheory.Subgroup.Simple
import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple

public section

namespace CFSG.Quasithin.SimsG4

variable {Γ : Type*} [Group Γ]

theorem G49.exists_index_two_simple_of_mulEquiv_perm {H : Subgroup Γ}
    (φ : ↥H ≃* Equiv.Perm (Fin 6)) :
    ∃ N ≤ H, (∀ g ∈ H, ∀ n ∈ N, g * n * g⁻¹ ∈ N) ∧ IsSimpleGroup ↥N ∧
      (∀ x ∈ H, ∀ g ∈ H, x * (g * x * g⁻¹) ∈ N) ∧ (∀ c ∈ H, c * c ∈ N) ∧
      ∃ t ∈ H, ∀ h ∈ H, h ∈ N ∨ h * t ∈ N := by
  set s : ↥H →* ℤˣ := Equiv.Perm.sign.comp φ.toMonoidHom with hs
  have hmem : ∀ (h : Γ) (hh : h ∈ H), h ∈ s.ker.map H.subtype ↔ s ⟨h, hh⟩ = 1 := by
    intro h hh
    constructor
    · rintro ⟨m, hm, hmh⟩
      have hm' : m = ⟨h, hh⟩ := Subtype.ext hmh
      rw [← hm']
      exact hm
    · intro h1
      exact ⟨⟨h, hh⟩, h1, rfl⟩
  have hker : s.ker = (alternatingGroup (Fin 6)).comap φ.toMonoidHom := by
    rw [hs, ← MonoidHom.comap_ker]
    rfl
  haveI : IsSimpleGroup ↥(alternatingGroup (Fin 6)) := alternatingGroup.isSimpleGroup (by simp)
  have e : ↥(s.ker.map H.subtype) ≃* ↥(alternatingGroup (Fin 6)) :=
    (Subgroup.equivMapOfInjective s.ker H.subtype H.subtype_injective).symm.trans <|
      (MulEquiv.subgroupCongr hker).trans <|
        (Subgroup.equivMapOfInjective _ φ.toMonoidHom φ.injective).trans
          (MulEquiv.subgroupCongr (Subgroup.map_comap_eq_self_of_surjective φ.surjective _))
  have hswap : s (φ.symm (Equiv.swap 0 1)) = -1 := by
    rw [hs, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.apply_symm_apply,
      Equiv.Perm.sign_swap (by decide)]
  refine ⟨s.ker.map H.subtype, Subgroup.map_subtype_le _, ?_, e.isSimpleGroup, ?_, ?_,
    φ.symm (Equiv.swap 0 1), (φ.symm (Equiv.swap 0 1)).2, ?_⟩
  · intro g hg n hn
    have hnH : n ∈ H := Subgroup.map_subtype_le _ hn
    rw [hmem _ (H.mul_mem (H.mul_mem hg hnH) (H.inv_mem hg))]
    change s (⟨g, hg⟩ * ⟨n, hnH⟩ * ⟨g, hg⟩⁻¹) = 1
    rw [map_mul, map_mul, map_inv, (hmem n hnH).mp hn, mul_one, mul_inv_cancel]
  · intro x hx g hg
    rw [hmem _ (H.mul_mem hx (H.mul_mem (H.mul_mem hg hx) (H.inv_mem hg)))]
    change s (⟨x, hx⟩ * (⟨g, hg⟩ * ⟨x, hx⟩ * ⟨g, hg⟩⁻¹)) = 1
    rw [map_mul, map_mul, map_mul, map_inv, mul_comm (s ⟨g, hg⟩), mul_inv_cancel_right,
      Int.units_mul_self]
  · intro c hc
    rw [hmem _ (H.mul_mem hc hc)]
    change s (⟨c, hc⟩ * ⟨c, hc⟩) = 1
    rw [map_mul, Int.units_mul_self]
  · intro h hh
    rcases Int.units_eq_one_or (s ⟨h, hh⟩) with h1 | h1
    · exact Or.inl ((hmem h hh).mpr h1)
    · refine Or.inr ((hmem _ (H.mul_mem hh (φ.symm (Equiv.swap 0 1)).2)).mpr ?_)
      change s (⟨h, hh⟩ * φ.symm (Equiv.swap 0 1)) = 1
      rw [map_mul, h1, hswap]
      decide

end CFSG.Quasithin.SimsG4

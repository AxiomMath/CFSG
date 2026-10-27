module

public import CFSG.Quasithin.Recognition.St84.Gen.NatSecDefs

public section

namespace CFSG.Quasithin.F112R.St84

open scoped MatrixGroups

variable {G G' : Type*} [Group G] [Group G']

theorem IsNatSecOf.of_mulEquiv {F : Type*} [Field F] {L E N : Subgroup G}
    {L' E' N' : Subgroup G'} (e : ↥L ≃* ↥L') (hE : E ≤ L) (hE' : E' ≤ L')
    (hEe : ∀ x : ↥L, (x : G) ∈ E ↔ ((e x : ↥L') : G') ∈ E')
    (hNe : ∀ x : ↥L, (x : G) ∈ N ↔ ((e x : ↥L') : G') ∈ N')
    {α : ↥L →* SL(2, F)} (h : IsNatSecOf L E N α) :
    IsNatSecOf L' E' N' (α.comp e.symm.toMonoidHom) := by
  obtain ⟨β, hβsurj, hβker, hβconj⟩ := h
  let f : ↥E' →* G := L.subtype.comp (e.symm.toMonoidHom.comp (Subgroup.inclusion hE'))
  let φ : ↥E' →* ↥E := f.codRestrict E fun x =>
    (hEe (e.symm (Subgroup.inclusion hE' x))).mpr (by simpa using x.2)
  have hφ_val : ∀ x : ↥E',
      ((φ x : ↥E) : G) = ((e.symm (Subgroup.inclusion hE' x) : ↥L) : G) :=
    fun _ => rfl
  have hφ_surj : Function.Surjective φ := by
    intro y
    refine ⟨⟨e (Subgroup.inclusion hE y), (hEe (Subgroup.inclusion hE y)).mp ?_⟩, ?_⟩
    · simpa using y.2
    · apply Subtype.ext
      change ((e.symm (e (Subgroup.inclusion hE y)) : ↥L) : G) = (y : G)
      simp
  refine ⟨β.comp φ, hβsurj.comp hφ_surj, ?_, ?_⟩
  · ext x
    have hβmem : ∀ y : ↥E, β y = 1 ↔ (y : G) ∈ N := by
      intro y
      rw [← MonoidHom.mem_ker, hβker, Subgroup.mem_subgroupOf]
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, hβmem, Subgroup.mem_subgroupOf]
    have h := hNe (e.symm (Subgroup.inclusion hE' x))
    rw [← hφ_val x] at h
    simpa using h
  · intro ℓ' u' v' hv
    have hv' : Subgroup.inclusion hE' v' = ℓ' * Subgroup.inclusion hE' u' * ℓ'⁻¹ := by
      apply Subtype.ext
      simpa using hv
    have hvG : ((φ v' : ↥E) : G) =
        ((e.symm ℓ' : ↥L) : G) * ((φ u' : ↥E) : G) * (((e.symm ℓ' : ↥L) : G))⁻¹ := by
      rw [hφ_val v', hφ_val u']
      simpa using congrArg (fun z : ↥L' => ((e.symm z : ↥L) : G)) hv'
    simpa using hβconj (e.symm ℓ') (φ u') (φ v') hvG

end CFSG.Quasithin.F112R.St84

end

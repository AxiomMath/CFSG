module

public import CFSG.LargeExtraspecial.S5Comp

public section

namespace CFSG.GGQ2Prime

open Subgroup CFSG.Open

theorem component_conj_eq {G : Type*} [Group G] [Finite G]
    {p : ℕ} {C L : Subgroup G} (hL : IsComponentOf L C)
    (hcyc : ∀ S : Subgroup G, S ≤ centralizer (L : Set G) → IsPGroup p S → IsCyclic S)
    {S : Subgroup G} (hSL : S ≤ L) (hSp : IsPGroup p S) (hSnc : ¬ IsCyclic S) {c : G}
    (hc : c ∈ C) : L.map (MulAut.conj c).toMonoidHom = L := by
  by_contra hne
  have hLc := CFSG.LargeExtraspecial.S5.isComponentOf_map_conj hL hc
  set Lc := L.map (MulAut.conj c).toMonoidHom
  have hle : S.map (MulAut.conj c).toMonoidHom ≤ centralizer (L : Set G) := by
    rintro _ ⟨s, hs, rfl⟩
    rw [mem_centralizer_iff]
    intro l hl
    exact (CFSG.LargeExtraspecial.S5.mul_comm_of_isComponentOf_ne hL hLc (Ne.symm hne) hl
      ⟨s, hSL hs, rfl⟩)
  have hSc : IsPGroup p (S.map (MulAut.conj c).toMonoidHom) := hSp.map _
  have := hcyc _ hle hSc
  apply hSnc
  have e : S ≃* S.map (MulAut.conj c).toMonoidHom :=
    S.equivMapOfInjective _ (MulAut.conj c).injective
  exact isCyclic_of_surjective e.symm.toMonoidHom e.symm.surjective

theorem component_normal {G : Type*} [Group G] [Finite G]
    {p : ℕ} {C L : Subgroup G} (hL : IsComponentOf L C)
    (hcyc : ∀ S : Subgroup G, S ≤ centralizer (L : Set G) → IsPGroup p S → IsCyclic S)
    {S : Subgroup G} (hSL : S ≤ L) (hSp : IsPGroup p S) (hSnc : ¬ IsCyclic S) :
    C ≤ normalizer (L : Set G) := by
  intro c hc
  rw [mem_normalizer_iff]
  intro l
  have h := component_conj_eq hL hcyc hSL hSp hSnc hc
  constructor
  · intro hl
    rw [← h]; exact ⟨l, hl, rfl⟩
  · intro hl
    have h' := component_conj_eq hL hcyc hSL hSp hSnc (inv_mem hc)
    rw [← h'] at ⊢
    refine ⟨c * l * c⁻¹, hl, ?_⟩
    simp [MulAut.conj_apply, mul_assoc]

end CFSG.GGQ2Prime

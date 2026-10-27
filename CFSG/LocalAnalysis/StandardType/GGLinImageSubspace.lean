module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveWeylE6QTwoSixAux

public section

namespace CFSG.StandardType

variable {G : Type} [Group G] {p : ℕ} {Bs : Subgroup G} {V : Type} [AddCommGroup V]
  [Module (ZMod p) V]

theorem exists_le_ggLinImage_eq_of_addEquiv (ι : Additive ↥Bs ≃+ V) (U : Submodule (ZMod p) V) :
    ∃ A : Subgroup G, A ≤ Bs ∧ ggLinImage (p := p) ι A = U := by
  classical
  let A₀ : Subgroup ↥Bs := AddSubgroup.toSubgroup' (U.toAddSubgroup.comap ι.toAddMonoidHom)
  have hsub : (A₀.map Bs.subtype).subgroupOf Bs = A₀ := by
    ext x
    simp only [Subgroup.mem_subgroupOf, Subgroup.mem_map]
    constructor
    · rintro ⟨a, ha, hax⟩
      rwa [Subtype.ext hax] at ha
    · intro hx
      exact ⟨x, hx, rfl⟩
  refine ⟨A₀.map Bs.subtype, Subgroup.map_subtype_le A₀, ?_⟩
  ext v
  rw [mem_ggLinImage, ← Subgroup.mem_subgroupOf, hsub]
  change Additive.ofMul (Additive.toMul (ι.symm v)) ∈
      U.toAddSubgroup.comap ι.toAddMonoidHom ↔ v ∈ U
  rw [AddSubgroup.mem_comap, AddEquiv.coe_toAddMonoidHom]
  simp only [ofMul_toMul, AddEquiv.apply_symm_apply, Submodule.mem_toAddSubgroup]

end CFSG.StandardType

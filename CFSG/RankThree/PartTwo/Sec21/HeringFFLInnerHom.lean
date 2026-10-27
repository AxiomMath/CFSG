module

public import Mathlib.GroupTheory.Subgroup.Centralizer
public import Mathlib.Data.Finset.Attr

public section

namespace CFSG.RankThree.PartTwo.Sec21

theorem exists_inner_hom {G : Type} [Group G] {X : Subgroup G} (hZ : Subgroup.center ↥X = ⊥)
    (hinn : ∀ α : MulAut ↥X, ∃ y : ↥X, α = MulAut.conj y) :
    ∃ φ : ↥(Subgroup.normalizer (X : Set G)) →* ↥X,
      ∀ g : ↥(Subgroup.normalizer (X : Set G)), ∀ x ∈ X,
        (g : G) * x * (g : G)⁻¹ = (φ g : G) * x * (φ g : G)⁻¹ := by
  have hinj : Function.Injective (MulAut.conj : ↥X →* MulAut ↥X) := by
    rw [injective_iff_map_eq_one]
    intro y hy
    have hyc : ∀ z : ↥X, y * z * y⁻¹ = z := fun z => by
      have h := congrArg (fun f : MulAut ↥X => f z) hy
      simpa [MulAut.conj_apply] using h
    have hy' : y ∈ Subgroup.center ↥X := by
      rw [Subgroup.mem_center_iff]
      intro z
      exact (mul_inv_eq_iff_eq_mul.mp (hyc z)).symm
    rw [hZ, Subgroup.mem_bot] at hy'
    exact hy'
  have hsurj : Function.Surjective (MulAut.conj : ↥X →* MulAut ↥X) := fun α => by
    obtain ⟨y, hy⟩ := hinn α
    exact ⟨y, hy.symm⟩
  let c : ↥X ≃* MulAut ↥X :=
    MulEquiv.ofBijective (MulAut.conj : ↥X →* MulAut ↥X) ⟨hinj, hsurj⟩
  refine ⟨c.symm.toMonoidHom.comp (Subgroup.normalizerMonoidHom X), ?_⟩
  intro g x hx
  have hc : MulAut.conj (c.symm (Subgroup.normalizerMonoidHom X g)) =
      Subgroup.normalizerMonoidHom X g := c.apply_symm_apply _
  have h1 := congrArg (fun f : MulAut ↥X => f (⟨x, hx⟩ : ↥X)) hc
  simp only [MulAut.conj_apply] at h1
  have h2 := congrArg Subtype.val h1
  simp only [Subgroup.coe_mul, Subgroup.coe_inv,
    Subgroup.normalizerMonoidHom_apply_apply_coe] at h2
  simpa [MonoidHom.comp_apply] using h2.symm

end CFSG.RankThree.PartTwo.Sec21

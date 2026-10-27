module

public import CFSG.OddTranspositions.PartThree.Eleven.Wong.CentData

public section

namespace CFSG.OddTranspositions.PartThree.Wong

open Subgroup

namespace WongHyp

variable {G : Type} [Group G] {t : G} {L₁ L₂ : Subgroup G}

theorem exists_swapData (h : WongHyp t L₁ L₂) {u : G} (hu : orderOf u = 2) (huK : u ∉ L₁ ⊔ L₂)
    (hL : L₁.map (MulAut.conj u).toMonoidHom = L₂) :
    ∃ D : SwapData G, D.t = t ∧ D.u = u ∧ D.i1.range = L₁ ∧ D.i2.range = L₂ := by
  obtain ⟨e⟩ := h.equiv₁
  let i1 : SL5 →* G := L₁.subtype.comp e.symm.toMonoidHom
  let i2 : SL5 →* G := (MulAut.conj u⁻¹).toMonoidHom.comp i1
  have hu2 : u * u = 1 := by
    rw [← pow_two, ← hu]
    exact pow_orderOf_eq_one u
  have huinv : u⁻¹ = u := inv_eq_of_mul_eq_one_right hu2
  have hr1 : i1.range = L₁ := by
    rw [show i1 = L₁.subtype.comp e.symm.toMonoidHom from rfl,
      MonoidHom.range_comp, MonoidHom.range_eq_top.mpr e.symm.surjective,
      Subgroup.map_top, Subgroup.range_subtype]
  have hr2 : i2.range = L₂ := by
    rw [show i2 = (MulAut.conj u⁻¹).toMonoidHom.comp i1 from rfl,
      MonoidHom.range_comp, hr1, huinv, hL]
  let D : SwapData G :=
    { i1 := i1,
      i2 := i2,
      t := t,
      u := u,
      hyp := by rw [hr1, hr2]; exact h,
      inj1 := by
        intro x y hxy
        exact e.symm.injective (Subtype.ext hxy),
      inj2 := by
        intro x y hxy
        have h1xy : i1 x = i1 y := (MulAut.conj u⁻¹).injective hxy
        exact e.symm.injective (Subtype.ext h1xy),
      orderOf_u := hu,
      swap := by
        intro x
        show u⁻¹ * i1 x * u = (MulAut.conj u⁻¹) (i1 x)
        rw [MulAut.conj_apply, inv_inv, huinv],
      u_not_mem := by rw [hr1, hr2]; exact huK }
  exact ⟨D, rfl, rfl, hr1, hr2⟩

end WongHyp

end CFSG.OddTranspositions.PartThree.Wong

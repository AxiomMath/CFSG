module

public import CFSG.Blueprint.NativeSporadic

public section

namespace CFSG.RankThree.PartTwo.J2Residue

open CFSG.Blueprint.NativeSporadic

variable {L : Type*} [Group L] {R M : Subgroup L} [R.Normal] [M.Normal]

noncomputable def conjActionJ2 (hRM : ∀ r ∈ R, ∀ m ∈ M, r * m = m * r) (ψ : L ⧸ R ≃* J2) :
    J2 →* MulAut ↥M :=
  (QuotientGroup.lift R (MulAut.conjNormal (H := M)) fun r hr => by
    rw [MonoidHom.mem_ker]
    ext m
    rw [MulAut.conjNormal_apply, hRM r hr m m.2, mul_inv_cancel_right]
    rfl).comp ψ.symm.toMonoidHom

theorem conjActionJ2_mk (hRM : ∀ r ∈ R, ∀ m ∈ M, r * m = m * r) (ψ : L ⧸ R ≃* J2) (ℓ : L)
    (m : M) : ((conjActionJ2 hRM ψ (ψ ℓ) m : M) : L) = ℓ * m * ℓ⁻¹ := by
  rw [conjActionJ2, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_apply,
    QuotientGroup.lift_mk, MulAut.conjNormal_apply]

end CFSG.RankThree.PartTwo.J2Residue

module

public import Mathlib.Algebra.Group.Subgroup.Basic
public import Mathlib.Algebra.GroupWithZero.Action.Basic

public section

namespace CFSG.RankThree.GF2n.Stroth80

theorem exists_addAut_hom_of_range {R H : Type*} [Group R] [Group H] (φ : R →* H)
    {S : Subgroup H} (hS : φ.range = S) {Y : Type*} [AddCommGroup Y] [DistribMulAction R Y]
    (hker : ∀ x ∈ φ.ker, ∀ a : Y, x • a = a) :
    ∃ π : ↥S →* Multiplicative (AddAut Y),
      ∀ (x : R) (hx : φ x ∈ S) (a : Y), π ⟨φ x, hx⟩ a = x • a := by
  subst hS
  let ρ : R →* Multiplicative (AddAut Y) := DistribMulAction.toAddAut R Y
  have hρker : φ.ker ≤ ρ.ker := by
    intro x hx
    rw [MonoidHom.mem_ker]
    apply Multiplicative.toAdd.injective
    apply AddEquiv.ext
    intro a
    exact hker x hx a
  have hrr : φ.rangeRestrict.ker ≤ ρ.ker := by
    rw [MonoidHom.ker_rangeRestrict]
    exact hρker
  let L : ↥φ.range →* Multiplicative (AddAut Y) :=
    MonoidHom.liftOfSurjective φ.rangeRestrict
      (MonoidHom.rangeRestrict_surjective φ) ⟨ρ, hrr⟩
  refine ⟨L, fun x hx a => ?_⟩
  have key : L ⟨φ x, hx⟩ = ρ x :=
    MonoidHom.liftOfRightInverse_comp_apply φ.rangeRestrict _ _ ⟨ρ, hrr⟩ x
  rw [key]
  rfl

end CFSG.RankThree.GF2n.Stroth80

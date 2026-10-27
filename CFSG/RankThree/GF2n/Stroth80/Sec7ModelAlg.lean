module

public import Mathlib.Algebra.Group.End
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.SetLike

public section

namespace CFSG.RankThree.GF2n.Stroth80

theorem sec7_psi_conj {E : Type*} [AddCommGroup E] {Γ : Type*} [Group Γ]
    (ρ : Γ →* Multiplicative (AddAut E)) (g g' : Γ) (e : E) :
    (ρ (g' * g * g'⁻¹)).toAdd e - e =
      (ρ g').toAdd ((ρ g).toAdd ((ρ g').toAdd.symm e) - (ρ g').toAdd.symm e) := by
  have h : (ρ (g' * g * g'⁻¹)).toAdd e = (ρ g').toAdd ((ρ g).toAdd ((ρ g').toAdd.symm e)) := by
    simp [map_mul, map_inv, AddAut.mul_apply, AddAut.inv_apply]
  rw [h, map_sub, AddEquiv.apply_symm_apply]

end CFSG.RankThree.GF2n.Stroth80

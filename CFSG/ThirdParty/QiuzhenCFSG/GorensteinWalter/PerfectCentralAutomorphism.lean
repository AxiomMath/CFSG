module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Defs
public import Mathlib.GroupTheory.IsPerfect
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

/-!
# Perfect groups have no nontrivial central automorphism discrepancy

This is the lifting step used when an ambient action is trivial on a
centerless component quotient.  Two automorphisms whose pointwise quotient
is central agree on commutators, hence agree everywhere on a perfect group.
-/

noncomputable section

namespace CFSG.GorensteinWalter

universe u

/-- Two automorphisms of a perfect group that differ pointwise by central
elements are equal. -/
public theorem perfect_central_automorphism_eq
    {E : Type u} [Group E]
    (hperf : Group.IsPerfect E) (α β : E ≃* E)
    (hdelta : ∀ x : E, α x * (β x)⁻¹ ∈ Subgroup.center E) :
    α = β := by
  apply MulEquiv.ext
  intro x
  let : Bracket E E := commutatorElement
  have hcomm : ∀ a b : E, α ⁅a, b⁆ = β ⁅a, b⁆ := by
    intro a b
    have hza := Subgroup.mem_center_iff.mp (hdelta a)
    have hzb := Subgroup.mem_center_iff.mp (hdelta b)
    have htarget : ⁅α a, α b⁆ = ⁅β a, β b⁆ := by
      rw [show α a = (α a * (β a)⁻¹) * β a by group,
        show α b = (α b * (β b)⁻¹) * β b by group]
      let za : E := α a * (β a)⁻¹
      let zb : E := α b * (β b)⁻¹
      have hza_center : za ∈ Subgroup.center E := by
        simpa [za] using hdelta a
      have hzb_center : zb ∈ Subgroup.center E := by
        simpa [zb] using hdelta b
      have hleft : ∀ z x y : E, z ∈ Subgroup.center E →
          ⁅z * x, y⁆ = ⁅x, y⁆ := by
        intro z x y hz
        rw [commutatorElement_mul_left_eq_conj_mul]
        have hzy : ⁅z, y⁆ = 1 := by
          rw [commutatorElement_eq_one_iff_mul_comm]
          exact (Subgroup.mem_center_iff.mp hz y).symm
        have hzc : z * ⁅x, y⁆ * z⁻¹ = ⁅x, y⁆ := by
          rw [(Subgroup.mem_center_iff.mp hz ⁅x, y⁆).symm]
          simp
        rw [hzy, hzc]
        simp
      have hright : ∀ z x y : E, z ∈ Subgroup.center E →
          ⁅x, y * z⁆ = ⁅x, y⁆ := by
        intro z x y hz
        rw [commutatorElement_mul_right_eq_mul_conj]
        have hxy : ⁅x, z⁆ = 1 := by
          rw [commutatorElement_eq_one_iff_mul_comm]
          exact Subgroup.mem_center_iff.mp hz x
        have hzc : z * ⁅x, y⁆ * z⁻¹ = ⁅x, y⁆ := by
          rw [(Subgroup.mem_center_iff.mp hz ⁅x, y⁆).symm]
          simp
        rw [hxy]
        simpa [mul_assoc] using hzc
      rw [hleft za (β a) (zb * β b) hza_center]
      rw [show zb * β b = β b * zb by
        exact (Subgroup.mem_center_iff.mp hzb_center (β b)).symm]
      rw [hright zb (β a) (β b) hzb_center]
    simpa only [map_commutatorElement] using htarget
  have hx : x ∈ ⁅(⊤ : Subgroup E), (⊤ : Subgroup E)⁆ := by
    have htop : Group.IsPerfect (↥(⊤ : Subgroup E)) := by
      let : Group.IsPerfect E := hperf
      infer_instance
    have hcommtop : ⁅(⊤ : Subgroup E), (⊤ : Subgroup E)⁆ = ⊤ :=
      (Subgroup.isPerfect_iff (H := (⊤ : Subgroup E))).mp htop
    rw [hcommtop]
    trivial
  rw [Subgroup.commutator_def] at hx
  refine Subgroup.closure_induction (p := fun y _hy => α y = β y)
    ?_ ?_ ?_ ?_ hx
  · intro y hy
    rcases hy with ⟨a, _ha, b, _hb, rfl⟩
    exact hcomm a b
  · simp
  · intro a b _ha _hb ha hb
    rw [map_mul, ha, hb, map_mul]
  · intro a _ha ha
    rw [map_inv, ha, map_inv]

end CFSG.GorensteinWalter

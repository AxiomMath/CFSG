module

public import CFSG.ThirdParty.QiuzhenCFSG.Glauberman.MinimalNormalPSubgroupGLAction

namespace CFSG
end CFSG
open CFSG

/-!
# Quadratic commutators as square-zero linear perturbations
-/

namespace CFSG.Glauberman

open scoped Pointwise commutatorElement IsMulCommutative

universe u

/-- A quadratic commutator acting nontrivially by conjugation is a nonzero
square-zero perturbation of the identity on an elementary abelian normal subgroup. -/
public theorem quotient_conjugation_sub_one_sq_eq_zero_and_ne_zero
    {p : ℕ} [Fact p.Prime] {Q : Type u} [Group Q]
    (H : Subgroup Q) [H.Normal] [IsElementaryAbelian p H]
    (ρ : Q ⧸ Subgroup.centralizer (H : Set Q) →*
      LinearMap.GeneralLinearGroup (ZMod p) (Additive H))
    (heval : ∀ (q : Q) (h : Additive H),
      Additive.toMul
        (((ρ (QuotientGroup.mk' (Subgroup.centralizer (H : Set Q)) q) :
          LinearMap.GeneralLinearGroup (ZMod p) (Additive H)) :
            Additive H →ₗ[ZMod p] Additive H) h) =
        MulAut.conjNormal (H := H) q (Additive.toMul h))
    (x : Q)
    (hcomm : ⁅⁅H, Subgroup.zpowers x⁆, Subgroup.zpowers x⁆ = ⊥)
    (hx : x ∉ Subgroup.centralizer (H : Set Q)) :
    ((ρ (QuotientGroup.mk' (Subgroup.centralizer (H : Set Q)) x) :
        Additive H →ₗ[ZMod p] Additive H) - 1) ^ 2 = 0 ∧
      (ρ (QuotientGroup.mk' (Subgroup.centralizer (H : Set Q)) x) :
        Additive H →ₗ[ZMod p] Additive H) - 1 ≠ 0 := by
  constructor
  · apply LinearMap.ext
    intro h
    apply Additive.toMul.injective
    apply Subtype.ext
    let A : Additive H →ₗ[ZMod p] Additive H :=
      (ρ (QuotientGroup.mk' (Subgroup.centralizer (H : Set Q)) x) :
        Additive H →ₗ[ZMod p] Additive H)
    change ((Additive.toMul ((A - 1) ((A - 1) h)) : H) : Q) = 1
    simp only [LinearMap.sub_apply, Module.End.one_apply, map_sub]
    simp only [toMul_sub, div_eq_mul_inv, Subgroup.coe_mul, Subgroup.coe_inv]
    have hAeval (v : Additive H) :
        ((Additive.toMul (A v) : H) : Q) =
          x * ((Additive.toMul v : H) : Q) * x⁻¹ := by
      exact congrArg Subtype.val (by simpa [A] using heval x v)
    rw [hAeval (A h), hAeval h]
    let hv : Q := ((Additive.toMul h : H) : Q)
    have htriple : ⁅⁅hv, x⁆, x⁆ = 1 := by
      rw [← Subgroup.mem_bot, ← hcomm]
      exact Subgroup.commutator_mem_commutator
        (Subgroup.commutator_mem_commutator
          (show hv ∈ H from (Additive.toMul h).2)
          (Subgroup.mem_zpowers x))
        (Subgroup.mem_zpowers x)
    have hc : Commute ⁅hv, x⁆ x :=
      commutatorElement_eq_one_iff_commute.mp htriple
    have hxc : Commute x ⁅x, hv⁆ := by
      rw [← commutatorElement_inv]
      exact hc.inv_left.symm
    have hdouble : ⁅x, ⁅x, hv⁆⁆ = 1 :=
      commutatorElement_eq_one_iff_commute.mpr hxc
    rw [← hdouble]
    simp only [hv, commutatorElement_def]
    group
  · intro hzero
    apply hx
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    let v : Additive H := Additive.ofMul (⟨h, hh⟩ : H)
    let A : Additive H →ₗ[ZMod p] Additive H :=
      (ρ (QuotientGroup.mk' (Subgroup.centralizer (H : Set Q)) x) :
        Additive H →ₗ[ZMod p] Additive H)
    have hAone : A = 1 := sub_eq_zero.mp hzero
    have hfix : A v = v := by rw [hAone, Module.End.one_apply]
    have hrep := congrArg Subtype.val (heval x v)
    have hrepA : ((Additive.toMul (A v) : H) : Q) = x * h * x⁻¹ := by
      simpa [A, v, MulAut.conjNormal_apply] using hrep
    have hleft : ((Additive.toMul (A v) : H) : Q) = h := by
      rw [hfix]
      rfl
    have hconj : x * h * x⁻¹ = h := hrepA.symm.trans hleft
    calc
      h * x = (x * h * x⁻¹) * x := by rw [hconj]
      _ = x * h := by group

end CFSG.Glauberman

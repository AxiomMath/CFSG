module

public import CFSG.RankThree.CentralCover.SteinbergBNVectorPairing
public import CFSG.RankThree.GroupTheory.SteinbergCECentralOddKernelLift
public import CFSG.Mathlib.LinearAlgebra.BilinForm.Reflection

public noncomputable section

namespace CFSG.RankThree.CentralCover

open CFSG.RankThree.Classical2 CFSG.RankThree.GroupTheory
open scoped IsMulCommutative

attribute [local instance] kernelOmega_isElementaryAbelian

variable {Y H : Type*} [Group Y] [Group H] {π : Y →* H}
  {p : ℕ} [Fact p.Prime] {V : Type*} [AddCommGroup V] [Module (ZMod p) V]

theorem liftComm_mem_kernelOmega (hπ : Function.Surjective π)
    (hker : π.ker ≤ Subgroup.center Y) (e : Multiplicative V →* H) (u v : V) :
    liftComm π hπ (e (.ofAdd u)) (e (.ofAdd v)) ∈ kernelOmega hker p := by
  refine ⟨liftComm_mem_ker hπ (commute_map_ofAdd e u v), ?_⟩
  have hpow : e (.ofAdd u) ^ p = 1 := by
    rw [← map_pow]
    have hu : (Multiplicative.ofAdd u : Multiplicative V) ^ p = 1 := by
      apply Multiplicative.toAdd.injective
      rw [toAdd_pow, toAdd_one]
      rw [← Nat.cast_smul_eq_nsmul (ZMod p), ZMod.natCast_self, zero_smul]
    rw [hu, map_one]
  rw [← liftComm_pow_left hπ hker (commute_map_ofAdd e u v), hpow,
    liftComm_one_left hπ hker]

@[expose] def liftCommBilinear (hπ : Function.Surjective π)
    (hker : π.ker ≤ Subgroup.center Y) (e : Multiplicative V →* H) :
    V →ₗ[ZMod p] V →ₗ[ZMod p] Additive (kernelOmega hker p) := by
  let b : V → V → Additive (kernelOmega hker p) := fun u v =>
    Additive.ofMul ⟨liftComm π hπ (e (.ofAdd u)) (e (.ofAdd v)),
      liftComm_mem_kernelOmega hπ hker e u v⟩
  have hleft : ∀ u u' v, b (u + u') v = b u v + b u' v := by
    intro u u' v
    apply Additive.toMul.injective
    apply Subtype.ext
    exact liftComm_add_left e hπ hker u u' v
  have hright : ∀ u v v', b u (v + v') = b u v + b u v' := by
    intro u v v'
    apply Additive.toMul.injective
    apply Subtype.ext
    exact liftComm_add_right e hπ hker u v v'
  exact AddMonoidHom.toZModLinearMap p (AddMonoidHom.mk'
    (fun u => AddMonoidHom.toZModLinearMap p (AddMonoidHom.mk' (b u) (hright u)))
    (fun u u' => by
      apply LinearMap.ext
      intro v
      exact hleft u u' v))

theorem liftCommBilinear_apply (hπ : Function.Surjective π)
    (hker : π.ker ≤ Subgroup.center Y) (e : Multiplicative V →* H) (u v : V) :
    ((Additive.toMul (liftCommBilinear (p := p) hπ hker e u v) : kernelOmega hker p) : Y) =
      liftComm π hπ (e (.ofAdd u)) (e (.ofAdd v)) := rfl

theorem liftCommBilinear_isAlt (hπ : Function.Surjective π)
    (hker : π.ker ≤ Subgroup.center Y) (e : Multiplicative V →* H) :
    (liftCommBilinear (p := p) hπ hker e).IsAlt := by
  intro v
  apply Additive.toMul.injective
  apply Subtype.ext
  exact liftComm_self hπ (e (.ofAdd v))

theorem liftCommBilinear_eq_of_conj (hπ : Function.Surjective π)
    (hker : π.ker ≤ Subgroup.center Y) (e : Multiplicative V →* H)
    (f : V → V) (g : H) (hg : ∀ v, g * e (.ofAdd v) * g⁻¹ = e (.ofAdd (f v)))
    (u v : V) :
    liftCommBilinear (p := p) hπ hker e (f u) (f v) =
      liftCommBilinear (p := p) hπ hker e u v := by
  apply Additive.toMul.injective
  apply Subtype.ext
  simp only [liftCommBilinear_apply]
  rw [← hg u, ← hg v]
  exact liftComm_conj hπ hker (commute_map_ofAdd e u v) g

theorem liftComm_eq_one_of_preReflection
    (hπ : Function.Surjective π) (hker : π.ker ≤ Subgroup.center Y)
    (e : Multiplicative V →* H) (h2 : (2 : ZMod p) ≠ 0)
    (a : V) (α : V →ₗ[ZMod p] ZMod p) (hα : α a = 2) (g : H)
    (hg : ∀ v, g * e (.ofAdd v) * g⁻¹ = e (.ofAdd (v - α v • a))) :
    ∀ v, liftComm π hπ (e (.ofAdd a)) (e (.ofAdd v)) = 1 := by
  let B := liftCommBilinear (p := p) hπ hker e
  have hinv : ∀ u v, B (u - α u • a) (v - α v • a) = B u v :=
    liftCommBilinear_eq_of_conj hπ hker e (fun v => v - α v • a) g hg
  have hB : B a = 0 := LinearMap.BilinMap.apply_left_eq_zero_of_preReflection
    B (liftCommBilinear_isAlt (p := p) hπ hker e) h2 a α hα hinv
  intro v
  have h := congrArg (fun f : V →ₗ[ZMod p] Additive (kernelOmega hker p) => f v) hB
  exact congrArg (fun b : Additive (kernelOmega hker p) =>
    ((Additive.toMul b : kernelOmega hker p) : Y)) h

theorem liftComm_eq_one_of_preReflection_of_central_lift [FiniteDimensional (ZMod p) V]
    (hπ : Function.Surjective π) (hker : π.ker ≤ Subgroup.center Y)
    (e : Multiplicative V →* H) (h2 : (2 : ZMod p) ≠ 0)
    (hdim : Module.finrank (ZMod p) V ≤ 3) (a : V) (α : V →ₗ[ZMod p] ZMod p)
    (hα : α a = 2) (g : H)
    (hg : ∀ v, g * e (.ofAdd v) * g⁻¹ = e (.ofAdd (v - α v • a)))
    (x : V) (hx : x ≠ 0) (hfix : α x = 0)
    (z : Y) (hz : z ∈ Subgroup.center Y) (hzx : π z = e (.ofAdd x)) :
    ∀ u v : V, liftComm π hπ (e (.ofAdd u)) (e (.ofAdd v)) = 1 := by
  let B := liftCommBilinear (p := p) hπ hker e
  have hinv : ∀ u v, B (u - α u • a) (v - α v • a) = B u v :=
    liftCommBilinear_eq_of_conj hπ hker e (fun v => v - α v • a) g hg
  have hxzero : B x = 0 := by
    apply LinearMap.ext
    intro v
    apply Additive.toMul.injective
    apply Subtype.ext
    change liftComm π hπ (e (.ofAdd x)) (e (.ofAdd v)) = 1
    rw [liftComm_eq hπ hker hzx (Function.surjInv_eq hπ _)]
    exact commutatorElement_eq_one_iff_mul_comm.mpr
      (Subgroup.mem_center_iff.mp hz _).symm
  have hB : B = 0 := LinearMap.BilinMap.eq_zero_of_preReflection_of_fixed_radical
    B (liftCommBilinear_isAlt (p := p) hπ hker e) h2 hdim a α hα hinv x hx hfix hxzero
  intro u v
  have h := congrArg (fun B => B u v) hB
  have h' := congrArg (fun v : Additive (kernelOmega hker p) =>
    ((Additive.toMul v : kernelOmega hker p) : Y)) h
  exact h'

end CFSG.RankThree.CentralCover

end

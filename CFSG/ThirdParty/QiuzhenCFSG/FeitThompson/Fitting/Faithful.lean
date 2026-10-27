module

public import Mathlib.Algebra.Group.Action.Faithful
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Data.Finite.Defs
public import Mathlib.GroupTheory.Solvable
public import Mathlib.SetTheory.Cardinal.Finite

import Mathlib.SetTheory.Cardinal.NatCard
import Mathlib.Tactic.Basic

import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.Fitting.Centralizer
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.Fitting.Core

namespace CFSG
end CFSG
open CFSG

/-!
# Proposition 1.4: faithful action on the Fitting subgroup (coprime case)

If a finite group `A` acts faithfully on a finite solvable group `G` and
`Nat.Coprime (Nat.card A) (Nat.card G)`, then `A` acts faithfully on `fittingSubgroup G`.
-/

-- Construct the induced action of `A` on `fittingSubgroup G`.
public instance CFSG.instMulDistribMulAction_fittingSubgroup (G A : Type*) [Group G] [Group A]
    [MulDistribMulAction A G] :
    MulDistribMulAction A (fittingSubgroup G) where
  smul a x :=
    ⟨a • (x : G), by
      have h_fixed :
          (fittingSubgroup G).comap (MulDistribMulAction.toMulAut A G a).toMonoidHom =
            fittingSubgroup G :=
        fittingSubgroup_characteristic.fixed (MulDistribMulAction.toMulAut A G a)
      have hx' :
          (MulDistribMulAction.toMulAut A G a).toMonoidHom (x : G) ∈ fittingSubgroup G := by
        rw [← Subgroup.mem_comap, h_fixed]
        exact x.property
      simpa [MulDistribMulAction.toMulAut] using hx'⟩
  one_smul x := by
    ext
    change ((1 : A) • (x : G)) = (x : G)
    simp
  mul_smul a b x := by
    ext
    change ((a * b) • (x : G)) = a • (b • (x : G))
    simp [smul_smul]
  smul_mul a x y := by
    ext
    change a • ((x : G) * (y : G)) = (a • (x : G)) * (a • (y : G))
    simp [smul_mul']
  smul_one a := by
    ext
    change a • (1 : G) = (1 : G)
    simp

public theorem CFSG.faithful_on_fitting_of_coprime {G : Type*} [Group G] [Finite G] {A : Type*} [Group A]
    [MulDistribMulAction A G] [FaithfulSMul A G] (hsolv : IsSolvable G) :
    Nat.Coprime (Nat.card A) (Nat.card G) -> FaithfulSMul A (fittingSubgroup G) := by
  intro hcoprime
  classical
  refine (faithfulSMul_iff (G := A) (α := fittingSubgroup G)).2 ?_
  intro a ha

  have hcop_a : Nat.Coprime (orderOf a) (Nat.card G) :=
    Nat.Coprime.of_dvd_left (orderOf_dvd_natCard a) hcoprime

  have haG : ∀ g : G, a • g = g := by
    intro g
    set x : G := g⁻¹ * (a • g) with hx_def

    have hx_centralizer :
        x ∈ Subgroup.centralizer (fittingSubgroup G : Set G) := by
      refine
        (Subgroup.mem_centralizer_iff (g := x) (s := (fittingSubgroup G : Set G))).2 ?_
      intro f hf

      have hf_fix : a • f = f := by
        have := congrArg Subtype.val (ha ⟨f, hf⟩)
        have hcoe :
            ((a • (⟨f, hf⟩ : fittingSubgroup G) : fittingSubgroup G) : G) = a • f := rfl
        exact hcoe.symm.trans this

      have hconj : g * f * g⁻¹ ∈ fittingSubgroup G :=
        Subgroup.Normal.conj_mem (inferInstance : (fittingSubgroup G).Normal) f hf g

      have hconj_fix : a • (g * f * g⁻¹) = g * f * g⁻¹ := by
        have h := congrArg Subtype.val (ha ⟨g * f * g⁻¹, hconj⟩)
        have hcoe :
            ((a • (⟨g * f * g⁻¹, hconj⟩ : fittingSubgroup G) : fittingSubgroup G) : G) =
              a • (g * f * g⁻¹) := rfl
        simpa [hcoe] using h

      have hconj_eq : g * f * g⁻¹ = (a • g) * f * (a • g)⁻¹ := by
        have :
            (a • g) * f * (a • g)⁻¹ = g * f * g⁻¹ := by
          simpa [smul_mul', smul_inv', hf_fix, mul_assoc] using hconj_fix
        simpa using this.symm

      have h1 : g * f * g⁻¹ * (a • g) = (a • g) * f := by
        calc
          g * f * g⁻¹ * (a • g)
              = ((a • g) * f * (a • g)⁻¹) * (a • g) := by
                  simpa [mul_assoc] using congrArg (fun t => t * (a • g)) hconj_eq
          _ = (a • g) * f := by
              simp [mul_assoc]

      have h2 : f * g⁻¹ * (a • g) = g⁻¹ * (a • g) * f := by
        have := congrArg (fun t : G => g⁻¹ * t) h1
        simpa [mul_assoc] using this

      simpa [hx_def, mul_assoc] using h2

    have hx_mem_F : x ∈ fittingSubgroup G :=
      (centralizer_fittingSubgroup_le_fittingSubgroup_of_solvable (G := G) hsolv) hx_centralizer

    have hx_fix : a • x = x := by
      have := congrArg Subtype.val (ha ⟨x, hx_mem_F⟩)
      have hcoe :
          ((a • (⟨x, hx_mem_F⟩ : fittingSubgroup G) : fittingSubgroup G) : G) = a • x := rfl
      exact hcoe.symm.trans this

    have hx_fix_pow : ∀ n : ℕ, (a ^ n) • x = x := by
      intro n
      induction n with
      | zero =>
          simp
      | succ n ih =>
          simp [pow_succ, mul_smul, hx_fix, ih]

    have ha_g : a • g = g * x := by
      simp [hx_def]

    have hpow : ∀ n : ℕ, (a ^ n) • g = g * x ^ n := by
      intro n
      induction n with
      | zero =>
          simp
      | succ n ih =>
          calc
            (a ^ (n + 1)) • g
                = (a ^ n) • (a • g) := by
                    simp [pow_succ, mul_smul]
            _ = (a ^ n) • (g * x) := by simp [ha_g]
            _ = ((a ^ n) • g) * ((a ^ n) • x) := by
                    simp [smul_mul']
            _ = (g * x ^ n) * x := by
                    simp [ih, hx_fix_pow n]
            _ = g * x ^ (n + 1) := by
                    simp [pow_succ, mul_assoc]

    have hx_pow_order : x ^ orderOf a = 1 := by
      have ha_pow : a ^ orderOf a = (1 : A) := pow_orderOf_eq_one a
      have : g = g * x ^ orderOf a := by
        calc
          g = (1 : A) • g := by simp
          _ = (a ^ orderOf a) • g := by simp [ha_pow]
          _ = g * x ^ orderOf a := hpow (orderOf a)
      have := congrArg (fun t : G => g⁻¹ * t) this
      simpa [mul_assoc] using this.symm

    have h_order_dvd : orderOf x ∣ orderOf a :=
      (orderOf_dvd_iff_pow_eq_one).2 hx_pow_order

    have h_order_one : orderOf x = 1 :=
      Nat.eq_one_of_dvd_coprimes hcop_a h_order_dvd (orderOf_dvd_natCard x)

    have hx_one : x = 1 :=
      (orderOf_eq_one_iff).1 h_order_one

    have : a • g = g * x := by
      simp [hx_def]
    simpa [hx_one] using this

  have hfaithG :
      ∀ a : A, (∀ g : G, a • g = g) → a = 1 :=
    (faithfulSMul_iff (G := A) (α := G)).1 (inferInstance : FaithfulSMul A G)

  exact hfaithG a haG

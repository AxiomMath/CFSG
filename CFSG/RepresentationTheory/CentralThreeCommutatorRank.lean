module

public import CFSG.LinearAlgebra.FixedPointFreeOrderThreeField
public import Mathlib.LinearAlgebra.Determinant
public import Mathlib.Data.Rat.Floor
public import Mathlib.RingTheory.LocalRing.Basic

public section

namespace CFSG.RepresentationTheory

open CFSG.LinearAlgebra
open scoped commutatorElement

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

theorem zmod_two_add_self (x : V) : x + x = 0 := by
  rw [← two_smul (ZMod 2), show (2 : ZMod 2) = 0 from rfl, zero_smul]

theorem omega_pow_three : LinearAlgebra.omega ^ 3 = 1 := by
  have h2 : LinearAlgebra.omega + LinearAlgebra.omega = 0 := by rw [← two_mul, omegaField_two_eq_zero, zero_mul]
  calc LinearAlgebra.omega ^ 3 = LinearAlgebra.omega * LinearAlgebra.omega ^ 2 := by ring
    _ = LinearAlgebra.omega * (LinearAlgebra.omega + 1) := by rw [omega_sq]
    _ = LinearAlgebra.omega ^ 2 + LinearAlgebra.omega := by ring
    _ = (LinearAlgebra.omega + LinearAlgebra.omega) + 1 := by rw [omega_sq]; ring
    _ = 1 := by rw [h2, zero_add]

theorem omega_ne_one : LinearAlgebra.omega ≠ 1 := by
  intro h
  have hsq := omega_sq
  rw [h, one_pow, one_add_one_eq_two, omegaField_two_eq_zero] at hsq
  exact one_ne_zero hsq

theorem orderOf_omega : orderOf LinearAlgebra.omega = 3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  exact orderOf_eq_prime omega_pow_three omega_ne_one

@[expose] def submoduleStabGL (W : Submodule (ZMod 2) V) :
    Subgroup (LinearMap.GeneralLinearGroup (ZMod 2) V) where
  carrier := {f | ∀ w ∈ W, (f : V →ₗ[ZMod 2] V) w ∈ W ∧
    ((f⁻¹ : LinearMap.GeneralLinearGroup (ZMod 2) V) : V →ₗ[ZMod 2] V) w ∈ W}
  mul_mem' {f g} hf hg w hw := by
    refine ⟨(hf _ (hg w hw).1).1, ?_⟩
    rw [mul_inv_rev]
    exact (hg _ (hf w hw).2).2
  one_mem' w hw := ⟨hw, hw⟩
  inv_mem' {f} hf w hw := by
    rw [inv_inv]
    exact ⟨(hf w hw).2, (hf w hw).1⟩

@[expose] def submoduleStabRestrict (W : Submodule (ZMod 2) V) :
    submoduleStabGL W →* LinearMap.GeneralLinearGroup (ZMod 2) W where
  toFun f :=
    { val := (f.1 : V →ₗ[ZMod 2] V).restrict fun w hw => (f.2 w hw).1
      inv := ((f.1⁻¹ : LinearMap.GeneralLinearGroup (ZMod 2) V) : V →ₗ[ZMod 2] V).restrict
        fun w hw => (f.2 w hw).2
      val_inv := LinearMap.ext fun w => Subtype.ext (by
        change (f.1 : V →ₗ[ZMod 2] V)
          (((f.1⁻¹ : LinearMap.GeneralLinearGroup (ZMod 2) V) : V →ₗ[ZMod 2] V) w) = w
        rw [← Module.End.mul_apply, ← Units.val_mul, mul_inv_cancel, Units.val_one,
          Module.End.one_apply])
      inv_val := LinearMap.ext fun w => Subtype.ext (by
        change ((f.1⁻¹ : LinearMap.GeneralLinearGroup (ZMod 2) V) : V →ₗ[ZMod 2] V)
          ((f.1 : V →ₗ[ZMod 2] V) w) = w
        rw [← Module.End.mul_apply, ← Units.val_mul, inv_mul_cancel, Units.val_one,
          Module.End.one_apply]) }
  map_one' := Units.ext (LinearMap.ext fun _ => rfl)
  map_mul' _ _ := Units.ext (LinearMap.ext fun _ => rfl)

theorem three_dvd_finrank_of_commutator_eq_omega {W : Type*} [AddCommGroup W]
    [Module (ZMod 2) W] [Module OmegaField W] [IsScalarTower (ZMod 2) OmegaField W]
    (a b z : LinearMap.GeneralLinearGroup (ZMod 2) W) (hz : z = a * b * a⁻¹ * b⁻¹)
    (hza : a * z = z * a) (hzb : b * z = z * b)
    (hω : ∀ w, LinearAlgebra.omega • w = (z : W →ₗ[ZMod 2] W) w) :
    3 ∣ Module.finrank OmegaField W := by
  have hF : ∀ g : LinearMap.GeneralLinearGroup (ZMod 2) W, g * z = z * g →
      ∃ gF : W →ₗ[OmegaField] W, ∀ w, gF w = (g : W →ₗ[ZMod 2] W) w := by
    intro g hg
    have hl := (commute_iff_omega_linear hω g).1 hg
    exact ⟨{ toFun := g, map_add' := map_add _, map_smul' := hl }, fun _ => rfl⟩
  have hinvc : ∀ g : LinearMap.GeneralLinearGroup (ZMod 2) W, g * z = z * g → g⁻¹ * z = z * g⁻¹ :=
    fun g hg => ((Commute.inv_left (hg : Commute g z)) : Commute g⁻¹ z).eq
  obtain ⟨aF, haF⟩ := hF a hza
  obtain ⟨bF, hbF⟩ := hF b hzb
  obtain ⟨aiF, haiF⟩ := hF a⁻¹ (hinvc a hza)
  obtain ⟨biF, hbiF⟩ := hF b⁻¹ (hinvc b hzb)
  have hval : ∀ (g : LinearMap.GeneralLinearGroup (ZMod 2) W) (w : W),
      (g : W →ₗ[ZMod 2] W) (((g⁻¹ : LinearMap.GeneralLinearGroup (ZMod 2) W) :
        W →ₗ[ZMod 2] W) w) = w := fun g w => by
    rw [← Module.End.mul_apply, ← Units.val_mul, mul_inv_cancel, Units.val_one,
      Module.End.one_apply]
  have ha1 : aF * aiF = 1 := LinearMap.ext fun w => by
    rw [Module.End.mul_apply, haiF, haF, hval, Module.End.one_apply]
  have hb1 : bF * biF = 1 := LinearMap.ext fun w => by
    rw [Module.End.mul_apply, hbiF, hbF, hval, Module.End.one_apply]
  have hcomm : aF * bF * aiF * biF = LinearAlgebra.omega • (1 : W →ₗ[OmegaField] W) := LinearMap.ext fun w => by
    rw [LinearMap.smul_apply, Module.End.one_apply, hω, hz]
    simp only [Module.End.mul_apply, haF, hbF, haiF, hbiF, Units.val_mul]
  have hdet : LinearAlgebra.omega ^ Module.finrank OmegaField W = 1 := by
    have h := congrArg LinearMap.det hcomm
    rw [LinearMap.det_smul, map_one, mul_one] at h
    have ha := congrArg LinearMap.det ha1
    have hb := congrArg LinearMap.det hb1
    rw [map_mul, map_one] at ha hb
    rw [← h, map_mul, map_mul, map_mul]
    linear_combination (LinearMap.det bF * LinearMap.det biF) * ha + hb
  rw [← orderOf_omega]
  exact orderOf_dvd_of_pow_eq_one hdet

theorem six_dvd_rank_central_three_commutator [FiniteDimensional (ZMod 2) V]
    (a b z : LinearMap.GeneralLinearGroup (ZMod 2) V) (hz : z = a * b * a⁻¹ * b⁻¹)
    (hz3 : z ^ 3 = 1) (hza : z * a = a * z) (hzb : z * b = b * z) :
    6 ∣ Module.finrank (ZMod 2) (LinearMap.range ((z : Module.End (ZMod 2) V) - 1)) := by
  classical
  set W := LinearMap.range ((z : Module.End (ZMod 2) V) - 1) with hW
  by_cases hW0 : W = ⊥
  · rw [hW0, finrank_bot]
    exact dvd_zero 6
  have hpres : ∀ f : LinearMap.GeneralLinearGroup (ZMod 2) V, f * z = z * f →
      ∀ w ∈ W, (f : V →ₗ[ZMod 2] V) w ∈ W := by
    intro f hf w hw
    obtain ⟨v, rfl⟩ := hw
    refine ⟨(f : V →ₗ[ZMod 2] V) v, ?_⟩
    have hfz : (f : V →ₗ[ZMod 2] V) ((z : V →ₗ[ZMod 2] V) v) =
        (z : V →ₗ[ZMod 2] V) ((f : V →ₗ[ZMod 2] V) v) := by
      have := congrArg (fun g : LinearMap.GeneralLinearGroup (ZMod 2) V =>
        (g : V →ₗ[ZMod 2] V) v) hf
      exact this
    simp only [LinearMap.sub_apply, Module.End.one_apply, map_sub, hfz]
  have hmem : ∀ f : LinearMap.GeneralLinearGroup (ZMod 2) V, f * z = z * f →
      f ∈ submoduleStabGL W := by
    intro f hf w hw
    exact ⟨hpres f hf w hw,
      hpres f⁻¹ ((Commute.inv_left (hf : Commute f z)) : Commute f⁻¹ z).eq w hw⟩
  let aS : submoduleStabGL W := ⟨a, hmem a hza.symm⟩
  let bS : submoduleStabGL W := ⟨b, hmem b hzb.symm⟩
  let zS : submoduleStabGL W := ⟨z, hmem z rfl⟩
  have hzS : zS = aS * bS * aS⁻¹ * bS⁻¹ := Subtype.ext hz
  let ρ := submoduleStabRestrict W
  have hzW : ρ zS = ρ aS * ρ bS * (ρ aS)⁻¹ * (ρ bS)⁻¹ := by
    rw [hzS, map_mul, map_mul, map_mul, map_inv, map_inv]
  have hzaW : ρ aS * ρ zS = ρ zS * ρ aS := by
    rw [← map_mul, ← map_mul]
    exact congrArg ρ (Subtype.ext hza.symm)
  have hzbW : ρ bS * ρ zS = ρ zS * ρ bS := by
    rw [← map_mul, ← map_mul]
    exact congrArg ρ (Subtype.ext hzb.symm)
  have hz3v : ∀ v, (z : V →ₗ[ZMod 2] V) ((z : V →ₗ[ZMod 2] V) ((z : V →ₗ[ZMod 2] V) v)) = v := by
    intro v
    have := congrArg (fun g : LinearMap.GeneralLinearGroup (ZMod 2) V =>
      (g : V →ₗ[ZMod 2] V) v) hz3
    simpa only [Units.val_pow_eq_pow_val, pow_succ, pow_zero, one_mul, Module.End.mul_apply,
      Units.val_one, Module.End.one_apply, Units.val_mul] using this
  have hfixW : ∀ w : W, ((ρ zS : LinearMap.GeneralLinearGroup (ZMod 2) W) : W →ₗ[ZMod 2] W) w = w →
      w = 0 := by
    rintro ⟨_, v, rfl⟩ hw
    apply Subtype.ext
    have hw' := congrArg Subtype.val hw
    change (z : V →ₗ[ZMod 2] V) (((z : Module.End (ZMod 2) V) - 1) v) =
      ((z : Module.End (ZMod 2) V) - 1) v at hw'
    simp only [LinearMap.sub_apply, Module.End.one_apply, map_sub] at hw'
    have hzz : (z : V →ₗ[ZMod 2] V) ((z : V →ₗ[ZMod 2] V) v) = v := by
      have e1 : (z : V →ₗ[ZMod 2] V) ((z : V →ₗ[ZMod 2] V) v) =
          ((z : V →ₗ[ZMod 2] V) v - v) + (z : V →ₗ[ZMod 2] V) v := by
        rw [← hw']
        abel
      rw [e1, sub_add_eq_add_sub, zmod_two_add_self, zero_sub]
      exact neg_eq_of_add_eq_zero_left (zmod_two_add_self v)
    have hzv : (z : V →ₗ[ZMod 2] V) v = v := by
      have := hz3v v
      rwa [hzz] at this
    change ((z : Module.End (ZMod 2) V) - 1) v = 0
    rw [LinearMap.sub_apply, Module.End.one_apply, hzv, sub_self]
  have hzW3 : ρ zS ^ 3 = 1 := by
    rw [← map_pow]
    have : zS ^ 3 = 1 := Subtype.ext hz3
    rw [this, map_one]
  have hzW1 : ρ zS ≠ 1 := by
    intro h1
    apply hW0
    rw [eq_bot_iff]
    intro w hw
    have := hfixW ⟨w, hw⟩ (by rw [h1]; rfl)
    rw [Submodule.mem_bot]
    exact congrArg Subtype.val this
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hord : orderOf (ρ zS) = 3 := orderOf_eq_prime hzW3 hzW1
  have hstr := @omega_semilinear_structure W _ _ (omegaModule (ρ zS) hord hfixW)
    (omegaModule_isScalarTower (ρ zS) hord hfixW) _ (ρ zS) hord
    (omegaModule_omega_smul (ρ zS) hord hfixW)
  have h3 := @three_dvd_finrank_of_commutator_eq_omega W _ _ (omegaModule (ρ zS) hord hfixW)
    (omegaModule_isScalarTower (ρ zS) hord hfixW) (ρ aS) (ρ bS) (ρ zS) hzW hzaW hzbW
    (omegaModule_omega_smul (ρ zS) hord hfixW)
  rw [hstr.1]
  exact mul_dvd_mul_left 2 h3

end CFSG.RepresentationTheory

module

public import Mathlib.LinearAlgebra.Matrix.BilinearForm
public import Mathlib.Algebra.Module.ZMod

public section

namespace CFSG.Sporadic.Co1.Cover

open Matrix

structure CentralExt (n : ℕ) (T : Type*) [Group T] where
  ψ : T →* Multiplicative (Fin n → ZMod 2)
  surj : Function.Surjective ψ
  z : T
  central : ∀ t : T, z * t = t * z
  sq : z * z = 1
  ne_one : z ≠ 1
  ker_eq : ψ.ker = Subgroup.zpowers z

namespace CentralExt

variable {n : ℕ} {T : Type*} [Group T] (E : CentralExt n T)

@[expose] def zz (k : ZMod 2) : T := E.z ^ k.val

theorem zz_zero : E.zz 0 = 1 := by simp [zz]

theorem zz_one : E.zz 1 = E.z := by simp [zz, ZMod.val_one]

theorem zz_central (k : ZMod 2) (t : T) : E.zz k * t = t * E.zz k := by
  have hz := E.central t
  unfold zz
  generalize k.val = m
  induction m with
  | zero => simp
  | succ m ih => rw [pow_succ, mul_assoc, hz, ← mul_assoc, ih, mul_assoc]

theorem zmod_two_cases (k : ZMod 2) : k = 0 ∨ k = 1 := by
  revert k
  decide

theorem zz_add (k l : ZMod 2) : E.zz (k + l) = E.zz k * E.zz l := by
  rcases zmod_two_cases k with rfl | rfl <;> rcases zmod_two_cases l with rfl | rfl
  · simp [zz_zero]
  · simp [zz_zero]
  · simp [zz_zero]
  · have : (1 : ZMod 2) + 1 = 0 := by decide
    rw [this, zz_zero, zz_one, E.sq]

theorem zz_mul_self (k : ZMod 2) : E.zz k * E.zz k = 1 := by
  rw [← zz_add]
  have : k + k = 0 := by
    rcases zmod_two_cases k with rfl | rfl <;> decide
  rw [this, zz_zero]

theorem zz_injective : Function.Injective E.zz := by
  intro k l h
  rcases zmod_two_cases k with rfl | rfl <;> rcases zmod_two_cases l with rfl | rfl
  · rfl
  · rw [zz_zero, zz_one] at h
    exact absurd h.symm E.ne_one
  · rw [zz_zero, zz_one] at h
    exact absurd h E.ne_one
  · rfl

theorem zpow_z (m : ℤ) : E.z ^ m = E.zz (m : ZMod 2) := by
  have h2 : E.z ^ (2 : ℤ) = 1 := by rw [zpow_two, E.sq]
  rcases Int.even_or_odd' m with ⟨q, rfl | rfl⟩
  · have : ((2 * q : ℤ) : ZMod 2) = 0 := by
      push_cast
      have : (2 : ZMod 2) = 0 := by decide
      rw [this, zero_mul]
    rw [this, zz_zero, zpow_mul, h2, one_zpow]
  · have : ((2 * q + 1 : ℤ) : ZMod 2) = 1 := by
      push_cast
      have : (2 : ZMod 2) = 0 := by decide
      rw [this, zero_mul, zero_add]
    rw [this, zz_one, zpow_add, zpow_mul, h2, one_zpow, one_mul, zpow_one]

theorem mem_ker_iff {y : T} : y ∈ E.ψ.ker ↔ ∃ k : ZMod 2, y = E.zz k := by
  rw [E.ker_eq, Subgroup.mem_zpowers_iff]
  constructor
  · rintro ⟨m, rfl⟩
    exact ⟨(m : ZMod 2), E.zpow_z m⟩
  · rintro ⟨k, rfl⟩
    refine ⟨(k.val : ℤ), ?_⟩
    rw [zpow_z, Int.cast_natCast, ZMod.natCast_zmod_val]

theorem zz_mem_ker (k : ZMod 2) : E.zz k ∈ E.ψ.ker := E.mem_ker_iff.2 ⟨k, rfl⟩

theorem exists_unique_zz {x y : T} (h : E.ψ x = E.ψ y) : ∃! k : ZMod 2, x = y * E.zz k := by
  have hmem : y⁻¹ * x ∈ E.ψ.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, h, inv_mul_cancel]
  obtain ⟨k, hk⟩ := E.mem_ker_iff.1 hmem
  refine ⟨k, ?_, fun l hl => ?_⟩
  · show x = y * E.zz k
    rw [← hk]; group
  · apply E.zz_injective
    have : y * E.zz l = y * E.zz k := by rw [← hl, ← hk]; group
    exact mul_left_cancel this

theorem mul_zz_comm (k : ZMod 2) (t : T) : t * E.zz k = E.zz k * t := (E.zz_central k t).symm

theorem mul_zz_mul (k : ZMod 2) (x y : T) : x * E.zz k * y = x * y * E.zz k := by
  rw [mul_assoc, E.zz_central k y, ← mul_assoc]

theorem psi_mul_comm (t u : T) : E.ψ (t * u) = E.ψ (u * t) := by
  rw [map_mul, map_mul]
  exact mul_comm _ _

noncomputable def kappa (t u : T) : ZMod 2 :=
  (E.exists_unique_zz (E.psi_mul_comm t u)).exists.choose

theorem mul_eq_kappa (t u : T) : t * u = u * t * E.zz (E.kappa t u) :=
  (E.exists_unique_zz (E.psi_mul_comm t u)).exists.choose_spec

theorem kappa_unique {t u : T} {k : ZMod 2} (h : t * u = u * t * E.zz k) : E.kappa t u = k :=
  (E.exists_unique_zz (E.psi_mul_comm t u)).unique (E.mul_eq_kappa t u) h

theorem kappa_mul_left (t t' u : T) : E.kappa (t * t') u = E.kappa t u + E.kappa t' u := by
  apply E.kappa_unique
  have h1 := E.mul_eq_kappa t u
  have h2 := E.mul_eq_kappa t' u
  calc t * t' * u = t * (t' * u) := mul_assoc _ _ _
    _ = t * (u * t' * E.zz (E.kappa t' u)) := by rw [h2]
    _ = t * u * t' * E.zz (E.kappa t' u) := by simp only [mul_assoc]
    _ = u * t * E.zz (E.kappa t u) * t' * E.zz (E.kappa t' u) := by rw [h1]
    _ = u * t * t' * E.zz (E.kappa t u) * E.zz (E.kappa t' u) := by rw [E.mul_zz_mul]
    _ = u * (t * t') * E.zz (E.kappa t u + E.kappa t' u) := by rw [E.zz_add]; simp only [mul_assoc]

theorem kappa_mul_right (t u u' : T) : E.kappa t (u * u') = E.kappa t u + E.kappa t u' := by
  apply E.kappa_unique
  have h1 := E.mul_eq_kappa t u
  have h2 := E.mul_eq_kappa t u'
  calc t * (u * u') = t * u * u' := (mul_assoc _ _ _).symm
    _ = u * t * E.zz (E.kappa t u) * u' := by rw [h1]
    _ = u * t * u' * E.zz (E.kappa t u) := by rw [E.mul_zz_mul]
    _ = u * (t * u') * E.zz (E.kappa t u) := by simp only [mul_assoc]
    _ = u * (u' * t * E.zz (E.kappa t u')) * E.zz (E.kappa t u) := by rw [h2]
    _ = u * u' * t * (E.zz (E.kappa t u') * E.zz (E.kappa t u)) := by simp only [mul_assoc]
    _ = u * u' * t * E.zz (E.kappa t u + E.kappa t u') := by
        rw [E.zz_add, ← E.zz_central (E.kappa t u') (E.zz (E.kappa t u))]

theorem kappa_zz_left (t u : T) (k : ZMod 2) : E.kappa (t * E.zz k) u = E.kappa t u := by
  apply E.kappa_unique
  have h1 := E.mul_eq_kappa t u
  calc t * E.zz k * u = t * u * E.zz k := E.mul_zz_mul k t u
    _ = u * t * E.zz (E.kappa t u) * E.zz k := by rw [h1]
    _ = u * t * (E.zz (E.kappa t u) * E.zz k) := by rw [mul_assoc]
    _ = u * t * (E.zz k * E.zz (E.kappa t u)) := by rw [E.zz_central (E.kappa t u) (E.zz k)]
    _ = u * (t * E.zz k) * E.zz (E.kappa t u) := by simp only [mul_assoc]

theorem kappa_zz_right (t u : T) (k : ZMod 2) : E.kappa t (u * E.zz k) = E.kappa t u := by
  apply E.kappa_unique
  have h1 := E.mul_eq_kappa t u
  calc t * (u * E.zz k) = t * u * E.zz k := (mul_assoc _ _ _).symm
    _ = u * t * E.zz (E.kappa t u) * E.zz k := by rw [h1]
    _ = u * t * (E.zz (E.kappa t u) * E.zz k) := by rw [mul_assoc]
    _ = u * t * (E.zz k * E.zz (E.kappa t u)) := by rw [E.zz_central (E.kappa t u) (E.zz k)]
    _ = u * t * E.zz k * E.zz (E.kappa t u) := (mul_assoc _ _ _).symm
    _ = u * E.zz k * t * E.zz (E.kappa t u) := by rw [E.mul_zz_mul k u t]

theorem kappa_self (t : T) : E.kappa t t = 0 := by
  apply E.kappa_unique
  rw [E.zz_zero, mul_one]

noncomputable def lift (v : Fin n → ZMod 2) : T := Function.surjInv E.surj (Multiplicative.ofAdd v)

theorem psi_lift (v : Fin n → ZMod 2) : E.ψ (E.lift v) = Multiplicative.ofAdd v :=
  Function.surjInv_eq E.surj _

theorem exists_zz_lift (t : T) : ∃ k, t = E.lift (Multiplicative.toAdd (E.ψ t)) * E.zz k :=
  (E.exists_unique_zz (by rw [psi_lift]; rfl)).exists

theorem exists_zz_lift_add (v w : Fin n → ZMod 2) :
    ∃ k, E.lift (v + w) = E.lift v * E.lift w * E.zz k := by
  refine (E.exists_unique_zz ?_).exists
  rw [map_mul, psi_lift, psi_lift, psi_lift]
  rfl

noncomputable def Cf (v w : Fin n → ZMod 2) : ZMod 2 := E.kappa (E.lift v) (E.lift w)

theorem kappa_eq_Cf (t u : T) :
    E.kappa t u = E.Cf (Multiplicative.toAdd (E.ψ t)) (Multiplicative.toAdd (E.ψ u)) := by
  obtain ⟨k, hk⟩ := E.exists_zz_lift t
  obtain ⟨l, hl⟩ := E.exists_zz_lift u
  unfold Cf
  conv_lhs => rw [hk, hl]
  rw [E.kappa_zz_left, E.kappa_zz_right]

theorem Cf_add_left (v v' w : Fin n → ZMod 2) : E.Cf (v + v') w = E.Cf v w + E.Cf v' w := by
  obtain ⟨k, hk⟩ := E.exists_zz_lift_add v v'
  rw [Cf, Cf, Cf, hk, E.kappa_zz_left, E.kappa_mul_left]

theorem Cf_add_right (v w w' : Fin n → ZMod 2) : E.Cf v (w + w') = E.Cf v w + E.Cf v w' := by
  obtain ⟨k, hk⟩ := E.exists_zz_lift_add w w'
  rw [Cf, Cf, Cf, hk, E.kappa_zz_right, E.kappa_mul_right]

theorem Cf_self (v : Fin n → ZMod 2) : E.Cf v v = 0 := E.kappa_self _

theorem zmod_two_eq_of_add_eq_zero {a b : ZMod 2} (h : a + b = 0) : a = b := by
  revert a b
  decide

theorem Cf_comm (v w : Fin n → ZMod 2) : E.Cf v w = E.Cf w v := by
  have h := E.Cf_self (v + w)
  rw [E.Cf_add_left, E.Cf_add_right, E.Cf_add_right, E.Cf_self, E.Cf_self, zero_add, add_zero] at h
  exact zmod_two_eq_of_add_eq_zero h

structure Act (E : CentralExt n T) (A : Matrix (Fin n) (Fin n) (ZMod 2)) where
  γ : T →* T
  fix_z : γ E.z = E.z
  act : ∀ t, E.ψ (γ t) = Multiplicative.ofAdd (A *ᵥ Multiplicative.toAdd (E.ψ t))

theorem Act.fix_zz {E : CentralExt n T} {A : Matrix (Fin n) (Fin n) (ZMod 2)} (a : E.Act A)
    (k : ZMod 2) :
    a.γ (E.zz k) = E.zz k := by
  rw [zz, map_pow, a.fix_z]

theorem Act.kappa {E : CentralExt n T} {A : Matrix (Fin n) (Fin n) (ZMod 2)} (a : E.Act A)
    (t u : T) :
    E.kappa (a.γ t) (a.γ u) = E.kappa t u := by
  apply E.kappa_unique
  have h := congrArg a.γ (E.mul_eq_kappa t u)
  rw [map_mul, map_mul, map_mul, a.fix_zz] at h
  exact h

theorem Act.Cf {E : CentralExt n T} {A : Matrix (Fin n) (Fin n) (ZMod 2)} (a : E.Act A)
    (v w : Fin n → ZMod 2) :
    E.Cf (A *ᵥ v) (A *ᵥ w) = E.Cf v w := by
  have h := a.kappa (E.lift v) (E.lift w)
  rw [E.kappa_eq_Cf, E.kappa_eq_Cf, a.act, a.act, E.psi_lift, E.psi_lift] at h
  simpa using h

theorem Cf_zero_left (w : Fin n → ZMod 2) : E.Cf 0 w = 0 := by
  have h := E.Cf_add_left 0 0 w
  rw [add_zero] at h
  revert h
  generalize E.Cf 0 w = x
  revert x
  decide

theorem Cf_zero_right (v : Fin n → ZMod 2) : E.Cf v 0 = 0 := by
  rw [E.Cf_comm, E.Cf_zero_left]

@[expose] noncomputable def CfForm : LinearMap.BilinForm (ZMod 2) (Fin n → ZMod 2) :=
  LinearMap.mk₂ (ZMod 2) E.Cf E.Cf_add_left
    (fun c v w => by
      rcases zmod_two_cases c with rfl | rfl
      · simp [E.Cf_zero_left]
      · simp)
    E.Cf_add_right
    (fun c v w => by
      rcases zmod_two_cases c with rfl | rfl
      · simp [E.Cf_zero_right]
      · simp)

theorem CfForm_apply (v w : Fin n → ZMod 2) : E.CfForm v w = E.Cf v w := rfl

theorem comm_of_forms {A B : Matrix (Fin n) (Fin n) (ZMod 2)} (a : E.Act A) (b : E.Act B)
    (hC : ∀ c : Matrix (Fin n) (Fin n) (ZMod 2), cᵀ = c → (∀ i, c i i = 0) →
      Aᵀ * c * A = c → Bᵀ * c * B = c → c = 0) (t u : T) : t * u = u * t := by
  set c : Matrix (Fin n) (Fin n) (ZMod 2) := LinearMap.BilinForm.toMatrix' E.CfForm with hc
  have hform : Matrix.toBilin' c = E.CfForm := Matrix.toBilin'_toMatrix' _
  have hcij : ∀ i j, c i j = E.Cf (Pi.single i 1) (Pi.single j 1) := fun i j => by
    rw [hc, LinearMap.BilinForm.toMatrix'_apply]; rfl
  have hinv : ∀ (M : Matrix (Fin n) (Fin n) (ZMod 2)) (x : E.Act M), Mᵀ * c * M = c := by
    intro M x
    have h1 : (Matrix.toBilin' c).comp M.toLin' M.toLin' = Matrix.toBilin' c := by
      refine LinearMap.ext₂ fun v w => ?_
      rw [LinearMap.BilinForm.comp_apply, Matrix.toLin'_apply, Matrix.toLin'_apply, hform]
      exact x.Cf v w
    apply Matrix.toBilin'.injective
    rw [← Matrix.toBilin'_comp, h1]
  have hc0 : c = 0 := hC c (by
      ext i j
      rw [Matrix.transpose_apply, hcij, hcij, E.Cf_comm])
    (fun i => by rw [hcij, E.Cf_self]) (hinv A a) (hinv B b)
  have hCf : ∀ v w, E.Cf v w = 0 := fun v w => by
    have := Matrix.toBilin'_apply' c v w
    rw [hform, hc0] at this
    rw [← E.CfForm_apply]
    simpa using this
  have hk : E.kappa t u = 0 := by rw [E.kappa_eq_Cf, hCf]
  have := E.mul_eq_kappa t u
  rwa [hk, zz_zero, mul_one] at this

theorem mul_self_multiplicative (x : Multiplicative (Fin n → ZMod 2)) : x * x = 1 := by
  rw [← ofAdd_toAdd x, ← ofAdd_add, ← ofAdd_zero]
  congr 1
  funext i
  simp [CharTwo.add_self_eq_zero]

theorem psi_mul_self (t : T) : E.ψ (t * t) = E.ψ 1 := by
  rw [map_mul, map_one, mul_self_multiplicative]

noncomputable def sqk (t : T) : ZMod 2 := (E.exists_unique_zz (E.psi_mul_self t)).exists.choose

theorem mul_self_eq_sqk (t : T) : t * t = E.zz (E.sqk t) := by
  have := (E.exists_unique_zz (E.psi_mul_self t)).exists.choose_spec
  rwa [one_mul] at this

theorem sqk_unique {t : T} {k : ZMod 2} (h : t * t = E.zz k) : E.sqk t = k := by
  refine (E.exists_unique_zz (E.psi_mul_self t)).unique ?_ ?_
  · exact (by have := E.mul_self_eq_sqk t; rwa [← one_mul (E.zz _)] at this)
  · rwa [one_mul]

theorem sqk_zz (t : T) (k : ZMod 2) : E.sqk (t * E.zz k) = E.sqk t := by
  apply E.sqk_unique
  calc t * E.zz k * (t * E.zz k) = t * t * (E.zz k * E.zz k) := by
        rw [mul_assoc, ← mul_assoc (E.zz k), E.zz_central k t, mul_assoc, mul_assoc, ← mul_assoc]
    _ = E.zz (E.sqk t) := by rw [E.zz_mul_self, mul_one, E.mul_self_eq_sqk]

@[expose] noncomputable def Qf (v : Fin n → ZMod 2) : ZMod 2 := E.sqk (E.lift v)

theorem sqk_eq_Qf (t : T) : E.sqk t = E.Qf (Multiplicative.toAdd (E.ψ t)) := by
  obtain ⟨k, hk⟩ := E.exists_zz_lift t
  conv_lhs => rw [hk]
  rw [E.sqk_zz]
  rfl

theorem Act.Qf {E : CentralExt n T} {A : Matrix (Fin n) (Fin n) (ZMod 2)} (a : E.Act A)
    (v : Fin n → ZMod 2) :
    E.Qf (A *ᵥ v) = E.Qf v := by
  have h1 : E.sqk (a.γ (E.lift v)) = E.sqk (E.lift v) := by
    apply E.sqk_unique
    rw [← map_mul, E.mul_self_eq_sqk, a.fix_zz]
  rw [E.sqk_eq_Qf, a.act, E.psi_lift] at h1
  exact h1

section Abelian

variable (hcomm : ∀ t u : T, t * u = u * t)
include hcomm

theorem sqk_mul (t t' : T) : E.sqk (t * t') = E.sqk t + E.sqk t' := by
  apply E.sqk_unique
  calc t * t' * (t * t') = t * (t' * t) * t' := by simp only [mul_assoc]
    _ = t * (t * t') * t' := by rw [hcomm t' t]
    _ = (t * t) * (t' * t') := by simp only [mul_assoc]
    _ = E.zz (E.sqk t) * E.zz (E.sqk t') := by rw [E.mul_self_eq_sqk t, E.mul_self_eq_sqk t']
    _ = E.zz (E.sqk t + E.sqk t') := (E.zz_add _ _).symm

theorem Qf_add (v w : Fin n → ZMod 2) : E.Qf (v + w) = E.Qf v + E.Qf w := by
  obtain ⟨k, hk⟩ := E.exists_zz_lift_add v w
  unfold Qf
  rw [hk, E.sqk_zz, E.sqk_mul hcomm]

theorem Qf_zero : E.Qf 0 = 0 := by
  have h := E.Qf_add hcomm 0 0
  rw [add_zero] at h
  revert h
  generalize E.Qf 0 = x
  revert x
  decide

theorem sq_of_functionals {A B : Matrix (Fin n) (Fin n) (ZMod 2)} (a : E.Act A) (b : E.Act B)
    (hl : ∀ l : Fin n → ZMod 2, Aᵀ *ᵥ l = l → Bᵀ *ᵥ l = l → l = 0) (t : T) : t * t = 1 := by
  let Qlin : (Fin n → ZMod 2) →ₗ[ZMod 2] ZMod 2 :=
    AddMonoidHom.toZModLinearMap 2 ⟨⟨E.Qf, E.Qf_zero hcomm⟩, E.Qf_add hcomm⟩
  have hQ : ∀ v, Qlin v = E.Qf v := fun v => rfl
  set l : Fin n → ZMod 2 := fun i => E.Qf (Pi.single i 1) with hl_def
  have hQl : ∀ v, E.Qf v = l ⬝ᵥ v := by
    intro v
    rw [← hQ, LinearMap.pi_apply_eq_sum_univ Qlin v]
    simp only [dotProduct, smul_eq_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    have : (fun j => if i = j then (1 : ZMod 2) else 0) = Pi.single i 1 := by
      funext j
      rw [Pi.single_apply]
      by_cases h : j = i
      · subst h; simp
      · have h' : ¬ i = j := fun e => h e.symm
        simp [h, h']
    rw [this, hQ, mul_comm]
  have hinv : ∀ (M : Matrix (Fin n) (Fin n) (ZMod 2)) (x : E.Act M), Mᵀ *ᵥ l = l := by
    intro M x
    funext j
    have h1 := x.Qf (Pi.single j 1)
    rw [hQl, hQl, Matrix.mulVec_single_one] at h1
    have h2 : (Mᵀ *ᵥ l) j = l ⬝ᵥ M.col j := by
      simp [Matrix.mulVec, dotProduct, mul_comm, Matrix.col]
    rw [h2, h1]
    simp [dotProduct, Pi.single_apply]
  have hl0 : l = 0 := hl l (hinv A a) (hinv B b)
  have h3 : E.sqk t = 0 := by
    rw [E.sqk_eq_Qf, hQl, hl0]
    simp
  rw [E.mul_self_eq_sqk, h3, zz_zero]

theorem exists_section_of_commutes
    (hsq : ∀ t : T, t * t = 1) :
    ∃ s : Multiplicative (Fin n → ZMod 2) →* T, ∀ v, E.ψ (s v) = v := by
  let : CommGroup T := { ‹Group T› with mul_comm := hcomm }
  have : Module (ZMod 2) (Additive T) := AddCommGroup.zmodModule (fun x => by
    rw [two_nsmul]
    exact hsq (Additive.toMul x))
  let ψA : Additive T →+ (Fin n → ZMod 2) :=
    { toFun := fun x => Multiplicative.toAdd (E.ψ (Additive.toMul x))
      map_zero' := by simp
      map_add' := fun x y => by simp }
  let ψL : Additive T →ₗ[ZMod 2] (Fin n → ZMod 2) := AddMonoidHom.toZModLinearMap 2 ψA
  have hsurj : Function.Surjective ψL := by
    intro v
    obtain ⟨t, ht⟩ := E.surj (Multiplicative.ofAdd v)
    exact ⟨Additive.ofMul t, by simp [ψL, ψA, ht]⟩
  obtain ⟨g, hg⟩ := LinearMap.exists_rightInverse_of_surjective ψL (LinearMap.range_eq_top.2 hsurj)
  refine ⟨{ toFun := fun x => Additive.toMul (g (Multiplicative.toAdd x))
            map_one' := by simp
            map_mul' := fun x y => by simp }, fun v => ?_⟩
  have := LinearMap.congr_fun hg (Multiplicative.toAdd v)
  simpa [ψL, ψA] using this

end Abelian

theorem exists_section_of_forms {A B : Matrix (Fin n) (Fin n) (ZMod 2)} (a : E.Act A)
    (b : E.Act B)
    (hC : ∀ c : Matrix (Fin n) (Fin n) (ZMod 2), cᵀ = c → (∀ i, c i i = 0) →
      Aᵀ * c * A = c → Bᵀ * c * B = c → c = 0)
    (hl : ∀ l : Fin n → ZMod 2, Aᵀ *ᵥ l = l → Bᵀ *ᵥ l = l → l = 0) :
    ∃ s : Multiplicative (Fin n → ZMod 2) →* T, ∀ v, E.ψ (s v) = v := by
  have hcomm := E.comm_of_forms a b hC
  exact E.exists_section_of_commutes hcomm (E.sq_of_functionals hcomm a b hl)

end CentralExt

end CFSG.Sporadic.Co1.Cover

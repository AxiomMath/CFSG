module

public import CFSG.Quasithin.Vol2.Ch11SecBK9F
public import CFSG.Quasithin.Vol2.Ch11SecBK9H

public section

set_option linter.unusedSectionVars false

namespace CFSG.Quasithin.Vol2.Ch11.SecB.K9

open Matrix QuadraticMap
open CFSG.Assembly.LowTwoRank (StatedSp)
open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_apply)
open CFSG.LieType.Universal.Spin (quadPlus quadPlus_apply polar_quadPlus)

variable {K : Type} [Field K] [CharP K 2]

theorem isSpForm_quadPlus : IsSpForm (quadPlus 2 K) := fun x y => by
  rw [polar_quadPlus, KGNat.toBilin'_spJ_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  linear_combination y (.inl i) * x (.inr i) * h2

@[expose] noncomputable def sqB (c : Fin 2 ⊕ Fin 2 → K) : QuadraticForm K (Fin 2 ⊕ Fin 2 → K) :=
  linMulLin (spB K c) (spB K c)

@[expose] noncomputable def qOf (c : Fin 2 ⊕ Fin 2 → K) : QuadraticForm K (Fin 2 ⊕ Fin 2 → K) :=
  quadPlus 2 K + sqB c

theorem qOf_apply (c x : Fin 2 ⊕ Fin 2 → K) : qOf c x = quadPlus 2 K x + spB K c x ^ 2 := by
  rw [qOf, _root_.add_apply, sqB, linMulLin_apply, _root_.sq]

theorem isSpForm_qOf (c : Fin 2 ⊕ Fin 2 → K) : IsSpForm (qOf c) := fun x y => by
  rw [← isSpForm_quadPlus x y]
  simp only [polar, qOf_apply, map_add]
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  linear_combination (spB K c x * spB K c y) * h2

theorem qOf_trv {Q : QuadraticForm K (Fin 2 ⊕ Fin 2 → K)} (hQ : IsSpForm Q)
    (y : Fin 2 ⊕ Fin 2 → K) (t : K) (x : Fin 2 ⊕ Fin 2 → K) :
    Q (mat 2 K (K7.trv y t) *ᵥ x) = Q x + (t ^ 2 * Q y + t) * spB K x y ^ 2 := by
  have h := hQ x ((t * spB K x y) • y)
  simp only [polar] at h
  rw [K7.trv_mulVec, show Q (x + (t * spB K x y) • y) =
    Q x + Q ((t * spB K x y) • y) + spB K x ((t * spB K x y) • y) by linear_combination h,
    QuadraticMap.map_smul, K7.bil_smul_right, smul_eq_mul]
  ring

variable [Finite K]

theorem exists_qOf_eq (hK : Nat.card K = 4) {Q : QuadraticForm K (Fin 2 ⊕ Fin 2 → K)}
    (hQ : IsSpForm Q) : ∃ c, Q = qOf c := by
  have := Fintype.ofFinite K
  have h4 : ∀ a : K, a ^ 4 = a := fun a => by
    have h := FiniteField.pow_card a
    rwa [← Nat.card_eq_fintype_card, hK] at h
  set D : (Fin 2 ⊕ Fin 2 → K) → K := fun x => Q x - quadPlus 2 K x with hD
  have hDadd : ∀ x y, D (x + y) = D x + D y := fun x y => by
    have h1 := hQ x y
    have h2 := isSpForm_quadPlus (K := K) x y
    simp only [polar] at h1 h2
    simp only [hD]
    linear_combination h1 - h2
  have hDsmul : ∀ (a : K) x, D (a • x) = a ^ 2 * D x := fun a x => by
    simp only [hD]
    rw [QuadraticMap.map_smul, QuadraticMap.map_smul, smul_eq_mul, smul_eq_mul]
    ring
  let ell : Module.Dual K (Fin 2 ⊕ Fin 2 → K) :=
    { toFun := fun x => D x ^ 2
      map_add' := fun x y => by rw [hDadd, CharTwo.add_sq]
      map_smul' := fun a x => by
        rw [hDsmul, mul_pow, ← pow_mul, show 2 * 2 = 4 by norm_num, h4]
        rfl }
  set c := ((spB K).toDual KGNat.toBilin'_spJ_nondegenerate).symm ell with hc
  have hcl : ∀ x, spB K c x = D x ^ 2 := fun x => by
    have h := LinearMap.BilinForm.toDual_def (b := KGNat.toBilin'_spJ_nondegenerate)
      (m := c) (n := x)
    rw [hc, LinearEquiv.apply_symm_apply] at h
    exact h.symm
  refine ⟨c, QuadraticMap.ext fun x => ?_⟩
  rw [qOf_apply, hcl, ← pow_mul, show 2 * 2 = 4 by norm_num, h4]
  simp only [hD]
  ring

theorem qOf_injective : Function.Injective (qOf (K := K)) := by
  intro c c' h
  apply sub_eq_zero.mp
  apply KGNat.toBilin'_spJ_nondegenerate.1 (c - c')
  intro x
  have h1 := congrArg (fun Q : QuadraticForm K (Fin 2 ⊕ Fin 2 → K) => Q x) h
  simp only [qOf_apply] at h1
  have h2 : (spB K c x - spB K c' x) ^ 2 = 0 := by
    have h2' : (2 : K) = 0 := CharTwo.two_eq_zero
    linear_combination h1 + (spB K c' x ^ 2 - spB K c x * spB K c' x) * h2'
  rw [map_sub, LinearMap.sub_apply]
  exact pow_eq_zero_iff (two_ne_zero) |>.mp h2

theorem isSpForm_comp {Q : QuadraticForm K (Fin 2 ⊕ Fin 2 → K)} (hQ : IsSpForm Q)
    (γ : ↥(StatedSp 2 K)) : IsSpForm (Q.comp (linEquiv γ).toLinearMap) := fun x y => by
  have h := hQ (mat 2 K γ *ᵥ x) (mat 2 K γ *ᵥ y)
  simp only [polar] at h
  simp only [polar, QuadraticMap.comp_apply, LinearEquiv.coe_coe, linEquiv_apply, mulVec_add]
  rw [h]
  exact KGNat.spB_mat γ x y

@[expose] noncomputable def bm (hK : Nat.card K = 4) (γ : ↥(StatedSp 2 K)) :
    Fin 2 ⊕ Fin 2 → K :=
  (exists_qOf_eq hK (isSpForm_comp (isSpForm_quadPlus (K := K)) γ⁻¹)).choose

theorem bm_spec (hK : Nat.card K = 4) (γ : ↥(StatedSp 2 K)) :
    (quadPlus 2 K).comp (linEquiv γ⁻¹).toLinearMap = qOf (bm hK γ) :=
  (exists_qOf_eq hK (isSpForm_comp (isSpForm_quadPlus (K := K)) γ⁻¹)).choose_spec

theorem spB_inv (γ : ↥(StatedSp 2 K)) (c x : Fin 2 ⊕ Fin 2 → K) :
    spB K c (mat 2 K γ⁻¹ *ᵥ x) = spB K (mat 2 K γ *ᵥ c) x := by
  rw [← KGNat.spB_mat γ c, KGNat.mat_mulVec_inv]

theorem qOf_comp (hK : Nat.card K = 4) (γ : ↥(StatedSp 2 K)) (c : Fin 2 ⊕ Fin 2 → K) :
    (qOf c).comp (linEquiv γ⁻¹).toLinearMap = qOf (mat 2 K γ *ᵥ c + bm hK γ) := by
  refine QuadraticMap.ext fun x => ?_
  have h := congrArg (fun Q : QuadraticForm K (Fin 2 ⊕ Fin 2 → K) => Q x) (bm_spec hK γ)
  simp only [QuadraticMap.comp_apply, LinearEquiv.coe_coe, linEquiv_apply] at h ⊢
  rw [qOf_apply, h, qOf_apply, qOf_apply, spB_inv, spB_add_left, CharTwo.add_sq]
  ring

theorem qOf_zero : qOf (0 : Fin 2 ⊕ Fin 2 → K) = quadPlus 2 K := by
  refine QuadraticMap.ext fun x => ?_
  rw [qOf_apply, map_zero, LinearMap.zero_apply, zero_pow two_ne_zero, add_zero]

theorem bm_mul (hK : Nat.card K = 4) (γ δ : ↥(StatedSp 2 K)) :
    bm hK (γ * δ) = bm hK γ + mat 2 K γ *ᵥ bm hK δ := by
  apply qOf_injective
  rw [← bm_spec, add_comm, ← qOf_comp, ← bm_spec]
  refine QuadraticMap.ext fun x => ?_
  simp only [QuadraticMap.comp_apply, LinearEquiv.coe_coe, linEquiv_apply]
  rw [_root_.mul_inv_rev, map_mul, mulVec_mulVec]

theorem trv_mul_self (y : Fin 2 ⊕ Fin 2 → K) (t : K) : K7.trv y t * K7.trv y t = 1 := by
  rw [K7.trv_mul, CharTwo.add_self_eq_zero, K7.trv_zero]

theorem bm_trv (hK : Nat.card K = 4) (y : Fin 2 ⊕ Fin 2 → K) (t : K) :
    bm hK (K7.trv y t) = (quadPlus 2 K y ^ 2 * t + t ^ 2) • y := by
  have := Fintype.ofFinite K
  have h4 : ∀ a : K, a ^ 4 = a := fun a => by
    have h := FiniteField.pow_card a
    rwa [← Nat.card_eq_fintype_card, hK] at h
  apply qOf_injective
  rw [← bm_spec, inv_eq_of_mul_eq_one_right (trv_mul_self y t)]
  refine QuadraticMap.ext fun x => ?_
  simp only [QuadraticMap.comp_apply, LinearEquiv.coe_coe, linEquiv_apply]
  rw [qOf_trv isSpForm_quadPlus, qOf_apply, K7.bil_smul_left, K7.bil_comm y x, mul_pow]
  have e1 : (quadPlus 2 K y ^ 2) ^ 2 = quadPlus 2 K y := by
    rw [← pow_mul]
    exact h4 _
  have e2 : (t ^ 2) ^ 2 = t := by
    rw [← pow_mul]
    exact h4 _
  rw [CharTwo.add_sq, mul_pow, e1, e2]
  ring

@[expose] noncomputable def bmCocycle (hK : Nat.card K = 4) : RootCocycle K where
  c := bm hK
  mul := bm_mul hK
  root y _ t := ⟨_, bm_trv hK y t⟩

theorem bmCocycle_coef (hK : Nat.card K = 4) {y : Fin 2 ⊕ Fin 2 → K} (hy : y ≠ 0) :
    ((bmCocycle hK).coef hK y).2 = 1 := by
  refine (lin_frob_unique hK (α := ((bmCocycle hK).coef hK y).1) (α' := quadPlus 2 K y ^ 2)
    (β' := 1) fun t => ?_).2
  rw [← (bmCocycle hK).rho_eq hK hy]
  apply smul_left_cancel hy
  rw [← (bmCocycle hK).rho_spec hy, one_mul]
  show bm hK (K7.trv y t) = _
  rw [bm_trv]

end CFSG.Quasithin.Vol2.Ch11.SecB.K9

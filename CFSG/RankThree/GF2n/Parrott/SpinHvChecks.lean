module

public import CFSG.RankThree.GF2n.Parrott.SpinConfig
public import CFSG.RankThree.GF2n.Parrott.SpinPack45

public section

namespace CFSG.RankThree.GF2n.Parrott

open CFSG.ComponentClassification.CatFactsSmall.PSp43 CFSG.GH74.KGroups
open scoped Matrix commutatorElement
open CFSG.KS.PCnt (pkw)
open CFSG.Permutation.FinPack64 (pk_mul eq_of_pk comm_mul_of)
open CFSG.RankThree.GF2n.Parrott.Pack45 (h45 pk_one pk_t pk_u pk_v)
open CFSG.RankThree.GF2n.Parrott.SpinPack45 (cB0 cG1 cG2 pk_B0 pk_G1 pk_G2 pk_CjA pk_CjB)

set_option quotPrecheck false in
local notation "A45" => ↥QA45.originalSubgroup
set_option quotPrecheck false in
local notation "tA" => (⟨t, t_mem_A⟩ : A45)
set_option quotPrecheck false in
local notation "uA" => (⟨u, u_mem_A⟩ : A45)
set_option quotPrecheck false in
local notation "vA" => (⟨v, v_mem_A⟩ : A45)
set_option quotPrecheck false in
local notation "xA" => (⟨x45, Q45_le_A45 x45_mem_Q⟩ : A45)
set_option quotPrecheck false in
local notation "yA" => (⟨y45, Q45_le_A45 y45_mem_Q⟩ : A45)
set_option quotPrecheck false in
local notation "fA" => (⟨f45, f45_mem_A⟩ : A45)
local notation "GL8" => Matrix.GeneralLinearGroup (Fin 8) (ZMod 2)
local notation "Mat8" => Matrix (Fin 8) (Fin 8) (ZMod 2)

@[expose] def spinMv : Mat8 :=
  !![1,0,0,0,0,0,0,0; 1,0,1,1,0,1,0,0; 1,0,1,0,0,1,0,0; 0,1,1,0,0,0,0,0;
     1,1,1,1,1,0,0,0; 0,0,0,0,0,1,0,0; 1,0,0,0,0,1,1,1; 0,0,0,0,0,0,0,1]

@[expose] def spinMvUV : Mat8 :=
  !![1,0,0,0,0,1,0,0; 1,0,1,1,0,1,0,0; 0,1,1,0,1,0,0,0; 1,0,1,0,1,0,0,0;
     1,1,1,1,1,1,0,0; 0,0,0,0,0,1,0,0; 0,0,1,1,0,0,1,1; 1,1,1,1,0,0,0,1]

@[expose] def spinMvvUV : Mat8 :=
  !![1,0,0,0,0,1,0,0; 0,1,0,0,0,0,0,0; 1,1,1,0,1,0,0,0; 1,1,0,1,1,1,0,0;
     0,0,0,0,1,1,0,0; 0,0,0,0,0,1,0,0; 0,1,0,0,0,0,1,0; 1,1,1,1,0,0,0,1]

theorem spinMv_fixed_mem_range : ∀ w : V, spinMv *ᵥ w = w → ∃ u : V, spinMv *ᵥ u + u = w := by
  decide +kernel

theorem exists_spinMv_fixed_q_eq_one : ∃ w : V, spinMv *ᵥ w = w ∧ q w = 1 := by
  decide +kernel

theorem spinMvUV_fixed_mem_range : ∀ w : V, spinMvUV *ᵥ w = w →
    ∃ u : V, spinMvUV *ᵥ u + u = w := by
  decide +kernel

theorem spinMvUV_fixed_singular : ∀ w : V, spinMvUV *ᵥ w = w → q w = 0 := by
  decide +kernel

theorem spinMvvUV_fixed_mem_range : ∀ w : V, spinMvvUV *ᵥ w = w →
    ∃ u : V, spinMvvUV *ᵥ u + u = w := by
  decide +kernel

theorem spinMv_spinMvUV_fixed_mem_image : ∀ w : V, spinMv *ᵥ w = w → spinMvUV *ᵥ w = w →
    ∃ u : V, spinMvUV *ᵥ u = u ∧ spinMv *ᵥ u + u = w := by
  decide +kernel

theorem Mx_hyperbolic_pairs : ∃ u₁ u₂ u₃ u₄ : V,
    Mx *ᵥ u₁ = u₁ ∧ Mx *ᵥ u₂ = u₂ ∧ Mx *ᵥ u₃ = u₃ ∧ Mx *ᵥ u₄ = u₄ ∧
    b u₁ u₂ ≠ 0 ∧ b u₃ u₄ ≠ 0 ∧ b u₁ u₃ = 0 ∧ b u₁ u₄ = 0 ∧ b u₂ u₃ = 0 ∧ b u₂ u₄ = 0 := by
  refine ⟨![0,1,0,1,0,0,0,0], ![1,0,0,0,0,1,0,0], ![0,1,0,1,0,0,1,0],
    ![1,0,0,0,0,1,0,1], ?_⟩
  decide +kernel


@[expose] def vUV : A45 := yA * xA * yA * xA * yA * fA * yA * xA * yA * yA
@[expose] def vUVG₁ : A45 := yA * yA * yA * yA * xA * yA
@[expose] def vUVG₂ : A45 := yA * yA * fA * yA * xA * yA * fA * yA * xA

private theorem pk_vUV : pkw 6 ((vUV : A45) : Equiv.Perm (Fin 45)) = cB0 := pk_B0

private theorem pk_vUVG₁ : pkw 6 ((vUVG₁ : A45) : Equiv.Perm (Fin 45)) = cG1 := pk_G1

private theorem pk_vUVG₂ : pkw 6 ((vUVG₂ : A45) : Equiv.Perm (Fin 45)) = cG2 := pk_G2

theorem vUV_mul_self : vUV * vUV = 1 := by
  apply Subtype.ext
  rw [Subgroup.coe_mul, Subgroup.coe_one]
  exact eq_of_pk h45 (pk_mul h45 pk_vUV pk_vUV) pk_one (by decide +kernel)

theorem vUVG₁_commute : vUVG₁ * vUV = vUV * vUVG₁ := by
  apply Subtype.ext
  rw [Subgroup.coe_mul, Subgroup.coe_mul]
  exact eq_of_pk h45 (pk_mul h45 pk_vUVG₁ pk_vUV) (pk_mul h45 pk_vUV pk_vUVG₁) (by decide +kernel)

theorem vUVG₂_commute : vUVG₂ * vUV = vUV * vUVG₂ := by
  apply Subtype.ext
  rw [Subgroup.coe_mul, Subgroup.coe_mul]
  exact eq_of_pk h45 (pk_mul h45 pk_vUVG₂ pk_vUV) (pk_mul h45 pk_vUV pk_vUVG₂) (by decide +kernel)

theorem rhoA_vUV_eq_spinMvUV : ((rhoA vUV : GL8) : Mat8) = spinMvUV := by
  rw [vUV]
  simp only [map_mul, rhoA_x, rhoA_y, rhoA_f]
  show My * Mx * My * Mx * My * Mf * My * Mx * My * My = spinMvUV
  decide +kernel

theorem rhoA_vUV_fixed_mem_range : ∀ w : V, ((rhoA vUV : GL8) : Mat8) *ᵥ w = w →
    ∃ u : V, ((rhoA vUV : GL8) : Mat8) *ᵥ u + u = w := by
  rw [rhoA_vUV_eq_spinMvUV]
  exact spinMvUV_fixed_mem_range

theorem rhoA_vUV_fixed_singular : ∀ w : V, ((rhoA vUV : GL8) : Mat8) *ᵥ w = w → q w = 0 := by
  rw [rhoA_vUV_eq_spinMvUV]
  exact spinMvUV_fixed_singular


theorem commutator_vUVG_mul_vUV : ⁅vUVG₁, vUVG₂⁆ * vUV = vA := by
  rw [commutatorElement_def]
  refine comm_mul_of vUV_mul_self ?_
  apply Subtype.ext
  simp only [Subgroup.coe_mul]
  exact eq_of_pk h45 (pk_mul h45 pk_vUVG₁ pk_vUVG₂)
    (pk_mul h45 (pk_mul h45 (pk_mul h45 pk_v pk_vUV) pk_vUVG₂) pk_vUVG₁) (by decide +kernel)

theorem isConj_vUV : IsConj vUV (uA * vA) := by
  refine (isConj_iff.mpr ⟨yA * yA * fA * yA * yA * yA, mul_inv_eq_of_eq_mul ?_⟩).symm
  apply Subtype.ext
  simp only [Subgroup.coe_mul]
  exact eq_of_pk h45 (pk_mul h45 pk_CjA (pk_mul h45 pk_u pk_v)) (pk_mul h45 pk_vUV pk_CjA)
    (by decide +kernel)

theorem isConj_v_mul_vUV : IsConj (vA * vUV) (uA * tA) := by
  refine (isConj_iff.mpr ⟨yA * xA * yA * yA * yA * fA * yA * fA * yA,
    mul_inv_eq_of_eq_mul ?_⟩).symm
  apply Subtype.ext
  simp only [Subgroup.coe_mul]
  exact eq_of_pk h45 (pk_mul h45 pk_CjB (pk_mul h45 pk_u pk_t))
    (pk_mul h45 (pk_mul h45 pk_v pk_vUV) pk_CjB) (by decide +kernel)

theorem rhoA_t_eq_Mx : ((rhoA tA : GL8) : Mat8) = Mx := by
  have h : tA = (⟨x45, Q45_le_A45 x45_mem_Q⟩ : A45) := Subtype.ext rfl
  rw [h, rhoA_x]
  rfl

theorem rhoA_v_eq_spinMv : ((rhoA vA : GL8) : Mat8) = spinMv := by
  rw [rhoA_v, Units.val_mul]
  show Mx * Mf = spinMv
  decide +kernel

theorem rhoA_v_mul_vUV_eq_spinMvvUV : ((rhoA (vA * vUV) : GL8) : Mat8) = spinMvvUV := by
  rw [map_mul, Units.val_mul, rhoA_v_eq_spinMv, rhoA_vUV_eq_spinMvUV]
  show spinMv * spinMvUV = spinMvvUV
  decide +kernel

theorem rhoA_v_fixed_mem_range : ∀ w : V, ((rhoA vA : GL8) : Mat8) *ᵥ w = w →
    ∃ u : V, ((rhoA vA : GL8) : Mat8) *ᵥ u + u = w := by
  rw [rhoA_v_eq_spinMv]
  exact spinMv_fixed_mem_range

theorem exists_rhoA_v_fixed_q_eq_one : ∃ w : V, ((rhoA vA : GL8) : Mat8) *ᵥ w = w ∧ q w = 1 := by
  rw [rhoA_v_eq_spinMv]
  exact exists_spinMv_fixed_q_eq_one

theorem rhoA_v_vUV_fixed_mem_image : ∀ w : V, ((rhoA vA : GL8) : Mat8) *ᵥ w = w →
    ((rhoA vUV : GL8) : Mat8) *ᵥ w = w →
    ∃ u : V, ((rhoA vUV : GL8) : Mat8) *ᵥ u = u ∧ ((rhoA vA : GL8) : Mat8) *ᵥ u + u = w := by
  rw [rhoA_v_eq_spinMv, rhoA_vUV_eq_spinMvUV]
  exact spinMv_spinMvUV_fixed_mem_image

theorem rhoA_v_mul_vUV_fixed_mem_range : ∀ w : V, ((rhoA (vA * vUV) : GL8) : Mat8) *ᵥ w = w →
    ∃ u : V, ((rhoA (vA * vUV) : GL8) : Mat8) *ᵥ u + u = w := by
  rw [rhoA_v_mul_vUV_eq_spinMvvUV]
  exact spinMvvUV_fixed_mem_range

theorem rhoA_t_hyperbolic_pairs : ∃ u₁ u₂ u₃ u₄ : V,
    ((rhoA tA : GL8) : Mat8) *ᵥ u₁ = u₁ ∧ ((rhoA tA : GL8) : Mat8) *ᵥ u₂ = u₂ ∧
    ((rhoA tA : GL8) : Mat8) *ᵥ u₃ = u₃ ∧ ((rhoA tA : GL8) : Mat8) *ᵥ u₄ = u₄ ∧
    b u₁ u₂ ≠ 0 ∧ b u₃ u₄ ≠ 0 ∧ b u₁ u₃ = 0 ∧ b u₁ u₄ = 0 ∧ b u₂ u₃ = 0 ∧ b u₂ u₄ = 0 := by
  rw [rhoA_t_eq_Mx]
  exact Mx_hyperbolic_pairs

end CFSG.RankThree.GF2n.Parrott

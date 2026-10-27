module

public import CFSG.RankThree.GF2n.Parrott.SpinFixedCardMore
public import CFSG.RankThree.GF2n.Parrott.SpinPack45

public section

namespace CFSG.RankThree.GF2n.Parrott

open CFSG.ComponentClassification.CatFactsSmall.PSp43 CFSG.GH74.KGroups
open scoped Matrix
open CFSG.KS.PCnt (pkw)
open CFSG.Permutation.FinPack64 (pk_mul eq_of_pk ne_of_pk pow_eq_one_of)
open CFSG.RankThree.GF2n.Parrott.Pack45 (h45 pk_one pk_x pk_u pk_v)
open CFSG.RankThree.GF2n.Parrott.SpinPack45 (cW pk_W)

set_option quotPrecheck false in
local notation "A45" => ↥QA45.originalSubgroup
set_option quotPrecheck false in
local notation "uA" => (⟨u, u_mem_A⟩ : A45)
set_option quotPrecheck false in
local notation "vA" => (⟨v, v_mem_A⟩ : A45)
local notation "GL8" => Matrix.GeneralLinearGroup (Fin 8) (ZMod 2)
local notation "Mat8" => Matrix (Fin 8) (Fin 8) (ZMod 2)

@[expose] def spinMuv : Mat8 :=
  !![1,0,0,0,0,0,0,0; 1,0,1,1,0,1,0,0; 1,0,1,0,0,1,0,0; 0,1,1,0,0,0,0,0;
     1,1,1,1,1,0,0,0; 0,0,0,0,0,1,0,0; 0,1,0,0,1,1,1,1; 0,0,0,0,0,1,0,1]
@[expose] def spinM5uv : Mat8 :=
  !![1,1,1,1,0,1,0,0; 0,0,0,0,1,1,1,1; 0,0,0,1,0,0,1,0; 1,0,0,1,1,0,0,1;
     1,1,1,0,0,0,0,0; 1,1,0,0,1,0,0,1; 1,1,1,1,1,1,1,0; 1,0,0,1,1,0,1,1]
@[expose] def spinM3uv : Mat8 :=
  !![1,1,1,1,0,1,0,0; 1,1,1,0,0,0,0,1; 1,0,1,0,0,1,1,1; 1,1,1,1,1,1,1,1;
     0,1,1,1,0,1,1,0; 0,0,1,1,1,0,0,1; 1,1,1,1,1,1,1,0; 0,0,0,1,0,0,1,1]

private def permW : Equiv.Perm (Fin 45) :=
  f45 * y45 ^ 3 * f45 * y45 ^ 2 * f45 * y45

private theorem pk_permW : pkw 6 permW = cW := pk_W

private theorem permW_sq_pow_five : (permW * permW) ^ 5 = 1 :=
  pow_eq_one_of h45 pk_one (pk_mul h45 pk_permW pk_permW) 5 (by decide +kernel)

private theorem permW_sq_ne_one : permW * permW ≠ 1 :=
  ne_of_pk (pk_mul h45 pk_permW pk_permW) pk_one (by decide +kernel)

private theorem permT_pow_three : ((x45 * permW) * (x45 * permW)) ^ 3 = 1 :=
  pow_eq_one_of h45 pk_one (pk_mul h45 (pk_mul h45 pk_x pk_permW) (pk_mul h45 pk_x pk_permW)) 3
    (by decide +kernel)

private theorem permT_ne_one : ((x45 * permW) * (x45 * permW)) ≠ 1 :=
  ne_of_pk (pk_mul h45 (pk_mul h45 pk_x pk_permW) (pk_mul h45 pk_x pk_permW)) pk_one
    (by decide +kernel)

theorem spinMuv_mul_self : spinMuv * spinMuv = 1 := by decide +kernel

theorem spinMuv_fixed_singular : ∀ w : V, spinMuv *ᵥ w = w → q w = 0 := by
  decide +kernel

theorem spinMuv_fixed_mem_range : ∀ w : V, spinMuv *ᵥ w = w → ∃ u : V, spinMuv *ᵥ u + u = w := by
  decide +kernel

private def trunc (n : ℕ) (v : V) : V := fun i => if (i : ℕ) < n then v i else 0

private def Fc (σ : Mat8) (c : V) : ℕ → V → ZMod 2
  | 0, _ => 0
  | n + 1, v => Fc σ c n v +
      (if h : n < 8 then
        (if v ⟨n, h⟩ = 1 then c ⟨n, h⟩ + b (trunc n v) ((σ + 1) *ᵥ Pi.single ⟨n, h⟩ 1) else 0)
      else 0)

set_option maxRecDepth 100000 in
private theorem psi_check : ∀ c : V, ¬ (∀ j : Fin 8,
    Fc spinMuv c 8 (spinM5uv *ᵥ Pi.single j 1) = c j ∧
    Fc spinMuv c 8 (spinM3uv *ᵥ Pi.single j 1) = c j) := by
  decide +kernel

private theorem Fc_succ (σ : Mat8) (c : V) (n : ℕ) (hn : n < 8) (v : V) :
    Fc σ c (n + 1) v = Fc σ c n v +
      (if v ⟨n, hn⟩ = 1 then c ⟨n, hn⟩ +
        b (trunc n v) ((σ + 1) *ᵥ Pi.single ⟨n, hn⟩ 1) else 0) := by
  rw [show Fc σ c (n + 1) v = Fc σ c n v +
      (if h : n < 8 then (if v ⟨n, h⟩ = 1 then c ⟨n, h⟩ +
        b (trunc n v) ((σ + 1) *ᵥ Pi.single ⟨n, h⟩ (1 : ZMod 2)) else 0) else 0) from rfl,
    dif_pos hn]

private theorem trunc_succ (n : ℕ) (hn : n < 8) (v : V) :
    trunc (n + 1) v = trunc n v +
      (if v ⟨n, hn⟩ = 1 then Pi.single ⟨n, hn⟩ (1 : ZMod 2) else 0) := by
  funext i
  rw [Pi.add_apply]
  have hz : ∀ x : ZMod 2, x = 0 ∨ x = 1 := by decide
  by_cases hi : (i : ℕ) = n
  · have hii : i = ⟨n, hn⟩ := Fin.ext (by simpa using hi)
    subst hii
    simp only [trunc, lt_self_iff_false, if_false, Nat.lt_succ_self, if_true, zero_add]
    rcases hz (v ⟨n, hn⟩) with h | h <;> simp [h]
  · have hsingle :
        (if v ⟨n, hn⟩ = 1 then (Pi.single ⟨n, hn⟩ (1 : ZMod 2) : V) else 0) i = 0 := by
      by_cases hv : v ⟨n, hn⟩ = 1
      · rw [if_pos hv]
        exact Pi.single_eq_of_ne (by intro h; exact hi (by rw [h])) 1
      · rw [if_neg hv]
        rfl
    rw [hsingle, add_zero]
    simp only [trunc]
    by_cases hlt : (i : ℕ) < n
    · rw [if_pos (by omega), if_pos hlt]
    · rw [if_neg (by omega), if_neg hlt]

private theorem trunc_eight (v : V) : trunc 8 v = v := by
  funext i
  simp [trunc, i.isLt]

private theorem b_zero_right : ∀ v : V, b v 0 = 0 := by decide +kernel

theorem spinMuv_no_psi : ¬ ∃ ψ : V → ZMod 2,
    (∀ v w, ψ (v + w) = ψ v + ψ w + b v ((spinMuv + 1) *ᵥ w)) ∧
    (∀ v, ψ (spinM5uv *ᵥ v) = ψ v) ∧ (∀ v, ψ (spinM3uv *ᵥ v) = ψ v) := by
  rintro ⟨ψ, hc, h5, h3⟩
  let c : V := fun i => ψ (Pi.single i 1)
  have hpsi0 : ψ 0 = 0 := by
    have h := hc 0 0
    have hb : b 0 ((spinMuv + 1) *ᵥ 0) = 0 := by decide +kernel
    rw [hb] at h
    have h' : ψ 0 + 0 = ψ 0 + ψ 0 := by
      simpa using h
    exact (add_left_cancel h').symm
  have htr : ∀ n, n ≤ 8 → ∀ v : V, ψ (trunc n v) = Fc spinMuv c n v := by
    intro n
    induction n with
    | zero =>
      intro _ v
      have h0 : trunc 0 v = 0 := by funext i; simp [trunc]
      rw [h0]
      simp [Fc, hpsi0]
    | succ n ih =>
      intro hn v
      have hn8 : n < 8 := by omega
      rw [trunc_succ n hn8 v, hc, ih (by omega) v, Fc_succ spinMuv c n hn8 v]
      by_cases hv : v ⟨n, hn8⟩ = 1
      · simp only [if_pos hv]
        rw [add_assoc]
      · simp only [if_neg hv]
        simp [hpsi0, b_zero_right]
  apply psi_check c
  intro j
  constructor
  · rw [← htr 8 le_rfl, trunc_eight, h5]
  · rw [← htr 8 le_rfl, trunc_eight, h3]


@[expose] def uvW : A45 :=
  (⟨f45, f45_mem_A⟩ : A45) * (⟨y45, Q45_le_A45 y45_mem_Q⟩ : A45) ^ 3 * (⟨f45, f45_mem_A⟩ : A45) *
    (⟨y45, Q45_le_A45 y45_mem_Q⟩ : A45) ^ 2 * (⟨f45, f45_mem_A⟩ : A45) *
    (⟨y45, Q45_le_A45 y45_mem_Q⟩ : A45)
@[expose] def uvFive : A45 := uvW * uvW
@[expose] def uvThree : A45 :=
  ((⟨x45, Q45_le_A45 x45_mem_Q⟩ : A45) * uvW) * ((⟨x45, Q45_le_A45 x45_mem_Q⟩ : A45) * uvW)

private theorem coe_uvFive : ((uvFive : A45) : Equiv.Perm (Fin 45)) = permW * permW := rfl

private theorem coe_uvThree : ((uvThree : A45) : Equiv.Perm (Fin 45)) =
    (x45 * permW) * (x45 * permW) := rfl

theorem orderOf_uvFive : orderOf uvFive = 5 := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  refine orderOf_eq_prime ?_ ?_
  · have h : ((uvFive ^ 5 : A45) : Equiv.Perm (Fin 45)) = 1 := by
      rw [Subgroup.coe_pow, coe_uvFive, permW_sq_pow_five]
    exact Subtype.ext h
  · intro h
    have h' : ((uvFive : A45) : Equiv.Perm (Fin 45)) = 1 := by rw [h]; rfl
    rw [coe_uvFive] at h'
    exact permW_sq_ne_one h'

theorem orderOf_uvThree : orderOf uvThree = 3 := by
  have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  refine orderOf_eq_prime ?_ ?_
  · have h : ((uvThree ^ 3 : A45) : Equiv.Perm (Fin 45)) = 1 := by
      rw [Subgroup.coe_pow, coe_uvThree, permT_pow_three]
    exact Subtype.ext h
  · intro h
    have h' : ((uvThree : A45) : Equiv.Perm (Fin 45)) = 1 := by rw [h]; rfl
    rw [coe_uvThree] at h'
    exact permT_ne_one h'

private theorem rhoA_uvW_val : ((rhoA uvW : GL8) : Mat8) =
    Mf * My ^ 3 * Mf * My ^ 2 * Mf * My := by
  rw [uvW]
  simp only [map_mul, map_pow, rhoA_f, rhoA_y]
  rfl

private theorem rhoA_xuvW_val : ((rhoA ((⟨x45, Q45_le_A45 x45_mem_Q⟩ : A45) * uvW) : GL8) : Mat8) =
    Mx * (Mf * My ^ 3 * Mf * My ^ 2 * Mf * My) := by
  rw [map_mul, rhoA_x, Units.val_mul, rhoA_uvW_val]
  rfl

theorem rhoA_uvFive : ((rhoA uvFive : GL8) : Mat8) = spinM5uv := by
  have h : rhoA uvFive = rhoA uvW * rhoA uvW := by rw [uvFive, map_mul]
  rw [h, Units.val_mul, rhoA_uvW_val]
  show (Mf * My ^ 3 * Mf * My ^ 2 * Mf * My) * (Mf * My ^ 3 * Mf * My ^ 2 * Mf * My) = spinM5uv
  decide +kernel

theorem rhoA_uvThree : ((rhoA uvThree : GL8) : Mat8) = spinM3uv := by
  have h : rhoA uvThree = rhoA ((⟨x45, Q45_le_A45 x45_mem_Q⟩ : A45) * uvW) *
      rhoA ((⟨x45, Q45_le_A45 x45_mem_Q⟩ : A45) * uvW) := by rw [uvThree, map_mul]
  rw [h, Units.val_mul, rhoA_xuvW_val]
  show (Mx * (Mf * My ^ 3 * Mf * My ^ 2 * Mf * My)) *
      (Mx * (Mf * My ^ 3 * Mf * My ^ 2 * Mf * My)) = spinM3uv
  decide +kernel


theorem rhoA_uv_eq_spinMuv : ((rhoA (uA * vA) : GL8) : Mat8) = spinMuv := by
  have h : rhoA (uA * vA) = evalW MxUnit MyUnit uWord * MxUnit * MfUnit := rhoA_u_mul_v
  rw [h, Units.val_mul, Units.val_mul, coe_evalW_genUnit]
  show matWord (toSpinWord uWord) * Mx * Mf = spinMuv
  decide +kernel

theorem uvFive_commute : (uA * vA) * uvFive = uvFive * (uA * vA) := by
  apply Subtype.ext
  simp only [Subgroup.coe_mul, coe_uvFive]
  exact eq_of_pk h45 (pk_mul h45 (pk_mul h45 pk_u pk_v) (pk_mul h45 pk_permW pk_permW))
    (pk_mul h45 (pk_mul h45 pk_permW pk_permW) (pk_mul h45 pk_u pk_v)) (by decide +kernel)

theorem uvThree_commute : (uA * vA) * uvThree = uvThree * (uA * vA) := by
  apply Subtype.ext
  simp only [Subgroup.coe_mul, coe_uvThree]
  exact eq_of_pk h45 (pk_mul h45 (pk_mul h45 pk_u pk_v)
      (pk_mul h45 (pk_mul h45 pk_x pk_permW) (pk_mul h45 pk_x pk_permW)))
    (pk_mul h45 (pk_mul h45 (pk_mul h45 pk_x pk_permW) (pk_mul h45 pk_x pk_permW))
      (pk_mul h45 pk_u pk_v)) (by decide +kernel)

end CFSG.RankThree.GF2n.Parrott

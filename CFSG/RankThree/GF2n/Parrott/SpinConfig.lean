module

public import CFSG.RankThree.GF2n.Parrott.SpinFixedCardMore
public import CFSG.RankThree.GF2n.Parrott.SpinFixedCardUT
public import CFSG.RankThree.GF2n.Parrott.SpinPack45

public section

namespace CFSG.RankThree.GF2n.Parrott

open CFSG.ComponentClassification.CatFactsSmall.PSp43 CFSG.GH74.KGroups
open scoped Matrix commutatorElement
open CFSG.KS.PCnt (pkw)
open CFSG.Permutation.FinPack64 (mulW pk_mul eq_of_pk conj_of)
open CFSG.RankThree.GF2n.Parrott.Pack45 (h45 cF pk_one pk_x pk_u pk_v pk_f)
open CFSG.RankThree.GF2n.Parrott.SpinPack45 (cCg2 cCut cCv pk_Cg2 pk_Cut pk_Cv)

local notation "GL8" => Matrix.GeneralLinearGroup (Fin 8) (ZMod 2)
set_option quotPrecheck false in
local notation "A45" => ↥QA45.originalSubgroup
set_option quotPrecheck false in
local notation "tA" => (⟨t, t_mem_A⟩ : A45)
set_option quotPrecheck false in
local notation "uA" => (⟨u, u_mem_A⟩ : A45)
set_option quotPrecheck false in
local notation "vA" => (⟨v, v_mem_A⟩ : A45)

theorem fixCard_Mx_mul_Mf : fixCard (Mx * Mf) = 16 := by
  decide +kernel

@[expose] def cfgG2P : Equiv.Perm (Fin 45) := y45 * x45 * y45 * y45 * y45 * y45
@[expose] def cfgBP : Equiv.Perm (Fin 45) := f45 * cfgG2P * f45⁻¹ * cfgG2P⁻¹
@[expose] def cfgCutP : Equiv.Perm (Fin 45) :=
  f45 * y45 * x45 * y45 * y45 * y45 * x45 * f45 * y45 * f45 * y45 * y45
@[expose] def cfgCvP : Equiv.Perm (Fin 45) :=
  y45 * x45 * f45 * y45 * x45 * y45 * y45 * f45 * y45 * x45 * y45 * f45 * y45

private theorem pk_cfgG2P : pkw 6 cfgG2P = cCg2 := pk_Cg2
private theorem pk_cfgCutP : pkw 6 cfgCutP = cCut := pk_Cut
private theorem pk_cfgCvP : pkw 6 cfgCvP = cCv := pk_Cv

private theorem cfg_f_inv : f45⁻¹ = f45 :=
  (eq_inv_of_mul_eq_one_left (eq_of_pk h45 (pk_mul h45 pk_f pk_f) pk_one (by decide +kernel))).symm

private theorem cfg_g2_inv : cfgG2P⁻¹ = cfgG2P :=
  (eq_inv_of_mul_eq_one_left
    (eq_of_pk h45 (pk_mul h45 pk_cfgG2P pk_cfgG2P) pk_one (by decide +kernel))).symm

private theorem pk_cfgBP : pkw 6 cfgBP = mulW 45 (mulW 45 (mulW 45 cF cCg2) cF) cCg2 := by
  unfold cfgBP
  rw [cfg_f_inv, cfg_g2_inv]
  exact pk_mul h45 (pk_mul h45 (pk_mul h45 pk_f pk_cfgG2P) pk_f) pk_cfgG2P

theorem cfgP_comm1 : u * v * f45 = f45 * (u * v) :=
  eq_of_pk h45 (pk_mul h45 (pk_mul h45 pk_u pk_v) pk_f) (pk_mul h45 pk_f (pk_mul h45 pk_u pk_v))
    (by decide +kernel)
theorem cfgP_comm2 : u * v * cfgG2P = cfgG2P * (u * v) :=
  eq_of_pk h45 (pk_mul h45 (pk_mul h45 pk_u pk_v) pk_cfgG2P)
    (pk_mul h45 pk_cfgG2P (pk_mul h45 pk_u pk_v)) (by decide +kernel)
theorem cfgP_b_sq : cfgBP * cfgBP = 1 :=
  eq_of_pk h45 (pk_mul h45 pk_cfgBP pk_cfgBP) pk_one (by decide +kernel)
theorem cfgP_conj1 : cfgCutP * cfgBP * cfgCutP⁻¹ = u * x45 :=
  conj_of h45 pk_cfgCutP pk_cfgBP (pk_mul h45 pk_u pk_x) (by decide +kernel)
theorem cfgP_conj2 : cfgCvP * (u * v * cfgBP) * cfgCvP⁻¹ = v :=
  conj_of h45 pk_cfgCvP (pk_mul h45 (pk_mul h45 pk_u pk_v) pk_cfgBP) pk_v (by decide +kernel)
theorem cfgP_uv_sq : u * v * (u * v) = 1 :=
  eq_of_pk h45 (pk_mul h45 (pk_mul h45 pk_u pk_v) (pk_mul h45 pk_u pk_v)) pk_one
    (by decide +kernel)
theorem cfgP_f_inv : f45⁻¹ = f45 := cfg_f_inv
theorem cfgP_g2_inv : cfgG2P⁻¹ = cfgG2P := cfg_g2_inv

@[expose] def cfgMa : Matrix (Fin 8) (Fin 8) (ZMod 2) := matWord (toSpinWord uWord) * Mx * Mf
@[expose] def cfgMg : Matrix (Fin 8) (Fin 8) (ZMod 2) := My * Mx * My * My * My * My
@[expose] def cfgMb : Matrix (Fin 8) (Fin 8) (ZMod 2) := Mf * cfgMg * Mf * cfgMg

theorem cfgM_q : ∀ w : V, cfgMa *ᵥ w = w → q w = 0 := by decide +kernel

theorem cfgM_inter : ∀ w : V, cfgMa *ᵥ w = w → cfgMb *ᵥ w = w →
    w = ![0, 0, 0, 0, 0, 0, 0, 0] ∨ w = ![0, 0, 1, 1, 1, 0, 0, 1] ∨
    w = ![0, 1, 0, 1, 1, 0, 1, 0] ∨ w = ![0, 1, 1, 0, 0, 0, 1, 1] := by decide +kernel

theorem cfgM_wit0 : cfgMa *ᵥ ![0, 0, 0, 0, 0, 0, 0, 0] = ![0, 0, 0, 0, 0, 0, 0, 0] ∧
    cfgMb *ᵥ ![0, 0, 0, 0, 0, 0, 0, 0] + ![0, 0, 0, 0, 0, 0, 0, 0] = ![0, 0, 0, 0, 0, 0, 0, 0] := by
  decide +kernel

theorem cfgM_wit1 : cfgMa *ᵥ ![0, 0, 0, 0, 1, 0, 0, 1] = ![0, 0, 0, 0, 1, 0, 0, 1] ∧
    cfgMb *ᵥ ![0, 0, 0, 0, 1, 0, 0, 1] + ![0, 0, 0, 0, 1, 0, 0, 1] = ![0, 0, 1, 1, 1, 0, 0, 1] := by
  decide +kernel

theorem cfgM_wit2 : cfgMa *ᵥ ![0, 0, 0, 0, 0, 0, 1, 0] = ![0, 0, 0, 0, 0, 0, 1, 0] ∧
    cfgMb *ᵥ ![0, 0, 0, 0, 0, 0, 1, 0] + ![0, 0, 0, 0, 0, 0, 1, 0] = ![0, 1, 0, 1, 1, 0, 1, 0] := by
  decide +kernel

theorem cfgM_wit3 : cfgMa *ᵥ ![0, 0, 0, 0, 1, 0, 1, 1] = ![0, 0, 0, 0, 1, 0, 1, 1] ∧
    cfgMb *ᵥ ![0, 0, 0, 0, 1, 0, 1, 1] + ![0, 0, 0, 0, 1, 0, 1, 1] = ![0, 1, 1, 0, 0, 0, 1, 1] := by
  decide +kernel

theorem rhoA_v : rhoA vA = MxUnit * MfUnit := by
  have hv : vA = (⟨x45, Q45_le_A45 x45_mem_Q⟩ : A45) * ⟨f45, f45_mem_A⟩ :=
    Subtype.ext v_eq_x45_mul_f45
  rw [hv, map_mul, rhoA_x, rhoA_f]

theorem spinFixedCard_v (a : A45) (ha : IsConj a vA) :
    fixCard (((rhoA a : Matrix.GeneralLinearGroup (Fin 8) (ZMod 2)) :
      Matrix (Fin 8) (Fin 8) (ZMod 2))) = 16 := by
  obtain ⟨c, hc⟩ := isConj_iff.mp ha
  have h1 : fixCard (((rhoA vA : Matrix.GeneralLinearGroup (Fin 8) (ZMod 2)) :
      Matrix (Fin 8) (Fin 8) (ZMod 2))) =
      fixCard (((rhoA a : Matrix.GeneralLinearGroup (Fin 8) (ZMod 2)) :
        Matrix (Fin 8) (Fin 8) (ZMod 2))) := by
    rw [← hc, map_mul, map_mul, map_inv]
    exact fixCard_conj (rhoA c) (rhoA a)
  rw [← h1, rhoA_v, Units.val_mul]
  exact fixCard_Mx_mul_Mf

private def cfgXA : A45 := ⟨x45, Q45_le_A45 x45_mem_Q⟩
private def cfgYA : A45 := ⟨y45, Q45_le_A45 y45_mem_Q⟩
private def cfgFA : A45 := ⟨f45, f45_mem_A⟩
private def cfgG2A : A45 := cfgYA * cfgXA * cfgYA * cfgYA * cfgYA * cfgYA

private def cfgCutA : A45 := cfgFA * cfgYA * cfgXA * cfgYA * cfgYA * cfgYA * cfgXA * cfgFA * cfgYA *
  cfgFA * cfgYA * cfgYA
private def cfgCvA : A45 := cfgYA * cfgXA * cfgFA * cfgYA * cfgXA * cfgYA * cfgYA * cfgFA * cfgYA *
  cfgXA * cfgYA * cfgFA * cfgYA

private theorem cfgComm_eq : ⁅cfgFA, cfgG2A⁆ = cfgFA * cfgG2A * cfgFA * cfgG2A := by
  apply Subtype.ext
  show f45 * cfgG2P * f45⁻¹ * cfgG2P⁻¹ = f45 * cfgG2P * f45 * cfgG2P
  rw [cfgP_f_inv, cfgP_g2_inv]

private theorem rhoA_cfgG2A : ((rhoA cfgG2A : GL8) : Matrix (Fin 8) (Fin 8) (ZMod 2)) = cfgMg := by
  simp only [cfgG2A, cfgYA, cfgXA, map_mul, rhoA_x, rhoA_y, Units.val_mul]
  rfl

private theorem rhoA_cfgComm :
    ((rhoA ⁅cfgFA, cfgG2A⁆ : GL8) : Matrix (Fin 8) (Fin 8) (ZMod 2)) = cfgMb := by
  rw [cfgComm_eq, map_mul, map_mul, map_mul, Units.val_mul, Units.val_mul, Units.val_mul,
    rhoA_cfgG2A]
  have hf : ((rhoA cfgFA : GL8) : Matrix (Fin 8) (Fin 8) (ZMod 2)) = Mf := by
    simp only [cfgFA, rhoA_f]
    rfl
  rw [hf]
  rfl

private theorem rhoA_uv_coe :
    ((rhoA ((uA : A45) * vA) : GL8) : Matrix (Fin 8) (Fin 8) (ZMod 2)) = cfgMa := by
  rw [rhoA_u_mul_v, Units.val_mul, Units.val_mul, coe_evalW_genUnit]
  rfl

theorem uv_mul_self_A : (uA * vA) * (uA * vA) = 1 := by
  apply Subtype.ext
  exact cfgP_uv_sq

theorem exists_spinConfig :
    ∃ g₁ g₂ : A45,
      (uA * vA) * g₁ = g₁ * (uA * vA) ∧ (uA * vA) * g₂ = g₂ * (uA * vA) ∧
      ⁅g₁, g₂⁆ * ⁅g₁, g₂⁆ = 1 ∧ IsConj ⁅g₁, g₂⁆ (uA * tA) ∧ IsConj (uA * vA * ⁅g₁, g₂⁆) vA ∧
      (∀ w : V, ((rhoA (uA * vA) : GL8) : Matrix (Fin 8) (Fin 8) (ZMod 2)) *ᵥ w = w → q w = 0) ∧
      (∀ w : V, ((rhoA (uA * vA) : GL8) : Matrix (Fin 8) (Fin 8) (ZMod 2)) *ᵥ w = w →
        ((rhoA ⁅g₁, g₂⁆ : GL8) : Matrix (Fin 8) (Fin 8) (ZMod 2)) *ᵥ w = w →
        ∃ w' : V, ((rhoA (uA * vA) : GL8) : Matrix (Fin 8) (Fin 8) (ZMod 2)) *ᵥ w' = w' ∧
          ((rhoA ⁅g₁, g₂⁆ : GL8) : Matrix (Fin 8) (Fin 8) (ZMod 2)) *ᵥ w' + w' = w) := by
  refine ⟨cfgFA, cfgG2A, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · apply Subtype.ext
    exact cfgP_comm1
  · apply Subtype.ext
    exact cfgP_comm2
  · apply Subtype.ext
    exact cfgP_b_sq
  · refine isConj_iff.mpr ⟨cfgCutA, ?_⟩
    apply Subtype.ext
    show cfgCutP * cfgBP * cfgCutP⁻¹ = u * x45
    exact cfgP_conj1
  · refine isConj_iff.mpr ⟨cfgCvA, ?_⟩
    apply Subtype.ext
    show cfgCvP * (u * v * cfgBP) * cfgCvP⁻¹ = v
    exact cfgP_conj2
  · rw [rhoA_uv_coe]
    exact cfgM_q
  · rw [rhoA_uv_coe, rhoA_cfgComm]
    intro w hwa hwb
    rcases cfgM_inter w hwa hwb with rfl | rfl | rfl | rfl
    · exact ⟨_, cfgM_wit0.1, cfgM_wit0.2⟩
    · exact ⟨_, cfgM_wit1.1, cfgM_wit1.2⟩
    · exact ⟨_, cfgM_wit2.1, cfgM_wit2.2⟩
    · exact ⟨_, cfgM_wit3.1, cfgM_wit3.2⟩

end CFSG.RankThree.GF2n.Parrott

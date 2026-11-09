module

public import CFSG.Permutation.FinPackSignCount
public import CFSG.Permutation.FinPackInv
public import CFSG.Permutation.FinPackVec

public section

namespace CFSG.Quasithin.H13.A7SignCountK

open Equiv Equiv.Perm Finset CFSG.Permutation.FinPack

@[expose] noncomputable def fix6B (c : ℕ) : Bool := Nat.beq (rd c 6) 6

@[expose] noncomputable def fix56B (c : ℕ) : Bool := Nat.beq (rd c 5) 5 && Nat.beq (rd c 6) 6

theorem check_fix6 : Nat.beq (cntK 7 (fun c => fix6B c && evenK 7 c) 7 0 0 0) 360 = true := by
  decide +kernel

theorem check_fix56 : Nat.beq (cntK 7 (fun c => fix56B c && evenK 7 c) 7 0 0 0) 60 = true := by
  decide +kernel

theorem fix6B_iff (σ : Perm (Fin 7)) : fix6B (enc σ) = true ↔ σ 6 = 6 := by
  have h6 : rd (enc σ) 6 = σ 6 := rd_enc (by norm_num) σ 6
  simp only [fix6B, h6, Nat.beq_eq, Fin.ext_iff] <;> exact Iff.rfl

theorem fix56B_iff (σ : Perm (Fin 7)) : fix56B (enc σ) = true ↔ σ 5 = 5 ∧ σ 6 = 6 := by
  have h5 : rd (enc σ) 5 = σ 5 := rd_enc (by norm_num) σ 5
  have h6 : rd (enc σ) 6 = σ 6 := rd_enc (by norm_num) σ 6
  simp only [fix56B, h5, h6, Bool.and_eq_true, Nat.beq_eq, Fin.ext_iff] <;> exact Iff.rfl

theorem card_sign_fix6 : (Finset.univ.filter fun σ : Perm (Fin 7) =>
    sign σ = 1 ∧ σ 6 = 6).card = 360 := by
  have e : (Finset.univ.filter fun σ : Perm (Fin 7) => sign σ = 1 ∧ σ 6 = 6) =
      Finset.univ.filter fun σ : Perm (Fin 7) => sign σ = 1 ∧ fix6B (enc σ) = true :=
    Finset.filter_congr fun σ _ => and_congr_right' (fix6B_iff σ).symm
  rw [e, card_sign_filter_eq_cntK (n := 7) (by norm_num) fix6B]
  exact Nat.eq_of_beq_eq_true check_fix6

theorem card_sign_fix56 : (Finset.univ.filter fun σ : Perm (Fin 7) =>
    sign σ = 1 ∧ σ 5 = 5 ∧ σ 6 = 6).card = 60 := by
  have e : (Finset.univ.filter fun σ : Perm (Fin 7) => sign σ = 1 ∧ σ 5 = 5 ∧ σ 6 = 6) =
      Finset.univ.filter fun σ : Perm (Fin 7) => sign σ = 1 ∧ fix56B (enc σ) = true :=
    Finset.filter_congr fun σ _ => and_congr_right' (fix56B_iff σ).symm
  rw [e, card_sign_filter_eq_cntK (n := 7) (by norm_num) fix56B]
  exact Nat.eq_of_beq_eq_true check_fix56

@[expose] noncomputable def stabVB (v c : ℕ) : Bool := Nat.beq (mulK 7 v (invCK 7 c)) v

theorem stabVB_iff (v : Fin 7 → ZMod 2) (σ : Perm (Fin 7)) :
    stabVB (vcode v) (enc σ) = true ↔ (fun i => v (σ⁻¹ i)) = v := by
  rw [stabVB, Nat.beq_eq, vcode_eq_iff, vcode_comp (by norm_num), enc_inv_invCK (by norm_num)]

theorem check_stabV4 :
    Nat.beq (cntK 7 (fun c => stabVB 1118464 c && evenK 7 c) 7 0 0 0) 72 = true := by
  decide +kernel

theorem card_sign_stabV4 (v : Fin 7 → ZMod 2) (hv : vcode v = 1118464) :
    (Finset.univ.filter fun σ : Perm (Fin 7) =>
      sign σ = 1 ∧ (fun i => v (σ⁻¹ i)) = v).card = 72 := by
  have e : (Finset.univ.filter fun σ : Perm (Fin 7) => sign σ = 1 ∧ (fun i => v (σ⁻¹ i)) = v) =
      Finset.univ.filter fun σ : Perm (Fin 7) => sign σ = 1 ∧ stabVB 1118464 (enc σ) = true :=
    Finset.filter_congr fun σ _ => and_congr_right' (by rw [← hv, stabVB_iff])
  rw [e, card_sign_filter_eq_cntK (n := 7) (by norm_num) (stabVB 1118464)]
  exact Nat.eq_of_beq_eq_true check_stabV4

end CFSG.Quasithin.H13.A7SignCountK

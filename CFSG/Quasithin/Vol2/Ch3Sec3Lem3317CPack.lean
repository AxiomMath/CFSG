module

public import CFSG.Permutation.FinPackComm
public import CFSG.Permutation.FinPackSignCount

public section

namespace CFSG.Quasithin.H13.L3317Pack

open Equiv Equiv.Perm Finset CFSG.Permutation.FinPack

@[expose] noncomputable def stabB (c : ℕ) : Bool :=
  (Nat.beq (rd c 5) 5 && Nat.beq (rd c 6) 6) || (Nat.beq (rd c 5) 6 && Nat.beq (rd c 6) 5)

theorem check_stab : Nat.beq (cntK 7 (fun c => stabB c && evenK 7 c) 7 0 0 0) 120 = true := by
  decide +kernel

theorem stabB_iff (σ : Perm (Fin 7)) :
    stabB (enc σ) = true ↔ ((σ 5 = 5 ∧ σ 6 = 6) ∨ (σ 5 = 6 ∧ σ 6 = 5)) := by
  have h5 : rd (enc σ) 5 = σ 5 := rd_enc (by norm_num) σ 5
  have h6 : rd (enc σ) 6 = σ 6 := rd_enc (by norm_num) σ 6
  simp only [stabB, h5, h6, Bool.or_eq_true, Bool.and_eq_true, Nat.beq_eq, Fin.ext_iff] <;>
    exact Iff.rfl

theorem card_stabFS_pack : (Finset.univ.filter fun σ : Perm (Fin 7) =>
    sign σ = 1 ∧ ((σ 5 = 5 ∧ σ 6 = 6) ∨ (σ 5 = 6 ∧ σ 6 = 5))).card = 120 := by
  have e : (Finset.univ.filter fun σ : Perm (Fin 7) =>
      sign σ = 1 ∧ ((σ 5 = 5 ∧ σ 6 = 6) ∨ (σ 5 = 6 ∧ σ 6 = 5))) =
      Finset.univ.filter fun σ : Perm (Fin 7) => sign σ = 1 ∧ stabB (enc σ) = true :=
    Finset.filter_congr fun σ _ => and_congr_right' (stabB_iff σ).symm
  rw [e, card_sign_filter_eq_cntK (n := 7) (by norm_num) stabB]
  exact Nat.eq_of_beq_eq_true check_stab

@[expose] noncomputable def centB (a b c : ℕ) : Bool :=
  commLaneK 7 c a && commLaneK 7 c b && !(Nat.beq c 106181136)

theorem check_cent :
    Nat.beq (cntK 7 (fun c => centB 106180641 105923361 c && evenK 7 c) 7 0 0 0) 0 = true := by
  decide +kernel

theorem enc_one7 : enc (1 : Perm (Fin 7)) = 106181136 := by decide +kernel

theorem enc_c012 : enc (swap 0 2 * swap 0 1 : Perm (Fin 7)) = 106180641 := by decide +kernel

theorem enc_c01234 : enc (swap 0 4 * swap 0 3 * swap 0 2 * swap 0 1 : Perm (Fin 7)) = 105923361 := by
  decide +kernel

theorem eq_one_of_commute_pack (x y : Perm (Fin 7)) (hx : enc x = 106180641)
    (hy : enc y = 105923361) (σ : Perm (Fin 7)) (hs : sign σ = 1) (h1 : σ * x = x * σ)
    (h2 : σ * y = y * σ) : σ = 1 := by
  by_contra hne
  have hc : centB 106180641 105923361 (enc σ) = true := by
    have hb : Nat.beq (enc σ) 106181136 = false := by
      rw [← enc_one7]
      exact beq_enc_false (by norm_num) hne
    rw [← hx, ← hy, centB, (commLaneK_iff (by norm_num) σ x).2 h1,
      (commLaneK_iff (by norm_num) σ y).2 h2, hb]
    rfl
  have h0 := Nat.eq_of_beq_eq_true check_cent
  rw [← card_sign_filter_eq_cntK (n := 7) (by norm_num) (centB 106180641 105923361),
    Finset.card_eq_zero] at h0
  have hm : σ ∈ (Finset.univ.filter fun τ : Perm (Fin 7) =>
      Perm.sign τ = 1 ∧ centB 106180641 105923361 (enc τ) = true) :=
    Finset.mem_filter.2 ⟨Finset.mem_univ _, hs, hc⟩
  rw [h0] at hm
  exact Finset.notMem_empty _ hm

end CFSG.Quasithin.H13.L3317Pack

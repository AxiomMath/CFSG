module

public import CFSG.Quasithin.H13.A6S1372L76EK
public import CFSG.Quasithin.H13.A6S13834FK
public import CFSG.Permutation.FinPackWalk

public section

namespace CFSG.Quasithin.H13.U3.S6OutK

open Equiv CFSG.Permutation.FinPack CFSG.Quasithin.H13.A6 CFSG.Quasithin.H13.A6.A6L76EK
  CFSG.Quasithin.H13.A6K

@[expose] noncomputable def cntL (f : ℕ → Bool) (L : List ℕ) : ℕ :=
  List.rec (motive := fun _ => ℕ) 0
    (fun a _ r => Bool.rec (motive := fun _ => ℕ) r (Nat.succ r) (f a)) L

theorem cntL_eq (f : ℕ → Bool) (L : List ℕ) : cntL f L = (L.filter f).length := by
  induction L with
  | nil => rfl
  | cons a L ih =>
    change Bool.rec (motive := fun _ => ℕ) (cntL f L) (Nat.succ (cntL f L)) (f a) = _
    rw [List.filter_cons]
    cases f a
    · exact ih
    · rw [if_pos rfl, List.length_cons, ← ih]

@[expose] def W4Q : List ℕ :=
  [0, 69632, 65792, 4352, 65552, 4112, 272, 69904, 65537, 4097, 257, 69889, 17, 69649, 65809, 4369]

@[expose] noncomputable def fixK (C : List ℕ) : ℕ :=
  cntL (fun w => allK (fun c => Nat.beq (nrmK (mulK 6 w c)) w) C) W4Q

theorem fix_bridge {L : List (Perm (Fin 6))} (hL : ∀ s ∈ L, s * s = 1) {W : List P6}
    (hW : (W.map vc6 == W4Q) = true) :
    (W.filter fun x => decide (∀ s ∈ L, act4f s x = x)).length = fixK (L.map enc) := by
  rw [beq_iff_eq] at hW
  unfold fixK
  rw [cntL_eq, ← hW, List.filter_map, List.length_map]
  refine congrArg List.length (List.filter_congr fun x _ => ?_)
  rw [Function.comp_apply]
  refine Bool.eq_iff_iff.2 ?_
  rw [decide_eq_true_iff, allK_iff]
  simp only [List.mem_map, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
  refine forall₂_congr fun s hs => ?_
  have hinv : s⁻¹ = s := inv_eq_of_mul_eq_one_right (hL s hs)
  rw [← vc6_act_inv, hinv, beq_vc6_iff]

@[expose] def pk (a b : ℕ) : ℕ := Nat.add a (Nat.shiftLeft b 24)

@[expose] def lo (p : ℕ) : ℕ := Nat.land p 16777215

@[expose] def hi (p : ℕ) : ℕ := Nat.shiftRight p 24

theorem lo_pk {a : ℕ} (b : ℕ) (ha : a < 2 ^ 24) : lo (pk a b) = a := by
  have h : (16777215 : ℕ) = 2 ^ 24 - 1 := by norm_num
  unfold lo pk
  change (a + b <<< 24) &&& 16777215 = a
  rw [h, Nat.and_two_pow_sub_one_eq_mod, Nat.shiftLeft_eq, Nat.add_mul_mod_self_right,
    Nat.mod_eq_of_lt ha]

theorem hi_pk {a : ℕ} (b : ℕ) (ha : a < 2 ^ 24) : hi (pk a b) = b := by
  unfold hi pk
  change (a + b <<< 24) >>> 24 = b
  rw [Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq, Nat.add_mul_div_right _ _ (by norm_num),
    Nat.div_eq_of_lt ha, zero_add]

theorem enc_lt (σ : Perm (Fin 6)) : enc σ < 2 ^ 24 := by
  unfold enc
  refine lt_of_lt_of_eq (encF_lt fun i hi => ?_) (by norm_num)
  rw [dif_pos hi]
  exact lt_of_lt_of_le (Fin.isLt _) (by norm_num)

@[expose] def DTC : List ℕ :=
  [92573999051280, 76016647483920, 75935866168080, 92363863434000, 75871190004225, 92428539605505,
    92509322879745, 76081323647745, 76016900116530, 92573746401330, 92428288917810, 75871440666930,
    92364116070435, 75935613521955, 76081072963875, 92509573546275]

theorem mem_DTC {k : ℕ} (hk : k < 16) : DTC.getD k 0 ∈ DTC := by
  have hl : DTC.length = 16 := rfl
  have hk' : k < DTC.length := by rw [hl]; exact hk
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk', Option.getD_some]
  exact List.getElem_mem hk'

theorem sq_beq {σ : Perm (Fin 6)} (h : σ * σ = 1) : Nat.beq (mulK 6 (enc σ) (enc σ)) EC = true := by
  rw [← enc_mul h16, h, enc_one6, Nat.beq_refl]

theorem sq_of_beq {σ : Perm (Fin 6)} (h : Nat.beq (mulK 6 (enc σ) (enc σ)) EC = true) :
    σ * σ = 1 := by
  rw [← enc_mul h16, ← enc_one6] at h
  exact (beq_enc_iff h16).1 h

@[expose] noncomputable def f1 (a c : ℕ) : Bool :=
  !(Nat.beq (mulK 6 a a) EC && !Nat.beq a EC) ||
    (Nat.beq (mulK 6 c c) EC && Nat.ble (Nat.mul (fixK [a]) (fixK [c])) 32)

@[expose] noncomputable def fix1B : Bool := allK (fun p => f1 (lo p) (hi p)) DTC

theorem fix1B_check : fix1B = true := by decide +kernel

theorem fix1_of {d t : Fin 16 → Perm (Fin 6)} {W : List P6} (hW : (W.map vc6 == W4Q) = true)
    (hp : ∀ i : Fin 16, DTC.getD i 0 = pk (enc (d i)) (enc (t i))) (i : Fin 16)
    (h1 : d i * d i = 1) (h2 : d i ≠ 1) :
    (W.filter fun x => decide (∀ s ∈ [d i], act4f s x = x)).length *
      (W.filter fun x => decide (∀ s ∈ [t i], act4f s x = x)).length ≤ 32 := by
  have hm := allK_iff.1 fix1B_check _ (mem_DTC i.isLt)
  rw [hp i, lo_pk _ (enc_lt _), hi_pk _ (enc_lt _), f1, sq_beq h1,
    beq_one_false h16 enc_one6 h2] at hm
  simp only [Bool.not_false, Bool.and_true, Bool.true_and, Bool.not_true, Bool.false_or, Bool.and_eq_true] at hm
  have ht := sq_of_beq hm.1
  rw [fix_bridge (by simpa using h1) hW, fix_bridge (by simpa using ht) hW]
  exact Nat.le_of_ble_eq_true hm.2

@[expose] noncomputable def f2 (a b c e : ℕ) : Bool :=
  !(Nat.beq (mulK 6 a a) EC && !Nat.beq a EC && Nat.beq (mulK 6 b b) EC && !Nat.beq b EC &&
      !Nat.beq a b && Nat.beq (mulK 6 a b) (mulK 6 b a)) ||
    (Nat.beq (mulK 6 c c) EC && Nat.beq (mulK 6 e e) EC &&
      Nat.ble (Nat.mul (fixK [a, b]) (fixK [c, e])) 16)

@[expose] noncomputable def fix2B : Bool :=
  allK (fun p => allK (fun q => f2 (lo p) (lo q) (hi p) (hi q)) DTC) DTC

theorem fix2B_check : fix2B = true := by decide +kernel

theorem fix2_of {d t : Fin 16 → Perm (Fin 6)} {W : List P6} (hW : (W.map vc6 == W4Q) = true)
    (hp : ∀ i : Fin 16, DTC.getD i 0 = pk (enc (d i)) (enc (t i))) (i j : Fin 16)
    (h1 : d i * d i = 1) (h2 : d i ≠ 1) (h3 : d j * d j = 1) (h4 : d j ≠ 1) (h5 : d i ≠ d j)
    (h6 : d i * d j = d j * d i) :
    (W.filter fun x => decide (∀ s ∈ [d i, d j], act4f s x = x)).length *
      (W.filter fun x => decide (∀ s ∈ [t i, t j], act4f s x = x)).length ≤ 16 := by
  have hm := allK_iff.1 (allK_iff.1 fix2B_check _ (mem_DTC i.isLt)) _ (mem_DTC j.isLt)
  rw [hp i, hp j, lo_pk _ (enc_lt _), hi_pk _ (enc_lt _), lo_pk _ (enc_lt _), hi_pk _ (enc_lt _),
    f2, sq_beq h1, sq_beq h3, beq_one_false h16 enc_one6 h2, beq_one_false h16 enc_one6 h4,
    beq_enc_false h16 h5, (comm_enc_iff h16).2 h6] at hm
  simp only [Bool.not_false, Bool.and_true, Bool.true_and, Bool.not_true, Bool.false_or, Bool.and_eq_true] at hm
  have hti := sq_of_beq hm.1.1
  have htj := sq_of_beq hm.1.2
  have hdl : ∀ s ∈ [d i, d j], s * s = 1 := by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro s (rfl | rfl)
    · exact h1
    · exact h3
  have htl : ∀ s ∈ [t i, t j], s * s = 1 := by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro s (rfl | rfl)
    · exact hti
    · exact htj
  rw [fix_bridge hdl hW, fix_bridge htl hW]
  exact Nat.le_of_ble_eq_true hm.2

end CFSG.Quasithin.H13.U3.S6OutK

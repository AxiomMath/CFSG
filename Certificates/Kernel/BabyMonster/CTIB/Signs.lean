module

public import Certificates.Kernel.BabyMonster.Pair.Max2B
public import Certificates.Kernel.BabyMonster.CTIB.Fourteen
public import CFSG.Certificates.Kernel.BabyMonster.MaskSound
public import CFSG.Certificates.Kernel.BabyMonster.CTIBRows.All
public import CFSG.Certificates.Kernel.BabyMonster.CTIBRows.Check0
public import CFSG.Certificates.Kernel.BabyMonster.CTIBRows.Check1
public import CFSG.Certificates.Kernel.BabyMonster.CTIBRows.Check10
public import CFSG.Certificates.Kernel.BabyMonster.CTIBRows.Check11
public import CFSG.Certificates.Kernel.BabyMonster.CTIBRows.Check12
public import CFSG.Certificates.Kernel.BabyMonster.CTIBRows.Check13
public import CFSG.Certificates.Kernel.BabyMonster.CTIBRows.Check14
public import CFSG.Certificates.Kernel.BabyMonster.CTIBRows.Check15
public import CFSG.Certificates.Kernel.BabyMonster.CTIBRows.Check16
public import CFSG.Certificates.Kernel.BabyMonster.CTIBRows.Check17
public import CFSG.Certificates.Kernel.BabyMonster.CTIBRows.Check18
public import CFSG.Certificates.Kernel.BabyMonster.CTIBRows.Check19
public import CFSG.Certificates.Kernel.BabyMonster.CTIBRows.Check2
public import CFSG.Certificates.Kernel.BabyMonster.CTIBRows.Check20
public import CFSG.Certificates.Kernel.BabyMonster.CTIBRows.Check21
public import CFSG.Certificates.Kernel.BabyMonster.CTIBRows.Check22
public import CFSG.Certificates.Kernel.BabyMonster.CTIBRows.Check23
public import CFSG.Certificates.Kernel.BabyMonster.CTIBRows.Check24
public import CFSG.Certificates.Kernel.BabyMonster.CTIBRows.Check25
public import CFSG.Certificates.Kernel.BabyMonster.CTIBRows.Check26
public import CFSG.Certificates.Kernel.BabyMonster.CTIBRows.Check27
public import CFSG.Certificates.Kernel.BabyMonster.CTIBRows.Check28
public import CFSG.Certificates.Kernel.BabyMonster.CTIBRows.Check29
public import CFSG.Certificates.Kernel.BabyMonster.CTIBRows.Check3
public import CFSG.Certificates.Kernel.BabyMonster.CTIBRows.Check30
public import CFSG.Certificates.Kernel.BabyMonster.CTIBRows.Check31
public import CFSG.Certificates.Kernel.BabyMonster.CTIBRows.Check32
public import CFSG.Certificates.Kernel.BabyMonster.CTIBRows.Check33
public import CFSG.Certificates.Kernel.BabyMonster.CTIBRows.Check34
public import CFSG.Certificates.Kernel.BabyMonster.CTIBRows.Check35
public import CFSG.Certificates.Kernel.BabyMonster.CTIBRows.Check36
public import CFSG.Certificates.Kernel.BabyMonster.CTIBRows.Check37
public import CFSG.Certificates.Kernel.BabyMonster.CTIBRows.Check38
public import CFSG.Certificates.Kernel.BabyMonster.CTIBRows.Check39
public import CFSG.Certificates.Kernel.BabyMonster.CTIBRows.Check4
public import CFSG.Certificates.Kernel.BabyMonster.CTIBRows.Check40
public import CFSG.Certificates.Kernel.BabyMonster.CTIBRows.Check41
public import CFSG.Certificates.Kernel.BabyMonster.CTIBRows.Check42
public import CFSG.Certificates.Kernel.BabyMonster.CTIBRows.Check43
public import CFSG.Certificates.Kernel.BabyMonster.CTIBRows.Check44
public import CFSG.Certificates.Kernel.BabyMonster.CTIBRows.Check45
public import CFSG.Certificates.Kernel.BabyMonster.CTIBRows.Check46
public import CFSG.Certificates.Kernel.BabyMonster.CTIBRows.Check47
public import CFSG.Certificates.Kernel.BabyMonster.CTIBRows.Check48
public import CFSG.Certificates.Kernel.BabyMonster.CTIBRows.Check49
public import CFSG.Certificates.Kernel.BabyMonster.CTIBRows.Check5
public import CFSG.Certificates.Kernel.BabyMonster.CTIBRows.Check50
public import CFSG.Certificates.Kernel.BabyMonster.CTIBRows.Check51
public import CFSG.Certificates.Kernel.BabyMonster.CTIBRows.Check6
public import CFSG.Certificates.Kernel.BabyMonster.CTIBRows.Check7
public import CFSG.Certificates.Kernel.BabyMonster.CTIBRows.Check8
public import CFSG.Certificates.Kernel.BabyMonster.CTIBRows.Check9

public section

namespace CertificateChecks.KernelBM.CTIB

open CFSG.KC.BM CFSG.Monster.B.Dyadic CertificateChecks.KernelBM.Pair CFSG.Monster.B.CTIB.Native
open scoped Matrix

local notation "MatB" => Matrix (Fin 4370) (Fin 4370) (ZMod 2)

set_option maxRecDepth 100000
set_option exponentiation.threshold 8192

@[expose] noncomputable def SG0l : List Nat :=
  [CTIBRows.S0, CTIBRows.S1, CTIBRows.S2, CTIBRows.S3, CTIBRows.S4, CTIBRows.S5, CTIBRows.S6,
    CTIBRows.S7, CTIBRows.S8, CTIBRows.S9, CTIBRows.S10, CTIBRows.S11, CTIBRows.S12,
    CTIBRows.S13, CTIBRows.S14, CTIBRows.S15, CTIBRows.S16, CTIBRows.S17, CTIBRows.S18,
    CTIBRows.S19, CTIBRows.S20, CTIBRows.S21]

@[expose] noncomputable def SG1l : List Nat :=
  [CTIBRows.S22, CTIBRows.S23, CTIBRows.S24, CTIBRows.S25, CTIBRows.S26, CTIBRows.S27,
    CTIBRows.S28, CTIBRows.S29, CTIBRows.S30, CTIBRows.S31, CTIBRows.S32, CTIBRows.S33,
    CTIBRows.S34, CTIBRows.S35, CTIBRows.S36, CTIBRows.S37, CTIBRows.S38, CTIBRows.S39,
    CTIBRows.S40, CTIBRows.S41, CTIBRows.S42, CTIBRows.S43]

@[expose] noncomputable def start0 : Nat := Nat.lor 483226 (Nat.mul (spreadRow Max2.vx) 3711077)

@[expose] noncomputable def start1 : Nat := Nat.lor 1178687 (Nat.mul (spreadRow Max2.vx) 3015616)

@[expose] noncomputable def prevSG (st : Nat) (L : List Nat) (s : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) st (fun k _ => L.getD k 0) s

@[expose] def maskOf (rows : List ℕ) (s : ℕ) : ℕ :=
  ((List.range 22).map fun i => if (rows.getD i 0).testBit s then 2 ^ i else 0).sum

@[expose] def SGOK (st : Nat) (L : List Nat) (rows : List ℕ) (s : Nat) : Prop :=
  Nat.beq (Nat.lor (Nat.sub (prevSG st L s) (Nat.land (prevSG st L s) (Nat.mul SM (maskOf rows s))))
    (mulS (Elist.getD s []) (Nat.land (prevSG st L s) (Nat.mul SM (maskOf rows s)))))
    (L.getD s 0) = true

theorem sgOK_of {st : Nat} {L : List Nat} {rows : List ℕ} {s : Nat} {M : List Nat} {P R m : Nat}
    (h : Nat.beq (Nat.lor (Nat.sub P (Nat.land P (Nat.mul SM m)))
      (mulS M (Nat.land P (Nat.mul SM m)))) R = true)
    (hM : M = Elist.getD s []) (hP : P = prevSG st L s) (hm : m = maskOf rows s)
    (hR : R = L.getD s 0) : SGOK st L rows s := by
  unfold SGOK
  rw [← hM, ← hP, ← hm, ← hR]
  exact h

theorem sg0_of (s : ℕ) {M : List Nat} {P R m : Nat}
    (h : Nat.beq (Nat.lor (Nat.sub P (Nat.land P (Nat.mul SM m)))
      (mulS M (Nat.land P (Nat.mul SM m)))) R = true)
    (hM : M = Elist.getD s []) (hP : P = prevSG start0 SG0l s)
    (hm : m = maskOf CFSG.Monster.B.Bin.quotRows1 s) (hR : R = SG0l.getD s 0) :
    SGOK start0 SG0l CFSG.Monster.B.Bin.quotRows1 s := sgOK_of h hM hP hm hR

theorem sg1_of (s : ℕ) {M : List Nat} {P R m : Nat}
    (h : Nat.beq (Nat.lor (Nat.sub P (Nat.land P (Nat.mul SM m)))
      (mulS M (Nat.land P (Nat.mul SM m)))) R = true)
    (hM : M = Elist.getD s []) (hP : P = prevSG start1 SG1l s)
    (hm : m = maskOf CFSG.Monster.B.Bin.quotRows2 s) (hR : R = SG1l.getD s 0) :
    SGOK start1 SG1l CFSG.Monster.B.Bin.quotRows2 s := sgOK_of h hM hP hm hR

theorem sg0_all : ∀ s < 22, SGOK start0 SG0l CFSG.Monster.B.Bin.quotRows1 s := by
  forall_lt_bind CFSG.KC.BM.CTIBRows.sg0_ 22 sg0_of

theorem sg1_all : ∀ s < 22, SGOK start1 SG1l CFSG.Monster.B.Bin.quotRows2 s := by
  forall_lt_bind CFSG.KC.BM.CTIBRows.sg1_ 22 sg1_of

theorem maskOf_lt1 : ∀ s < 22, maskOf CFSG.Monster.B.Bin.quotRows1 s < 2 ^ 64 := by decide +kernel

theorem maskOf_lt2 : ∀ s < 22, maskOf CFSG.Monster.B.Bin.quotRows2 s < 2 ^ 64 := by decide +kernel

theorem maskOf_bit1 : ∀ s < 22, ∀ t < 22, (maskOf CFSG.Monster.B.Bin.quotRows1 s).testBit t =
    (CFSG.Monster.B.Bin.quotRows1.getD t 0).testBit s := by decide +kernel

theorem maskOf_bit2 : ∀ s < 22, ∀ t < 22, (maskOf CFSG.Monster.B.Bin.quotRows2 s).testBit t =
    (CFSG.Monster.B.Bin.quotRows2.getD t 0).testBit s := by decide +kernel

@[expose] noncomputable def rowAcc (v : Fin 4370 → ZMod 2) (r : ℕ) : ℕ → (Fin 4370 → ZMod 2)
  | 0 => v
  | s + 1 => rowAcc v r s ᵥ* (if r.testBit s then EK s else 1)

theorem vecN_vx : Max2.vx < 2 ^ 4370 ∧ vecN Max2.vx = e0 ᵥ* XK := by
  obtain ⟨h1, -⟩ := Dy.andB_true Max2.vxdef
  have hb : AllBlocks Max2.Xb.rows Max2.Xb 0 := by bm_blocks CFSG.KC.BM.Max2.rows_Xb 69
  have h1lt : (1 : ℕ) < 2 ^ 4370 := Nat.one_lt_two_pow (by norm_num)
  obtain ⟨hlt, heq⟩ := vecMul_strip hb Max2.wf_Xb h1lt
  rw [Nat.eq_of_beq_eq_true h1] at hlt heq
  exact ⟨hlt, by rw [heq, vecN_one]; rfl⟩

section Chain

variable {st : Nat} {L : List Nat} {rows : List ℕ} {sg : ℕ}
  (hok : ∀ s < 22, SGOK st L rows s)
  (hlt : ∀ s < 22, maskOf rows s < 2 ^ 64)
  (hbit : ∀ s < 22, ∀ t < 22, (maskOf rows s).testBit t = (rows.getD t 0).testBit s)
  (hst : ∀ t < 22, vrow (rowOf st t) = if sg.testBit t then e0 ᵥ* XK else e0)

include hok hlt hbit hst in
theorem rows_SG : ∀ s < 22, ∀ t < 22, vrow (rowOf (L.getD s 0) t) =
    rowAcc (if sg.testBit t then e0 ᵥ* XK else e0) (rows.getD t 0) (s + 1)
  | 0, hs, t, ht => by
    have h := hok 0 hs
    unfold SGOK at h
    rw [← Nat.eq_of_beq_eq_true h, maskUpd_rows (wfE 0 hs) _ _ (hlt 0 hs) (by omega)]
    have hp : prevSG st L 0 = st := rfl
    rw [hp, hst t ht, hbit 0 hs t ht, rowAcc, rowAcc]
    by_cases hb : (rows.getD t 0).testBit 0
    · rw [ite_eq_left hb, ite_eq_left hb]
      rfl
    · rw [ite_eq_right hb, ite_eq_right hb, Matrix.vecMul_one]
  | s + 1, hs, t, ht => by
    have h := hok (s + 1) hs
    unfold SGOK at h
    rw [← Nat.eq_of_beq_eq_true h, maskUpd_rows (wfE (s + 1) hs) _ _ (hlt (s + 1) hs)
      (by omega)]
    have hp : prevSG st L (s + 1) = L.getD s 0 := rfl
    rw [hp, rows_SG s (by omega) t ht, hbit (s + 1) hs t ht,
      rowAcc.eq_2 _ _ (s + 1)]
    by_cases hb : (rows.getD t 0).testBit (s + 1)
    · rw [ite_eq_left hb, ite_eq_left hb]
      rfl
    · rw [ite_eq_right hb, ite_eq_right hb, Matrix.vecMul_one]

end Chain

theorem prodK_append (l₁ l₂ : List MatB) : prodK (l₁ ++ l₂) = prodK l₁ * prodK l₂ := by
  induction l₁ with
  | nil => rw [List.nil_append, prodK, Matrix.one_mul]
  | cons M l ih => rw [List.cons_append, prodK, prodK, ih, Matrix.mul_assoc]

theorem vecMul_prodK_range (v : Fin 4370 → ZMod 2) (r : ℕ) : ∀ n, v ᵥ*
    prodK ((List.range n).map fun j => if r.testBit j then EK j else 1) = rowAcc v r n
  | 0 => by rw [List.range_zero, List.map_nil, prodK, Matrix.vecMul_one, rowAcc]
  | n + 1 => by
    rw [List.range_succ, List.map_append, prodK_append, ← Matrix.vecMul_vecMul,
      vecMul_prodK_range v r n, List.map_cons, List.map_nil, prodK, prodK, Matrix.mul_one,
      rowAcc]

theorem signedImg_bit {rows : List ℕ} {sg t j : ℕ} (hj : j < 22) :
    (signedImg rows sg t).testBit j = (rows.getD t 0).testBit j := by
  rw [signedImg, Nat.testBit_or]
  split_ifs
  · rw [Nat.testBit_two_pow]
    have : ¬ 22 = j := by omega
    simp [this]
  · simp

theorem signedImg_bit22 {rows : List ℕ} {sg t : ℕ} (hr : rows.getD t 0 < 2 ^ 22) :
    (signedImg rows sg t).testBit 22 = sg.testBit t := by
  rw [signedImg, Nat.testBit_or, Nat.testBit_eq_false_of_lt hr, Bool.false_or]
  split_ifs with h
  · rw [Nat.testBit_two_pow_self, h]
  · rw [Nat.zero_testBit, Bool.eq_false_of_ne_true h]

theorem e0_qK {rows : List ℕ} {sg t : ℕ} (hr : rows.getD t 0 < 2 ^ 22) :
    e0 ᵥ* qK (signedImg rows sg t) =
      rowAcc (if sg.testBit t then e0 ᵥ* XK else e0) (rows.getD t 0) 22 := by
  have hl : ((List.range 22).map fun j => if (signedImg rows sg t).testBit j then EK j else 1) =
      (List.range 22).map fun j => if (rows.getD t 0).testBit j then EK j else 1 :=
    List.map_congr_left fun j hj => by rw [signedImg_bit (List.mem_range.1 hj)]
  rw [qK, hl, ← Matrix.vecMul_vecMul, vecMul_prodK_range, signedImg_bit22 hr]
  by_cases h : sg.testBit t
  · rw [ite_eq_left h, ite_eq_left h]
  · rw [ite_eq_right h, ite_eq_right h, Matrix.vecMul_one]

theorem quotRows1_lt : ∀ t < 22, CFSG.Monster.B.Bin.quotRows1.getD t 0 < 2 ^ 22 := by
  decide +kernel

theorem quotRows2_lt : ∀ t < 22, CFSG.Monster.B.Bin.quotRows2.getD t 0 < 2 ^ 22 := by
  decide +kernel

theorem start_bits0 :
    ∀ t < 22, (3711077 : ℕ).testBit t = false → (483226 : ℕ).testBit t = true := by
  decide +kernel

theorem start_bits1 :
    ∀ t < 22, (3015616 : ℕ).testBit t = false → (1178687 : ℕ).testBit t = true := by
  decide +kernel

theorem start_row {m₀ m₁ : ℕ} (hd : Nat.land m₀ m₁ = 0) (h₀ : m₀ < 2 ^ 64) (h₁ : m₁ < 2 ^ 64)
    (hb : ∀ t < 22, m₁.testBit t = false → m₀.testBit t = true) {t : ℕ} (ht : t < 22) :
    vrow (rowOf (Nat.lor m₀ (Nat.mul (spreadRow Max2.vx) m₁)) t) =
      if m₁.testBit t then e0 ᵥ* XK else e0 := by
  rw [start_rows hd h₀ h₁ vecN_vx.1 (by omega), vecN_vx.2]
  by_cases h : m₁.testBit t
  · rw [ite_eq_left h, ite_eq_left h]
  · rw [ite_eq_right h, ite_eq_right h, ite_eq_left (hb t ht (Bool.eq_false_of_ne_true h))]

theorem signs_g0 : ∀ t < 22, e0 ᵥ* (G1K * EK t * G1K) =
    e0 ᵥ* qK (signedImg CFSG.Monster.B.Bin.quotRows1 3711077 t) := by
  intro t ht
  have h := rows_SG (sg := 3711077) sg0_all maskOf_lt1 maskOf_bit1
    (fun t ht => start_row (by decide) (by norm_num) (by norm_num) start_bits0 ht) 21
    (by norm_num) t ht
  have e : SG0l.getD 21 0 = Max2.PP0 := Nat.eq_of_beq_eq_true CTIBRows.sg0
  rw [e, rows_PP Max2.wf_G1 ps0_all pp0_check ht] at h
  rw [e0_qK (quotRows1_lt t ht)]
  exact h

theorem signs_g1 : ∀ t < 22, e0 ᵥ* (Gi2K * EK t * G2K) =
    e0 ᵥ* qK (signedImg CFSG.Monster.B.Bin.quotRows2 3015616 t) := by
  intro t ht
  have h := rows_SG (sg := 3015616) sg1_all maskOf_lt2 maskOf_bit2
    (fun t ht => start_row (by decide) (by norm_num) (by norm_num) start_bits1 ht) 21
    (by norm_num) t ht
  have e : SG1l.getD 21 0 = Max2.PP1 := Nat.eq_of_beq_eq_true CTIBRows.sg1
  rw [e, rows_PP Max2.wf_G2 ps1_all pp1_check ht] at h
  rw [e0_qK (quotRows2_lt t ht)]
  exact h

end CertificateChecks.KernelBM.CTIB

end

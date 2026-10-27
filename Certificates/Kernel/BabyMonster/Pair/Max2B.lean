module

public import Certificates.Kernel.BabyMonster.Pair.Max2A
public import Certificates.Kernel.BabyMonster.ForallBind

public section

namespace CertificateChecks.KernelBM.Pair

open CFSG.KC.BM CFSG.Monster.B.Dyadic
open scoped Matrix

set_option maxRecDepth 100000
set_option exponentiation.threshold 8192

local notation "MatB" => Matrix (Fin 4370) (Fin 4370) (ZMod 2)

@[expose] noncomputable def AJl : List Nat :=
  [Max2.AJ0, Max2.AJ1, Max2.AJ2, Max2.AJ3, Max2.AJ4, Max2.AJ5, Max2.AJ6, Max2.AJ7, Max2.AJ8,
    Max2.AJ9, Max2.AJ10, Max2.AJ11, Max2.AJ12, Max2.AJ13, Max2.AJ14, Max2.AJ15, Max2.AJ16,
    Max2.AJ17, Max2.AJ18, Max2.AJ19, Max2.AJ20, Max2.AJ21]

@[expose] noncomputable def AXJl : List Nat :=
  [Max2.AXJ0, Max2.AXJ1, Max2.AXJ2, Max2.AXJ3, Max2.AXJ4, Max2.AXJ5, Max2.AXJ6, Max2.AXJ7,
    Max2.AXJ8, Max2.AXJ9, Max2.AXJ10, Max2.AXJ11, Max2.AXJ12, Max2.AXJ13, Max2.AXJ14, Max2.AXJ15,
    Max2.AXJ16, Max2.AXJ17, Max2.AXJ18, Max2.AXJ19, Max2.AXJ20, Max2.AXJ21]

@[expose] noncomputable def PS0l : List Nat :=
  [Max2.PS0_0, Max2.PS0_1, Max2.PS0_2, Max2.PS0_3, Max2.PS0_4, Max2.PS0_5, Max2.PS0_6,
    Max2.PS0_7, Max2.PS0_8, Max2.PS0_9, Max2.PS0_10, Max2.PS0_11, Max2.PS0_12, Max2.PS0_13,
    Max2.PS0_14, Max2.PS0_15, Max2.PS0_16, Max2.PS0_17, Max2.PS0_18, Max2.PS0_19, Max2.PS0_20,
    Max2.PS0_21]

@[expose] noncomputable def PS1l : List Nat :=
  [Max2.PS1_0, Max2.PS1_1, Max2.PS1_2, Max2.PS1_3, Max2.PS1_4, Max2.PS1_5, Max2.PS1_6,
    Max2.PS1_7, Max2.PS1_8, Max2.PS1_9, Max2.PS1_10, Max2.PS1_11, Max2.PS1_12, Max2.PS1_13,
    Max2.PS1_14, Max2.PS1_15, Max2.PS1_16, Max2.PS1_17, Max2.PS1_18, Max2.PS1_19, Max2.PS1_20,
    Max2.PS1_21]

@[expose] noncomputable def CJ0l : List Nat :=
  [Max2.CJ0_0, Max2.CJ0_1, Max2.CJ0_2, Max2.CJ0_3, Max2.CJ0_4, Max2.CJ0_5, Max2.CJ0_6,
    Max2.CJ0_7, Max2.CJ0_8, Max2.CJ0_9, Max2.CJ0_10, Max2.CJ0_11, Max2.CJ0_12, Max2.CJ0_13,
    Max2.CJ0_14, Max2.CJ0_15, Max2.CJ0_16, Max2.CJ0_17, Max2.CJ0_18, Max2.CJ0_19, Max2.CJ0_20,
    Max2.CJ0_21]

@[expose] noncomputable def CJ1l : List Nat :=
  [Max2.CJ1_0, Max2.CJ1_1, Max2.CJ1_2, Max2.CJ1_3, Max2.CJ1_4, Max2.CJ1_5, Max2.CJ1_6,
    Max2.CJ1_7, Max2.CJ1_8, Max2.CJ1_9, Max2.CJ1_10, Max2.CJ1_11, Max2.CJ1_12, Max2.CJ1_13,
    Max2.CJ1_14, Max2.CJ1_15, Max2.CJ1_16, Max2.CJ1_17, Max2.CJ1_18, Max2.CJ1_19, Max2.CJ1_20,
    Max2.CJ1_21]

@[expose] noncomputable def DI0l : List Nat :=
  [Max2.DI0_0, Max2.DI0_1, Max2.DI0_2, Max2.DI0_3, Max2.DI0_4, Max2.DI0_5, Max2.DI0_6,
    Max2.DI0_7, Max2.DI0_8, Max2.DI0_9, Max2.DI0_10, Max2.DI0_11, Max2.DI0_12, Max2.DI0_13,
    Max2.DI0_14, Max2.DI0_15, Max2.DI0_16, Max2.DI0_17, Max2.DI0_18, Max2.DI0_19, Max2.DI0_20,
    Max2.DI0_21]

@[expose] noncomputable def DX0l : List Nat :=
  [Max2.DX0_0, Max2.DX0_1, Max2.DX0_2, Max2.DX0_3, Max2.DX0_4, Max2.DX0_5, Max2.DX0_6,
    Max2.DX0_7, Max2.DX0_8, Max2.DX0_9, Max2.DX0_10, Max2.DX0_11, Max2.DX0_12, Max2.DX0_13,
    Max2.DX0_14, Max2.DX0_15, Max2.DX0_16, Max2.DX0_17, Max2.DX0_18, Max2.DX0_19, Max2.DX0_20,
    Max2.DX0_21]

@[expose] noncomputable def DI1l : List Nat :=
  [Max2.DI1_0, Max2.DI1_1, Max2.DI1_2, Max2.DI1_3, Max2.DI1_4, Max2.DI1_5, Max2.DI1_6,
    Max2.DI1_7, Max2.DI1_8, Max2.DI1_9, Max2.DI1_10, Max2.DI1_11, Max2.DI1_12, Max2.DI1_13,
    Max2.DI1_14, Max2.DI1_15, Max2.DI1_16, Max2.DI1_17, Max2.DI1_18, Max2.DI1_19, Max2.DI1_20,
    Max2.DI1_21]

@[expose] noncomputable def DX1l : List Nat :=
  [Max2.DX1_0, Max2.DX1_1, Max2.DX1_2, Max2.DX1_3, Max2.DX1_4, Max2.DX1_5, Max2.DX1_6,
    Max2.DX1_7, Max2.DX1_8, Max2.DX1_9, Max2.DX1_10, Max2.DX1_11, Max2.DX1_12, Max2.DX1_13,
    Max2.DX1_14, Max2.DX1_15, Max2.DX1_16, Max2.DX1_17, Max2.DX1_18, Max2.DX1_19, Max2.DX1_20,
    Max2.DX1_21]

@[expose] def enc32L (l : List Nat) : Nat := l.foldr (fun x acc => x + 4294967296 * acc) 0

@[expose] noncomputable def prevF (Gi : List Nat) (PSl : List Nat) (s : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (Nat.mul (Nat.land (nthN Gi 0) SM) 4194303)
    (fun k _ => PSl.getD k 0) s

theorem wfE : ∀ i < 22, wfMat (Elist.getD i []) = true := by
  intro i hi
  interval_cases i
  · exact NativePair24.wf_Q0
  · exact Max2.wf_E1
  · exact Max2.wf_E2
  · exact Max2.wf_E3
  · exact Max2.wf_E4
  · exact Max2.wf_E5
  · exact Max2.wf_E6
  · exact Max2.wf_E7
  · exact Max2.wf_E8
  · exact Max2.wf_E9
  · exact Max2.wf_E10
  · exact Max2.wf_E11
  · exact Max2.wf_E12
  · exact Max2.wf_E13
  · exact Max2.wf_E14
  · exact Max2.wf_E15
  · exact Max2.wf_E16
  · exact Max2.wf_E17
  · exact Max2.wf_E18
  · exact Max2.wf_E19
  · exact Max2.wf_E20
  · exact Max2.wf_E21

theorem rows_mulS {B : List Nat} {X Y : Nat} (hB : wfMat B = true) (h : Nat.beq (mulS B X) Y = true)
    {t : Nat} (ht : t < 64) : vrow (rowOf Y t) = vrow (rowOf X t) ᵥ* stripMat B := by
  rw [← Nat.eq_of_beq_eq_true h]
  exact mulS_rows hB X ht

theorem rows_E {t : Nat} (ht : t < 22) : vrow (rowOf (row0Strip Elist) t) = e0 ᵥ* EK t :=
  row0Strip_rows (by decide) (by change t < 22; exact ht)

theorem rows_mulW3 {A B C : List Nat} {X Y : Nat} (hA : wfMat A = true) (hB : wfMat B = true)
    (hC : wfMat C = true) (h : Nat.beq (mulW [A, B, C] X) Y = true) {t : Nat} (ht : t < 64) :
    vrow (rowOf Y t) = vrow (rowOf X t) ᵥ* (stripMat A * stripMat B * stripMat C) := by
  have hW : ∀ W ∈ [A, B, C], wfMat W = true := by
    intro W hW
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hW
    rcases hW with h1 | h1 | h1 <;> subst h1 <;> assumption
  have e := mulW_rows (Ws := [A, B, C]) hW X ht
  rw [List.map_cons, List.map_cons, List.map_cons, List.map_nil, List.prod_cons, List.prod_cons,
    List.prod_cons, List.prod_nil, mul_one] at e
  rw [← Nat.eq_of_beq_eq_true h, e, mul_assoc]

theorem comm_vec {Cs : List Nat} {D D' i r : Nat} (h : Nat.beq (commRow Cs D D' i) r = true)
    (hr : r < 2 ^ 64) {j : Nat} (hj : j < Cs.length) {u v w : Fin 4370 → ZMod 2}
    (hu : vrow (rowOf (Cs.getD j 0) i) = u) (hv : vrow (rowOf D j) = v)
    (hw : vrow (rowOf D' j) = w) : u = if r.testBit j then w else v := by
  obtain ⟨h1, h0⟩ := commRow_sound (Nat.eq_of_beq_eq_true h) hr j hj
  by_cases hb : r.testBit j
  · rw [ite_eq_left hb, ← hu, ← hw, h1 hb]
  · rw [ite_eq_right hb, ← hu, ← hv, h0 (Bool.eq_false_of_ne_true hb)]

theorem comm_mat {Cs : List Nat} {D D' i r : Nat} (h : Nat.beq (commRow Cs D D' i) r = true)
    (hr : r < 2 ^ 64) {j : Nat} (hj : j < Cs.length) {A B X : MatB}
    (hu : vrow (rowOf (Cs.getD j 0) i) = e0 ᵥ* (A * B)) (hv : vrow (rowOf D j) = e0 ᵥ* (B * A))
    (hw : vrow (rowOf D' j) = e0 ᵥ* (B * X * A)) :
    e0 ᵥ* (A * B) = e0 ᵥ* (B * X ^ (if r.testBit j then 1 else 0) * A) := by
  rw [comm_vec h hr hj hu hv hw]
  by_cases hb : r.testBit j
  · rw [ite_eq_left hb, ite_eq_left hb, pow_one]
  · rw [ite_eq_right hb, ite_eq_right hb, pow_zero, mul_one]

theorem enc32L_testBit : ∀ (L : List Nat), (∀ x ∈ L, x < 2 ^ 32) → ∀ (l j : Nat), j < 32 →
    (enc32L L).testBit (32 * l + j) = (L.getD l 0).testBit j
  | [], _, l, j, _ => by
    simp [enc32L]
  | x :: xs, hL, l, j, hj => by
    have hx : x < 2 ^ 32 := hL x List.mem_cons_self
    have e : enc32L (x :: xs) = 2 ^ 32 * enc32L xs + x := by
      change x + 4294967296 * enc32L xs = _
      rw [Nat.add_comm]
      rfl
    rw [e, Nat.testBit_two_pow_mul_add _ hx]
    cases l with
    | zero =>
      rw [Nat.mul_zero, Nat.zero_add, ite_eq_left hj, List.getD_cons_zero]
    | succ l =>
      rw [ite_eq_right (by omega), List.getD_cons_succ,
        (by omega : 32 * (l + 1) + j - 32 = 32 * l + j)]
      exact enc32L_testBit xs (fun y hy => hL y (List.mem_cons_of_mem _ hy)) l j hj

theorem enc32L_bit (L : List Nat) (hL : ∀ x ∈ L, x < 2 ^ 32) (l j : Nat) (hj : j < 32) :
    (Nat.shiftRight (enc32L L) (32 * l)).testBit j = (L.getD l 0).testBit j := by
  change (enc32L L >>> (32 * l)).testBit j = _
  rw [Nat.testBit_shiftRight]
  exact enc32L_testBit L hL l j hj

theorem gram_lt : ∀ x ∈ CFSG.Monster.B.Bin.gramRows, x < 2 ^ 32 := by decide +kernel

theorem gram_lt64 : ∀ i < 22, CFSG.Monster.B.Bin.gramRows.getD i 0 < 2 ^ 64 := by decide +kernel

theorem act_bit (rows : List ℕ) {i j : ℕ} (hj : j < 22) :
    (if (vm32 22 (enc32L CFSG.Monster.B.Bin.gramRows) (rows.getD i 0)).testBit j then 1 else 0) =
      actK rows i j := by
  have h := vm32_bit 22 (enc32L CFSG.Monster.B.Bin.gramRows) (rows.getD i 0) (j := j) (by omega)
  have e : ∑ l ∈ Finset.range 22, (if (rows.getD i 0).testBit l then (1 : ZMod 2) else 0) *
      (if (Nat.shiftRight (enc32L CFSG.Monster.B.Bin.gramRows) (32 * l)).testBit j then 1 else 0) =
      ∑ l ∈ Finset.range 22,
        ((rowBitK rows i l * rowBitK CFSG.Monster.B.Bin.gramRows l j : ℕ) : ZMod 2) := by
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [enc32L_bit _ gram_lt l j (by omega), rowBitK, rowBitK]
    split_ifs <;> simp
  rw [actK, ← e, ← h]
  split_ifs <;> rfl

theorem rx_of {R : Nat} {Ms : List (List Nat)} (h : Nat.beq (mulS Max2.Xb (row0Strip Ms)) R = true)
    (hMs : Ms = Elist) : Nat.beq (mulS Max2.Xb (row0Strip Elist)) R = true := by
  subst hMs
  exact h

theorem rx_check : Nat.beq (mulS Max2.Xb (row0Strip Elist)) Max2.RX = true := by
  bm_bind rx_of CFSG.KC.BM.Max2.rx

theorem rows_RX {t : Nat} (ht : t < 22) : vrow (rowOf Max2.RX t) = e0 ᵥ* (EK t * XK) := by
  rw [rows_mulS Max2.wf_Xb rx_check (by omega), rows_E ht, Matrix.vecMul_vecMul]
  rfl

theorem aj_of (i : ℕ) {M : List Nat} {Ms : List (List Nat)} {A AX : Nat}
    (h : andB (Nat.beq (mulS M (row0Strip Ms)) A) (Nat.beq (mulS M Max2.RX) AX) = true)
    (hM : M = Elist.getD i []) (hMs : Ms = Elist) (hA : A = AJl.getD i 0)
    (hAX : AX = AXJl.getD i 0) :
    andB (Nat.beq (mulS (Elist.getD i []) (row0Strip Elist)) (AJl.getD i 0))
      (Nat.beq (mulS (Elist.getD i []) Max2.RX) (AXJl.getD i 0)) = true := by
  subst hM hMs hA hAX
  exact h

theorem aj_all : ∀ j < 22, andB (Nat.beq (mulS (Elist.getD j []) (row0Strip Elist)) (AJl.getD j 0))
    (Nat.beq (mulS (Elist.getD j []) Max2.RX) (AXJl.getD j 0)) = true := by
  forall_lt_bind CFSG.KC.BM.Max2.aj 22 aj_of

theorem gram_of (i : ℕ) {Cs : List Nat} {D D' r : Nat}
    (h : Nat.beq (commRow Cs D D' i) r = true) (hCs : Cs = AJl) (hD : D = AJl.getD i 0)
    (hD' : D' = AXJl.getD i 0) (hr : r = CFSG.Monster.B.Bin.gramRows.getD i 0) :
    Nat.beq (commRow AJl (AJl.getD i 0) (AXJl.getD i 0) i)
      (CFSG.Monster.B.Bin.gramRows.getD i 0) = true := by
  subst hCs hD hD' hr
  exact h

theorem gram_all : ∀ i < 22, Nat.beq (commRow AJl (AJl.getD i 0) (AXJl.getD i 0) i)
    (CFSG.Monster.B.Bin.gramRows.getD i 0) = true := by
  forall_lt_bind CFSG.KC.BM.Max2.gram 22 gram_of

theorem rows_AJ {j t : Nat} (hj : j < 22) (ht : t < 22) :
    vrow (rowOf (AJl.getD j 0) t) = e0 ᵥ* (EK t * EK j) := by
  obtain ⟨h1, -⟩ := Dy.andB_true (aj_all j hj)
  rw [rows_mulS (wfE j hj) h1 (by omega), rows_E ht, Matrix.vecMul_vecMul]
  rfl

theorem rows_AXJ {j t : Nat} (hj : j < 22) (ht : t < 22) :
    vrow (rowOf (AXJl.getD j 0) t) = e0 ᵥ* (EK t * XK * EK j) := by
  obtain ⟨-, h2⟩ := Dy.andB_true (aj_all j hj)
  rw [rows_mulS (wfE j hj) h2 (by omega), rows_RX ht, Matrix.vecMul_vecMul]
  rfl

theorem gram_test : ∀ i j, i < 22 → j < 22 → e0 ᵥ* (EK i * EK j) =
    e0 ᵥ* (EK j * XK ^ rowBitK CFSG.Monster.B.Bin.gramRows i j * EK i) := by
  intro i j hi hj
  exact comm_mat (gram_all i hi) (gram_lt64 i hi) (by change j < 22; exact hj) (rows_AJ hj hi)
    (rows_AJ hi hj) (rows_AXJ hi hj)

section Act

variable {Gi G : List Nat} {PSl CJl DIl DXl : List Nat} {PP : Nat} {rows : List ℕ}
  (hGi : wfMat Gi = true) (hG : wfMat G = true)
  (hps : ∀ s < 22, Nat.beq (Nat.lor (mulS (Elist.getD s [])
      (Nat.land (prevF Gi PSl s) (Nat.shiftLeft SM s)))
      (Nat.sub (prevF Gi PSl s) (Nat.land (prevF Gi PSl s) (Nat.shiftLeft SM s))))
      (PSl.getD s 0) = true)
  (hpp : Nat.beq (mulS G (PSl.getD 21 0)) PP = true)
  (hcj : ∀ j < 22, Nat.beq (mulS (Elist.getD j []) PP) (CJl.getD j 0) = true)
  (hdi : ∀ i < 22, andB (Nat.beq (mulW [Gi, Elist.getD i [], G] (row0Strip Elist)) (DIl.getD i 0))
      (Nat.beq (mulW [Gi, Elist.getD i [], G] Max2.RX) (DXl.getD i 0)) = true)
  (hact : ∀ i < 22, Nat.beq (commRow CJl (DIl.getD i 0) (DXl.getD i 0) i)
      (vm32 22 (enc32L CFSG.Monster.B.Bin.gramRows) (rows.getD i 0)) = true)
  (hlen : CJl.length = 22)

include hps in
theorem rows_PS : ∀ i < 22, ∀ t < 22, vrow (rowOf (PSl.getD i 0) t) =
    if t ≤ i then e0 ᵥ* (stripMat Gi * EK t) else e0 ᵥ* stripMat Gi
  | 0, _, t, ht => by
    rw [← Nat.eq_of_beq_eq_true (hps 0 (by norm_num)), rowUpd_rows (wfE 0 (by norm_num)) _
      (by norm_num) (by omega)]
    have hrep : ∀ s < 22, vrow (rowOf (prevF Gi PSl 0) s) = e0 ᵥ* stripMat Gi := fun s hs =>
      rep_rows Gi (k := 22) (by norm_num) (by norm_num) hs
    by_cases h0 : t = 0
    · subst h0
      rw [ite_eq_left rfl, ite_eq_left le_rfl, hrep 0 (by norm_num), Matrix.vecMul_vecMul]
      rfl
    · rw [ite_eq_right h0, ite_eq_right (by omega), hrep t ht]
  | i + 1, hi, t, ht => by
    have hp : prevF Gi PSl (i + 1) = PSl.getD i 0 := rfl
    rw [← Nat.eq_of_beq_eq_true (hps (i + 1) hi), hp, rowUpd_rows (wfE (i + 1) hi) _ (by omega)
      (by omega)]
    by_cases h : t = i + 1
    · subst h
      rw [ite_eq_left rfl, ite_eq_left le_rfl, rows_PS i (by omega) (i + 1) ht,
        ite_eq_right (by omega),
        Matrix.vecMul_vecMul]
      rfl
    · rw [ite_eq_right h, rows_PS i (by omega) t ht]
      by_cases h' : t ≤ i
      · rw [ite_eq_left h', ite_eq_left (by omega)]
      · rw [ite_eq_right h', ite_eq_right (by omega)]

include hG hps hpp in
theorem rows_PP {t : Nat} (ht : t < 22) :
    vrow (rowOf PP t) = e0 ᵥ* (stripMat Gi * EK t * stripMat G) := by
  rw [rows_mulS hG hpp (by omega), rows_PS hps 21 (by norm_num) t ht, ite_eq_left (by omega),
    Matrix.vecMul_vecMul]

include hG hps hpp hcj in
theorem rows_CJ {j t : Nat} (hj : j < 22) (ht : t < 22) :
    vrow (rowOf (CJl.getD j 0) t) = e0 ᵥ* (stripMat Gi * EK t * stripMat G * EK j) := by
  rw [rows_mulS (wfE j hj) (hcj j hj) (by omega), rows_PP hG hps hpp ht, Matrix.vecMul_vecMul]
  rfl

include hGi hG hdi in
theorem rows_DI {i t : Nat} (hi : i < 22) (ht : t < 22) :
    vrow (rowOf (DIl.getD i 0) t) = e0 ᵥ* (EK t * (stripMat Gi * EK i * stripMat G)) := by
  obtain ⟨h1, -⟩ := Dy.andB_true (hdi i hi)
  rw [rows_mulW3 hGi (wfE i hi) hG h1 (by omega), rows_E ht, Matrix.vecMul_vecMul]
  rfl

include hGi hG hdi in
theorem rows_DX {i t : Nat} (hi : i < 22) (ht : t < 22) :
    vrow (rowOf (DXl.getD i 0) t) = e0 ᵥ* (EK t * XK * (stripMat Gi * EK i * stripMat G)) := by
  obtain ⟨-, h2⟩ := Dy.andB_true (hdi i hi)
  rw [rows_mulW3 hGi (wfE i hi) hG h2 (by omega), rows_RX ht, Matrix.vecMul_vecMul]
  rfl

include hGi hG hps hpp hcj hdi hact hlen in
theorem act_test : ∀ i j, i < 22 → j < 22 →
    e0 ᵥ* (stripMat Gi * EK i * stripMat G * EK j) =
      e0 ᵥ* (EK j * XK ^ actK rows i j * (stripMat Gi * EK i * stripMat G)) := by
  intro i j hi hj
  have h := comm_mat (hact i hi) (lt_trans (vm32_lt _ _ _) (by norm_num)) (by rw [hlen]; exact hj)
    (rows_CJ hG hps hpp hcj hj hi) (rows_DI hGi hG hdi hi hj) (rows_DX hGi hG hdi hi hj)
  rwa [act_bit rows hj] at h

end Act

@[expose] def PSOK (Gi PSl : List Nat) (s : Nat) : Prop :=
  Nat.beq (Nat.lor (mulS (Elist.getD s []) (Nat.land (prevF Gi PSl s) (Nat.shiftLeft SM s)))
    (Nat.sub (prevF Gi PSl s) (Nat.land (prevF Gi PSl s) (Nat.shiftLeft SM s))))
    (PSl.getD s 0) = true

theorem psOK_of {Gi PSl : List Nat} {s : Nat} {M : List Nat} {P R : Nat}
    (h : Nat.beq (Nat.lor (mulS M (Nat.land P (Nat.shiftLeft SM s)))
      (Nat.sub P (Nat.land P (Nat.shiftLeft SM s)))) R = true)
    (hM : M = Elist.getD s []) (hP : P = prevF Gi PSl s) (hR : R = PSl.getD s 0) :
    PSOK Gi PSl s := by
  subst hM hP hR
  exact h

theorem ps0_of (s : ℕ) {M : List Nat} {P R : Nat}
    (h : Nat.beq (Nat.lor (mulS M (Nat.land P (Nat.shiftLeft SM s)))
      (Nat.sub P (Nat.land P (Nat.shiftLeft SM s)))) R = true)
    (hM : M = Elist.getD s []) (hP : P = prevF Max2.G1 PS0l s) (hR : R = PS0l.getD s 0) :
    PSOK Max2.G1 PS0l s := psOK_of h hM hP hR

theorem ps1_of (s : ℕ) {M : List Nat} {P R : Nat}
    (h : Nat.beq (Nat.lor (mulS M (Nat.land P (Nat.shiftLeft SM s)))
      (Nat.sub P (Nat.land P (Nat.shiftLeft SM s)))) R = true)
    (hM : M = Elist.getD s []) (hP : P = prevF Max2.Gi2 PS1l s) (hR : R = PS1l.getD s 0) :
    PSOK Max2.Gi2 PS1l s := psOK_of h hM hP hR

theorem ps0_all : ∀ s < 22, PSOK Max2.G1 PS0l s := by
  forall_lt_bind CFSG.KC.BM.Max2.ps0_ 22 ps0_of

theorem ps1_all : ∀ s < 22, PSOK Max2.Gi2 PS1l s := by
  forall_lt_bind CFSG.KC.BM.Max2.ps1_ 22 ps1_of

theorem pp_of {P R S : Nat} {Gs : List Nat} (h : Nat.beq (mulS Gs P) R = true)
    (hP : P = S) : Nat.beq (mulS Gs S) R = true := by
  subst hP
  exact h

theorem pp0_check : Nat.beq (mulS Max2.G1 (PS0l.getD 21 0)) Max2.PP0 = true :=
  pp_of Max2.pp0 rfl

theorem pp1_check : Nat.beq (mulS Max2.G2 (PS1l.getD 21 0)) Max2.PP1 = true :=
  pp_of Max2.pp1 rfl

theorem cj0_of (j : ℕ) {M : List Nat} {C : Nat} (h : Nat.beq (mulS M Max2.PP0) C = true)
    (hM : M = Elist.getD j []) (hC : C = CJ0l.getD j 0) :
    Nat.beq (mulS (Elist.getD j []) Max2.PP0) (CJ0l.getD j 0) = true := by
  subst hM hC
  exact h

theorem cj1_of (j : ℕ) {M : List Nat} {C : Nat} (h : Nat.beq (mulS M Max2.PP1) C = true)
    (hM : M = Elist.getD j []) (hC : C = CJ1l.getD j 0) :
    Nat.beq (mulS (Elist.getD j []) Max2.PP1) (CJ1l.getD j 0) = true := by
  subst hM hC
  exact h

theorem cj0_all : ∀ j < 22, Nat.beq (mulS (Elist.getD j []) Max2.PP0) (CJ0l.getD j 0) = true := by
  forall_lt_bind CFSG.KC.BM.Max2.cj0_ 22 cj0_of

theorem cj1_all : ∀ j < 22, Nat.beq (mulS (Elist.getD j []) Max2.PP1) (CJ1l.getD j 0) = true := by
  forall_lt_bind CFSG.KC.BM.Max2.cj1_ 22 cj1_of

theorem di0_of (i : ℕ) {Ws : List (List Nat)} {Ms : List (List Nat)} {A B : Nat}
    (h : andB (Nat.beq (mulW Ws (row0Strip Ms)) A) (Nat.beq (mulW Ws Max2.RX) B) = true)
    (hWs : Ws = [Max2.G1, Elist.getD i [], Max2.G1]) (hMs : Ms = Elist) (hA : A = DI0l.getD i 0)
    (hB : B = DX0l.getD i 0) :
    andB (Nat.beq (mulW [Max2.G1, Elist.getD i [], Max2.G1] (row0Strip Elist)) (DI0l.getD i 0))
      (Nat.beq (mulW [Max2.G1, Elist.getD i [], Max2.G1] Max2.RX) (DX0l.getD i 0)) = true := by
  subst hWs hMs hA hB
  exact h

theorem di1_of (i : ℕ) {Ws : List (List Nat)} {Ms : List (List Nat)} {A B : Nat}
    (h : andB (Nat.beq (mulW Ws (row0Strip Ms)) A) (Nat.beq (mulW Ws Max2.RX) B) = true)
    (hWs : Ws = [Max2.Gi2, Elist.getD i [], Max2.G2]) (hMs : Ms = Elist) (hA : A = DI1l.getD i 0)
    (hB : B = DX1l.getD i 0) :
    andB (Nat.beq (mulW [Max2.Gi2, Elist.getD i [], Max2.G2] (row0Strip Elist)) (DI1l.getD i 0))
      (Nat.beq (mulW [Max2.Gi2, Elist.getD i [], Max2.G2] Max2.RX) (DX1l.getD i 0)) = true := by
  subst hWs hMs hA hB
  exact h

theorem di0_all : ∀ i < 22,
    andB (Nat.beq (mulW [Max2.G1, Elist.getD i [], Max2.G1] (row0Strip Elist)) (DI0l.getD i 0))
      (Nat.beq (mulW [Max2.G1, Elist.getD i [], Max2.G1] Max2.RX) (DX0l.getD i 0)) = true := by
  forall_lt_bind CFSG.KC.BM.Max2.di0_ 22 di0_of

theorem di1_all : ∀ i < 22,
    andB (Nat.beq (mulW [Max2.Gi2, Elist.getD i [], Max2.G2] (row0Strip Elist)) (DI1l.getD i 0))
      (Nat.beq (mulW [Max2.Gi2, Elist.getD i [], Max2.G2] Max2.RX) (DX1l.getD i 0)) = true := by
  forall_lt_bind CFSG.KC.BM.Max2.di1_ 22 di1_of

theorem act0_of (i : ℕ) {Cs : List Nat} {D D' r : Nat} (h : Nat.beq (commRow Cs D D' i) r = true)
    (hCs : Cs = CJ0l) (hD : D = DI0l.getD i 0) (hD' : D' = DX0l.getD i 0)
    (hr : r = vm32 22 (enc32L CFSG.Monster.B.Bin.gramRows)
      (CFSG.Monster.B.Bin.quotRows1.getD i 0)) :
    Nat.beq (commRow CJ0l (DI0l.getD i 0) (DX0l.getD i 0) i)
      (vm32 22 (enc32L CFSG.Monster.B.Bin.gramRows) (CFSG.Monster.B.Bin.quotRows1.getD i 0)) =
        true := by
  subst hCs hD hD' hr
  exact h

theorem act1_of (i : ℕ) {Cs : List Nat} {D D' r : Nat} (h : Nat.beq (commRow Cs D D' i) r = true)
    (hCs : Cs = CJ1l) (hD : D = DI1l.getD i 0) (hD' : D' = DX1l.getD i 0)
    (hr : r = vm32 22 (enc32L CFSG.Monster.B.Bin.gramRows)
      (CFSG.Monster.B.Bin.quotRows2.getD i 0)) :
    Nat.beq (commRow CJ1l (DI1l.getD i 0) (DX1l.getD i 0) i)
      (vm32 22 (enc32L CFSG.Monster.B.Bin.gramRows) (CFSG.Monster.B.Bin.quotRows2.getD i 0)) =
        true := by
  subst hCs hD hD' hr
  exact h

theorem act0_all : ∀ i < 22, Nat.beq (commRow CJ0l (DI0l.getD i 0) (DX0l.getD i 0) i)
    (vm32 22 (enc32L CFSG.Monster.B.Bin.gramRows) (CFSG.Monster.B.Bin.quotRows1.getD i 0)) =
      true := by
  forall_lt_bind CFSG.KC.BM.Max2.act0_ 22 act0_of

theorem act1_all : ∀ i < 22, Nat.beq (commRow CJ1l (DI1l.getD i 0) (DX1l.getD i 0) i)
    (vm32 22 (enc32L CFSG.Monster.B.Bin.gramRows) (CFSG.Monster.B.Bin.quotRows2.getD i 0)) =
      true := by
  forall_lt_bind CFSG.KC.BM.Max2.act1_ 22 act1_of

theorem act1_test : ∀ i j, i < 22 → j < 22 → e0 ᵥ* (G1K * EK i * G1K * EK j) =
    e0 ᵥ* (EK j * XK ^ actK CFSG.Monster.B.Bin.quotRows1 i j * (G1K * EK i * G1K)) :=
  act_test Max2.wf_G1 Max2.wf_G1 ps0_all pp0_check cj0_all di0_all act0_all rfl

theorem act2_test : ∀ i j, i < 22 → j < 22 → e0 ᵥ* (Gi2K * EK i * G2K * EK j) =
    e0 ᵥ* (EK j * XK ^ actK CFSG.Monster.B.Bin.quotRows2 i j * (Gi2K * EK i * G2K)) :=
  act_test Max2.wf_Gi2 Max2.wf_G2 ps1_all pp1_check cj1_all di1_all act1_all rfl

theorem vecN_one : vecN 1 = e0 := by
  funext j
  rw [vecN, e0, Pi.single_apply, show (1 : ℕ) = 2 ^ 0 from rfl, Nat.testBit_two_pow]
  by_cases h : j = 0
  · subst h
    simp
  · have h' : (0 : ℕ) ≠ j.val := fun e => h (Fin.ext e.symm)
    simp [h, h']

theorem vx_ne : e0 ᵥ* XK ≠ e0 := by
  obtain ⟨h1, h2⟩ := Dy.andB_true Max2.vxdef
  have hb : AllBlocks Max2.Xb.rows Max2.Xb 0 := by bm_blocks CFSG.KC.BM.Max2.rows_Xb 69
  have h1lt : (1 : ℕ) < 2 ^ 4370 := Nat.one_lt_two_pow (by norm_num)
  obtain ⟨hlt, heq⟩ := vecMul_strip hb Max2.wf_Xb h1lt
  rw [Nat.eq_of_beq_eq_true h1] at hlt heq
  intro h
  have e : vecN Max2.vx = vecN 1 := by
    rw [heq, vecN_one]
    exact h
  rw [vecN_injective hlt h1lt e] at h2
  exact absurd h2 (by decide)

end CertificateChecks.KernelBM.Pair

end

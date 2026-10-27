module

public import CFSG.RankThree.PartTwo.Sec4.T444.Item434G28Check

public section

namespace CFSG.RankThree.PartTwo.Sec4.Item434G28

open CFSG.Quasithin
open scoped Matrix

@[expose] def vecCode (v : Array ℕ) : Array ℕ :=
  Array.ofFn (n := 36) fun t => if t.val % 6 = 0 then v[t.val / 6]! else 0

@[expose] def transCode (A : Array ℕ) : Array ℕ :=
  Array.ofFn (n := 36) fun t => A[6 * (t.val % 6) + t.val / 6]!

@[expose] def jCode : Array ℕ :=
  Array.ofFn (n := 36) fun t => if t.val % 6 = (t.val / 6 + 3) % 6 then 1 else 0

@[expose] def linCode (w : Array ℕ) (Q : Array (Array ℕ)) : Array ℕ :=
  Array.ofFn (n := 36) fun t =>
    mt w[0]! (Q[0]!)[t.val]! ^^^ mt w[1]! (Q[1]!)[t.val]! ^^^ mt w[2]! (Q[2]!)[t.val]! ^^^
      mt w[3]! (Q[3]!)[t.val]! ^^^ mt w[4]! (Q[4]!)[t.val]! ^^^ mt w[5]! (Q[5]!)[t.val]!

@[expose] def cCode (g : Array (Array ℕ)) (i : ℕ) : Array ℕ :=
  Array.ofFn (n := 36) fun t => (g[t.val % 6]!)[6 * (t.val / 6) + i]!

@[expose] def qCodes (g : Array (Array ℕ)) (binv : Array ℕ) : Array (Array ℕ) :=
  Array.ofFn (n := 6) fun i => mulCode (cCode g i.val) binv

@[expose] def centAt (Q : Array (Array ℕ)) (w : Array ℕ) : Bool :=
  let M := linCode w Q
  mulCode (mulCode (transCode M) jCode) M != jCode || powCode M 9 == idCode

@[expose] def centAll (Q : Array (Array ℕ)) : Bool :=
  (List.range 8).all fun a0 => (List.range 8).all fun a1 => (List.range 8).all fun a2 =>
    (List.range 8).all fun a3 => (List.range 8).all fun a4 => (List.range 8).all fun a5 =>
      centAt Q #[a0, a1, a2, a3, a4, a5]

@[expose] def centOK (g : Array (Array ℕ)) (v0 b binv : Array ℕ) : Bool :=
  decide (Valid b) && decide (Valid binv) && decide (v0.size = 6 ∧ ∀ i < 6, v0[i]! < 8) &&
  (List.range 6).all (fun k => decide (Valid g[k]!) && (List.range 6).all fun r =>
    b[6 * r + k]! == (mulCode g[k]! (vecCode v0))[6 * r]!) &&
  mulCode b binv == idCode && centAll (qCodes g binv)

theorem valid_vecCode {v : Array ℕ} (hv : ∀ i < 6, v[i]! < 8) : Valid (vecCode v) := by
  refine ⟨by simp [vecCode], fun t ht => ?_⟩
  rw [vecCode, getElem!_ofFn_nat' _ ht]
  split_ifs
  · exact hv _ (by omega)
  · norm_num

theorem decode_vecCode {v : Array ℕ} (i j : Fin 6) :
    decode (vecCode v) i j = if j.val = 0 then GF8.ofNat' v[i.val]! else 0 := by
  have ht : 6 * i.val + j.val < 36 := by have := i.2; have := j.2; omega
  have e1 : (6 * i.val + j.val) / 6 = i.val := by omega
  have e2 : (6 * i.val + j.val) % 6 = j.val := by omega
  simp only [decode, Matrix.of_apply]
  rw [vecCode, getElem!_ofFn_nat' _ ht]
  simp only [e1, e2]
  split_ifs
  · rfl
  · rfl

theorem valid_transCode {A : Array ℕ} (hA : Valid A) : Valid (transCode A) := by
  refine ⟨by simp [transCode], fun t ht => ?_⟩
  rw [transCode, getElem!_ofFn_nat' _ ht]
  exact hA.2 _ (by omega)

theorem decode_transCode {A : Array ℕ} : decode (transCode A) = (decode A).transpose := by
  ext i j
  have ht : 6 * i.val + j.val < 36 := by have := i.2; have := j.2; omega
  have e1 : (6 * i.val + j.val) / 6 = i.val := by omega
  have e2 : (6 * i.val + j.val) % 6 = j.val := by omega
  simp only [decode, Matrix.of_apply, Matrix.transpose_apply]
  rw [transCode, getElem!_ofFn_nat' _ ht]
  simp only [e1, e2]

theorem valid_jCode : Valid jCode := by
  refine ⟨by simp [jCode], fun t ht => ?_⟩
  rw [jCode, getElem!_ofFn_nat' _ ht]
  split_ifs <;> norm_num

theorem valid_linCode {w : Array ℕ} {Q : Array (Array ℕ)} (hw : ∀ i < 6, w[i]! < 8)
    (hQ : ∀ i < 6, Valid Q[i]!) : Valid (linCode w Q) := by
  refine ⟨by simp [linCode], fun t ht => ?_⟩
  rw [linCode, getElem!_ofFn_nat' _ ht]
  have l : ∀ i, i < 6 → mt w[i]! (Q[i]!)[t]! < 8 := fun i hi => mt_lt (hw i hi) ((hQ i hi).2 t ht)
  exact xor_lt8' (xor_lt8' (xor_lt8' (xor_lt8' (xor_lt8' (l 0 (by omega)) (l 1 (by omega)))
    (l 2 (by omega))) (l 3 (by omega))) (l 4 (by omega))) (l 5 (by omega))

theorem decode_linCode_six {w : Array ℕ} {Q : Array (Array ℕ)} (hw : ∀ i < 6, w[i]! < 8)
    (hQ : ∀ i < 6, Valid Q[i]!) :
    decode (linCode w Q) =
      GF8.ofNat' w[0]! • decode Q[0]! + GF8.ofNat' w[1]! • decode Q[1]! +
      GF8.ofNat' w[2]! • decode Q[2]! + GF8.ofNat' w[3]! • decode Q[3]! +
      GF8.ofNat' w[4]! • decode Q[4]! + GF8.ofNat' w[5]! • decode Q[5]! := by
  ext i j
  have ht : 6 * i.val + j.val < 36 := by have := i.2; have := j.2; omega
  have l : ∀ k, k < 6 → mt w[k]! (Q[k]!)[6 * i.val + j.val]! < 8 :=
    fun k hk => mt_lt (hw k hk) ((hQ k hk).2 _ ht)
  simp only [decode, Matrix.of_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  rw [linCode, getElem!_ofFn_nat' _ ht]
  rw [ofNat'_xor6 (l 0 (by omega)) (l 1 (by omega)) (l 2 (by omega)) (l 3 (by omega))
    (l 4 (by omega)) (l 5 (by omega))]
  rw [ofNat'_mt (hw 0 (by omega)) ((hQ 0 (by omega)).2 _ ht),
    ofNat'_mt (hw 1 (by omega)) ((hQ 1 (by omega)).2 _ ht),
    ofNat'_mt (hw 2 (by omega)) ((hQ 2 (by omega)).2 _ ht),
    ofNat'_mt (hw 3 (by omega)) ((hQ 3 (by omega)).2 _ ht),
    ofNat'_mt (hw 4 (by omega)) ((hQ 4 (by omega)).2 _ ht),
    ofNat'_mt (hw 5 (by omega)) ((hQ 5 (by omega)).2 _ ht)]

theorem decode_linCode {w : Array ℕ} {Q : Array (Array ℕ)} (hw : ∀ i < 6, w[i]! < 8)
    (hQ : ∀ i < 6, Valid Q[i]!) :
    decode (linCode w Q) = ∑ i : Fin 6, GF8.ofNat' w[i.val]! • decode Q[i.val]! := by
  rw [Fin.sum_univ_six]
  exact decode_linCode_six hw hQ

theorem valid_cCode {g : Array (Array ℕ)} (hg : ∀ k < 6, Valid g[k]!) {i : ℕ} (hi : i < 6) :
    Valid (cCode g i) := by
  refine ⟨by simp [cCode], fun t ht => ?_⟩
  rw [cCode, getElem!_ofFn_nat' _ ht]
  exact (hg _ (by omega)).2 _ (by omega)

theorem decode_cCode (g : Array (Array ℕ)) (i : ℕ) (r k : Fin 6) :
    decode (cCode g i) r k = GF8.ofNat' (g[k.val]!)[6 * r.val + i]! := by
  have ht : 6 * r.val + k.val < 36 := by have := r.2; have := k.2; omega
  have e1 : (6 * r.val + k.val) / 6 = r.val := by omega
  have e2 : (6 * r.val + k.val) % 6 = k.val := by omega
  simp only [decode, Matrix.of_apply]
  rw [cCode, getElem!_ofFn_nat' _ ht]
  simp only [e1, e2]

theorem qCodes_get (g : Array (Array ℕ)) (binv : Array ℕ) {i : ℕ} (hi : i < 6) :
    (qCodes g binv)[i]! = mulCode (cCode g i) binv := by
  rw [qCodes, getElem!_ofFn_nat' _ hi]

theorem decode_powCode {A : Array ℕ} (hA : Valid A) (k : ℕ) :
    decode (powCode A k) = (decode A) ^ k := by
  induction k with
  | zero => simp [powCode, decode_idCode]
  | succ k ih => rw [powCode, decode_mulCode (valid_powCode hA k) hA, ih, pow_succ]

theorem pow_nine_of_commutes {g : Array (Array ℕ)} {v0 b binv : Array ℕ}
    (h : centOK g v0 b binv = true) {P : Matrix (Fin 6) (Fin 6) GF8}
    (hP : ∀ k < 6, P * decode g[k]! = decode g[k]! * P)
    (hsymp : P.transpose * decode jCode * P = decode jCode) : P ^ 9 = 1 := by
  simp only [centOK, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range,
    beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨hb, hbinv⟩, hv0⟩, hcol⟩, hmul⟩, hall⟩ := h
  simp only [centAll, List.all_eq_true, List.mem_range] at hall
  have hg : ∀ k < 6, Valid g[k]! := fun k hk => (hcol k hk).1
  have hv0' : ∀ i < 6, v0[i]! < 8 := hv0.2
  have hV : Valid (vecCode v0) := valid_vecCode hv0'
  set B := decode b with hB
  set Bi := decode binv with hBi
  have hBBi : B * Bi = 1 := by rw [hB, hBi, ← decode_mulCode hb hbinv, hmul, decode_idCode]
  set vv : Fin 6 → GF8 := fun r => GF8.ofNat' v0[r.val]! with hvv
  have hcolB : ∀ k r : Fin 6, B r k = (decode g[k.val]! *ᵥ vv) r := by
    intro k r
    have e := congrFun (congrFun (decode_mulCode (hg k.val k.2) hV) r) 0
    rw [Matrix.mul_apply] at e
    have e2 : B r k = decode (mulCode g[k.val]! (vecCode v0)) r 0 := by
      have := (hcol k.val k.2).2 r.val r.2
      simp only [hB, decode, Matrix.of_apply]
      rw [this]
      simp
    rw [e2, e]
    simp only [decode_vecCode, Matrix.mulVec, dotProduct, vv]
    simp
  set w : Fin 6 → GF8 := P *ᵥ vv with hw
  have hPB : ∀ r k : Fin 6, (P * B) r k = (decode g[k.val]! *ᵥ w) r := by
    intro r k
    have h1 : (P * B) r k = (P *ᵥ (fun j => B j k)) r := by
      simp [Matrix.mul_apply, Matrix.mulVec, dotProduct]
    have h2 : (fun j => B j k) = decode g[k.val]! *ᵥ vv := funext fun j => hcolB k j
    rw [h1, h2, Matrix.mulVec_mulVec, hP k.val k.2, ← Matrix.mulVec_mulVec]
  have hC : P * B = ∑ i : Fin 6, w i • decode (cCode g i.val) := by
    ext r k
    rw [hPB]
    simp only [Matrix.sum_apply, Matrix.smul_apply, decode_cCode, smul_eq_mul, Matrix.mulVec,
      dotProduct]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [mul_comm]
    simp [decode]
  have hPeq : P = ∑ i : Fin 6, w i • decode (mulCode (cCode g i.val) binv) := by
    have h1 : P = P * B * Bi := by rw [mul_assoc, hBBi, mul_one]
    rw [h1, hC, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [decode_mulCode (valid_cCode hg i.2) hbinv, smul_mul_assoc]
  set wArr : Array ℕ :=
    #[(w 0).toNat, (w 1).toNat, (w 2).toNat, (w 3).toNat, (w 4).toNat, (w 5).toNat] with hwArr
  have hwArr_lt : ∀ i < 6, wArr[i]! < 8 := by
    intro i hi
    interval_cases i <;> exact toNat_lt' _
  have hQ : ∀ i < 6, Valid (qCodes g binv)[i]! := by
    intro i hi
    rw [qCodes_get g binv hi]
    exact valid_mulCode (valid_cCode hg hi) hbinv
  have hwi : ∀ i : Fin 6, GF8.ofNat' wArr[i.val]! = w i := by
    intro i
    fin_cases i <;> simp [hwArr, ofNat'_toNat']
  have hdecM : decode (linCode wArr (qCodes g binv)) = P := by
    rw [decode_linCode hwArr_lt hQ, hPeq]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [qCodes_get g binv i.2, hwi i]
  have hMv : Valid (linCode wArr (qCodes g binv)) := valid_linCode hwArr_lt hQ
  have hchk := hall (w 0).toNat (toNat_lt' _) (w 1).toNat (toNat_lt' _) (w 2).toNat
    (toNat_lt' _) (w 3).toNat (toNat_lt' _) (w 4).toNat (toNat_lt' _) (w 5).toNat (toNat_lt' _)
  simp only [centAt, Bool.or_eq_true, bne_iff_ne, ne_eq, beq_iff_eq] at hchk
  rcases hchk with hne | hpow
  · exfalso
    apply hne
    have hv1 := valid_mulCode (valid_transCode hMv) valid_jCode
    apply eq_of_decode_eq (valid_mulCode hv1 hMv) valid_jCode
    rw [decode_mulCode hv1 hMv, decode_mulCode (valid_transCode hMv) valid_jCode, decode_transCode,
      hdecM]
    exact hsymp
  · have := congrArg decode hpow
    rw [decode_powCode hMv, hdecM, decode_idCode] at this
    exact this

end CFSG.RankThree.PartTwo.Sec4.Item434G28

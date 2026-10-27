module

public import CFSG.Quasithin.Background.F918W2

public section

namespace CFSG.Quasithin.D35ValChk

open Matrix

theorem charP_two_of_card_four (K : Type) [Field K] [Finite K] (h : Nat.card K = 4) : CharP K 2 := by
  have := Fintype.ofFinite K
  obtain ⟨n, hp, hn⟩ := FiniteField.card K (ringChar K)
  rw [← Nat.card_eq_fintype_card, h] at hn
  have hdvd : ringChar K ∣ 2 ^ 2 := by
    have : ringChar K ∣ ringChar K ^ (n : ℕ) := dvd_pow_self _ n.ne_zero
    rw [← hn] at this
    simpa using this
  have h2 : ringChar K = 2 := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow hdvd)
  exact h2 ▸ ringChar.charP K

private theorem exists_omega (K : Type) [Field K] [Finite K] (h : Nat.card K = 4) :
    ∃ ω : K, ω ≠ 0 ∧ ω ≠ 1 ∧ ω * ω = ω + 1 ∧ ∀ c : K, c = 0 ∨ c = 1 ∨ c = ω ∨ c = 1 + ω := by
  classical
  have hK2 := charP_two_of_card_four K h
  have h2 : (2 : K) = 0 := by
    have := CharP.cast_eq_zero K 2
    simpa using this
  have := Fintype.ofFinite K
  have hcard : Fintype.card K = 4 := by rw [← Nat.card_eq_fintype_card, h]
  obtain ⟨ω, hω0, hω1⟩ : ∃ ω : K, ω ≠ 0 ∧ ω ≠ 1 := by
    by_contra hcon
    have hsub : (Finset.univ : Finset K) ⊆ {0, 1} := by
      intro x _
      by_cases hx : x = 0
      · simp [hx]
      · have : x = 1 := by
          by_contra hx1
          exact hcon ⟨x, hx, hx1⟩
        simp [this]
    have := Finset.card_le_card hsub
    rw [Finset.card_univ, hcard] at this
    have h2' : ({0, 1} : Finset K).card ≤ 2 := Finset.card_le_two
    omega
  have hcardu : Nat.card Kˣ = 3 := by
    rw [Nat.card_units, h]
  have hω3 : ω ^ 3 = 1 := by
    have := pow_card_eq_one' (G := Kˣ) (x := Units.mk0 ω hω0)
    rw [hcardu] at this
    simpa using congrArg Units.val this
  have hq : ω * ω = ω + 1 := by
    have h1 : (ω - 1) * (ω * ω + ω + 1) = 0 := by linear_combination hω3
    have h1' : ω - 1 ≠ 0 := sub_ne_zero.mpr hω1
    have h3 := (mul_eq_zero.mp h1).resolve_left h1'
    linear_combination h3 - (ω + 1) * h2
  have hn0 : 1 + ω ≠ 0 := by
    intro hh
    apply hω1
    linear_combination hh - h2
  have hn1 : 1 + ω ≠ 1 := by
    intro hh
    apply hω0
    linear_combination hh
  have hn2 : 1 + ω ≠ ω := by
    intro hh
    exact one_ne_zero (by linear_combination hh)
  have h01 : (0 : K) ≠ 1 := zero_ne_one
  have hdist : ({0, 1, ω, 1 + ω} : Finset K).card = 4 := by
    rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_pair]
    · exact hn2.symm
    · simp [hω1.symm, hn1.symm]
    · simp [h01, hω0.symm, hn0.symm]
  have huniv : ({0, 1, ω, 1 + ω} : Finset K) = Finset.univ :=
    Finset.eq_univ_of_card _ (by rw [hdist, hcard])
  refine ⟨ω, hω0, hω1, hq, fun c => ?_⟩
  have hc : c ∈ ({0, 1, ω, 1 + ω} : Finset K) := by rw [huniv]; exact Finset.mem_univ c
  simpa using hc

theorem exists_kcoding (K : Type) [Field K] [Finite K] (h : Nat.card K = 4) : Nonempty (KCoding K) := by
  classical
  obtain ⟨ω, hω0, hω1, hq, hall⟩ := exists_omega K h
  have hK2 := charP_two_of_card_four K h
  have h2 : (2 : K) = 0 := by
    have := CharP.cast_eq_zero K 2
    simpa using this
  have hn0 : 1 + ω ≠ 0 := by
    intro hh
    apply hω1
    linear_combination hh - h2
  have hn1 : 1 + ω ≠ 1 := by
    intro hh
    apply hω0
    linear_combination hh
  have hn2 : 1 + ω ≠ ω := by
    intro hh
    exact one_ne_zero (by linear_combination hh)
  have h10 : (1 : K) ≠ 0 := one_ne_zero
  have hω10 : ω ≠ 0 := hω0
  refine ⟨{ dec := fun e => if e = 0 then 0 else if e = 1 then 1 else if e = 2 then ω else 1 + ω
            enc := fun c => if c = 0 then 0 else if c = 1 then 1 else if c = ω then 2 else 3
            enc_lt := ?_, dec_enc := ?_, enc_dec := ?_, dec_zero := ?_, dec_one := ?_, dec_xor := ?_,
            dec_smul := ?_ }⟩
  · intro c
    split_ifs <;> decide
  · intro c
    rcases hall c with rfl | rfl | rfl | rfl
    · simp
    · simp [h10]
    · simp [hω0, hω1]
    · simp [hn0, hn1, hn2]
  · intro e he
    interval_cases e
    · simp
    · simp [h10]
    · simp [hω0, hω1]
    · simp [hn0, hn1, hn2]
  · simp
  · simp
  · intro a b ha hb
    interval_cases a <;> interval_cases b <;> simp [Nat.xor_eq] <;> first
      | ring1
      | linear_combination (-1 : K) * h2
      | linear_combination h2
      | linear_combination ω * h2
      | linear_combination (-ω) * h2
      | linear_combination (1 + ω) * h2
      | linear_combination (-(1 + ω)) * h2
  · intro a b ha hb
    interval_cases a <;> interval_cases b <;> simp [smul, smTab, hq] <;> first
      | ring1
      | linear_combination (-1 : K) * h2
      | linear_combination h2
      | linear_combination ω * h2
      | linear_combination (-ω) * h2
      | linear_combination (1 + ω) * h2
      | linear_combination (-(1 + ω)) * h2
      | linear_combination (-1 : K) * hq
      | linear_combination hq
      | linear_combination (-1 : K) * hq + (-ω) * h2
      | linear_combination hq + ω * h2
      | linear_combination (-1 : K) * hq - (ω + 1) * h2

theorem kent_eq_div_mod (a p : Nat) : kent a p = (a / 2 ^ p) % 4 := by
  have h1 : Nat.shiftRight a p = a / 2 ^ p := Nat.shiftRight_eq_div_pow a p
  unfold kent
  rw [h1, Nat.land_eq, show (3 : Nat) = 2 ^ 2 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]

theorem kent_lt4 (a p : Nat) : kent a p < 4 := by
  rw [kent_eq_div_mod]; omega

theorem digits_sum (a : Nat) (ha : a < 2 ^ 18) :
    a = kent a 0 + 4 * kent a 2 + 16 * kent a 4 + 64 * kent a 6 + 256 * kent a 8 + 1024 * kent a 10 +
      4096 * kent a 12 + 16384 * kent a 14 + 65536 * kent a 16 := by
  simp only [kent_eq_div_mod]
  norm_num
  omega

theorem eq_of_kent_eq {a b : Nat} (ha : a < 2 ^ 18) (hb : b < 2 ^ 18)
    (h : ∀ i, i < 3 → ∀ j, j < 3 → kent a (6 * i + 2 * j) = kent b (6 * i + 2 * j)) : a = b := by
  rw [digits_sum a ha, digits_sum b hb]
  have h00 := h 0 (by omega) 0 (by omega)
  have h01 := h 0 (by omega) 1 (by omega)
  have h02 := h 0 (by omega) 2 (by omega)
  have h10 := h 1 (by omega) 0 (by omega)
  have h11 := h 1 (by omega) 1 (by omega)
  have h12 := h 1 (by omega) 2 (by omega)
  have h20 := h 2 (by omega) 0 (by omega)
  have h21 := h 2 (by omega) 1 (by omega)
  have h22 := h 2 (by omega) 2 (by omega)
  simp only [Nat.mul_zero, Nat.zero_add, Nat.reduceMul, Nat.reduceAdd] at h00 h01 h02 h10 h11 h12 h20 h21 h22
  rw [h00, h01, h02, h10, h11, h12, h20, h21, h22]

theorem lor_shl {x y : Nat} (k : Nat) (hx : x < 2 ^ k) :
    Nat.lor x (Nat.shiftLeft y k) = x + y * 2 ^ k := by
  have h1 : Nat.shiftLeft y k = y <<< k := rfl
  rw [h1, Nat.lor_eq, Nat.or_comm, ← Nat.shiftLeft_add_eq_or_of_lt hx, Nat.shiftLeft_eq]
  ring

theorem smul_lt64 (e v : Nat) : smul e v < 64 := by
  unfold smul
  rw [Nat.land_eq, show (63 : Nat) = 2 ^ 6 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
  exact Nat.mod_lt _ (by norm_num)

theorem smul_lt4 : ∀ e, e < 4 → ∀ v, v < 4 → smul e v < 4 := by decide

private theorem smul_digits : ∀ e, e < 4 → ∀ v, v < 64 →
    kent (smul e v) 0 = smul e (kent v 0) ∧ kent (smul e v) 2 = smul e (kent v 2) ∧
      kent (smul e v) 4 = smul e (kent v 4) := by decide

private theorem kent_smul (e v j : Nat) (he : e < 4) (hv : v < 64) (hj : j < 3) :
    kent (smul e v) (2 * j) = smul e (kent v (2 * j)) := by
  obtain ⟨h0, h2, h4⟩ := smul_digits e he v hv
  interval_cases j
  · exact h0
  · exact h2
  · exact h4

theorem kent_xor (x y p : Nat) : kent (Nat.xor x y) p = Nat.xor (kent x p) (kent y p) := by
  have h : ∀ x p : Nat, Nat.shiftRight x p = x >>> p := fun _ _ => rfl
  simp only [kent, h, Nat.land_eq, Nat.xor_eq, Nat.shiftRight_xor_distrib, Nat.and_xor_distrib_right]

private theorem krow_lt64 (b k : Nat) : krow b k < 64 := by
  unfold krow
  rw [Nat.land_eq, show (63 : Nat) = 2 ^ 6 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
  exact Nat.mod_lt _ (by norm_num)

private theorem kent_krow (b k j : Nat) (hj : j < 3) :
    kent (krow b k) (2 * j) = kent b (6 * k + 2 * j) := by
  have h1 : krow b k = (b / 2 ^ (6 * k)) % 64 := by
    unfold krow
    have h : Nat.shiftRight b (Nat.mul 6 k) = b >>> (6 * k) := rfl
    rw [h, Nat.shiftRight_eq_div_pow, Nat.land_eq, show (63 : Nat) = 2 ^ 6 - 1 from rfl,
      Nat.and_two_pow_sub_one_eq_mod]
  rw [kent_eq_div_mod, kent_eq_div_mod, h1, pow_add, ← Nat.div_div_eq_div_mul]
  interval_cases j <;> norm_num <;> omega

private theorem krowMul_lt64 (a s b : Nat) : krowMul a s b < 64 := by
  unfold krowMul
  exact Nat.xor_lt_two_pow (n := 6) (Nat.xor_lt_two_pow (n := 6) (smul_lt64 _ _) (smul_lt64 _ _)) (smul_lt64 _ _)

private theorem kmul_eq (a b : Nat) :
    kmul a b = krowMul a 0 b + krowMul a 6 b * 2 ^ 6 + krowMul a 12 b * 2 ^ 12 := by
  have h0 := krowMul_lt64 a 0 b
  have h1 := krowMul_lt64 a 6 b
  unfold kmul
  rw [lor_shl 6 (by omega), lor_shl 12 (by omega)]

private theorem kent_krowMul (a s b j : Nat) (hj : j < 3) :
    kent (krowMul a s b) (2 * j) =
      Nat.xor (Nat.xor (smul (kent a s) (kent b (2 * j))) (smul (kent a (s + 2)) (kent b (6 + 2 * j))))
        (smul (kent a (s + 4)) (kent b (12 + 2 * j))) := by
  have e0 := kent_krow b 0 j hj
  have e1 := kent_krow b 1 j hj
  have e2 := kent_krow b 2 j hj
  simp only [Nat.mul_zero, Nat.zero_add, Nat.reduceMul] at e0 e1 e2
  unfold krowMul
  rw [kent_xor, kent_xor, kent_smul _ _ _ (kent_lt4 _ _) (krow_lt64 _ _) hj,
    kent_smul _ _ _ (kent_lt4 _ _) (krow_lt64 _ _) hj, kent_smul _ _ _ (kent_lt4 _ _) (krow_lt64 _ _) hj,
    e0, e1, e2]

theorem kent_kmul (a b i j : Nat) (hi : i < 3) (hj : j < 3) :
    kent (kmul a b) (6 * i + 2 * j) =
      Nat.xor (Nat.xor (smul (kent a (6 * i)) (kent b (2 * j)))
        (smul (kent a (6 * i + 2)) (kent b (6 + 2 * j)))) (smul (kent a (6 * i + 4)) (kent b (12 + 2 * j))) := by
  have h0 := krowMul_lt64 a 0 b
  have h1 := krowMul_lt64 a 6 b
  have h2 := krowMul_lt64 a 12 b
  rw [kmul_eq]
  interval_cases i
  · have := kent_krowMul a 0 b j hj
    simp only [Nat.mul_zero, Nat.zero_add] at this ⊢
    rw [← this, kent_eq_div_mod, kent_eq_div_mod]
    interval_cases j <;> norm_num <;> omega
  · have := kent_krowMul a 6 b j hj
    simp only [Nat.mul_one] at this ⊢
    rw [← this, kent_eq_div_mod, kent_eq_div_mod]
    interval_cases j <;> norm_num <;> omega
  · have := kent_krowMul a 12 b j hj
    rw [show 6 * 2 = 12 from rfl]
    rw [← this, kent_eq_div_mod, kent_eq_div_mod]
    interval_cases j <;> norm_num <;> omega

private def kX (a v s : Nat) : Nat :=
  Nat.xor (Nat.xor (fmul (kent a s) (kent v 0)) (fmul (kent a (s + 2)) (kent v 2))) (fmul (kent a (s + 4)) (kent v 4))

private theorem kX_lt4 (a v s : Nat) : kX a v s < 4 := by
  unfold kX fmul
  exact Nat.xor_lt_two_pow (n := 2) (Nat.xor_lt_two_pow (n := 2) (smul_lt4 _ (kent_lt4 _ _) _ (kent_lt4 _ _))
    (smul_lt4 _ (kent_lt4 _ _) _ (kent_lt4 _ _))) (smul_lt4 _ (kent_lt4 _ _) _ (kent_lt4 _ _))

private theorem kapply_eq (a v : Nat) : kapply a v = kX a v 0 + kX a v 6 * 2 ^ 2 + kX a v 12 * 2 ^ 4 := by
  have h0 := kX_lt4 a v 0
  have h1 := kX_lt4 a v 6
  have e : kapply a v =
      Nat.lor (Nat.lor (kX a v 0) (Nat.shiftLeft (kX a v 6) 2)) (Nat.shiftLeft (kX a v 12) 4) := rfl
  rw [e, lor_shl 2 h0, lor_shl 4 (by omega)]

private theorem kent_kapply (a v i : Nat) (hi : i < 3) : kent (kapply a v) (2 * i) = kX a v (6 * i) := by
  have h0 := kX_lt4 a v 0
  have h1 := kX_lt4 a v 6
  have h2 := kX_lt4 a v 12
  rw [kapply_eq, kent_eq_div_mod]
  interval_cases i <;> norm_num <;> omega

theorem digits_sum6 (a : Nat) (ha : a < 2 ^ 6) : a = kent a 0 + 4 * kent a 2 + 16 * kent a 4 := by
  simp only [kent_eq_div_mod]
  norm_num
  omega

theorem eq_of_kent_eq6 {a b : Nat} (ha : a < 2 ^ 6) (hb : b < 2 ^ 6)
    (h : ∀ j, j < 3 → kent a (2 * j) = kent b (2 * j)) : a = b := by
  rw [digits_sum6 a ha, digits_sum6 b hb]
  have h0 := h 0 (by omega)
  have h1 := h 1 (by omega)
  have h2 := h 2 (by omega)
  simp only [Nat.mul_zero, Nat.reduceMul] at h0 h1 h2
  rw [h0, h1, h2]

theorem eq_of_kent_eq_fin {a b : Nat} (ha : a < 2 ^ 18) (hb : b < 2 ^ 18)
    (h : ∀ i j : Fin 3, kent a (6 * i.val + 2 * j.val) = kent b (6 * i.val + 2 * j.val)) : a = b :=
  eq_of_kent_eq ha hb fun i hi j hj => h ⟨i, hi⟩ ⟨j, hj⟩

namespace KCoding

variable {K : Type} [Field K] (C : KCoding K)

theorem kent_mc (A : Matrix (Fin 3) (Fin 3) K) (i j : Fin 3) :
    kent (C.mc A) (6 * i.val + 2 * j.val) = C.enc (A i j) := by
  have h0 := C.enc_lt (A 0 0); have h1 := C.enc_lt (A 0 1); have h2 := C.enc_lt (A 0 2)
  have h3 := C.enc_lt (A 1 0); have h4 := C.enc_lt (A 1 1); have h5 := C.enc_lt (A 1 2)
  have h6 := C.enc_lt (A 2 0); have h7 := C.enc_lt (A 2 1); have h8 := C.enc_lt (A 2 2)
  rw [kent_eq_div_mod]
  unfold KCoding.mc
  fin_cases i <;> fin_cases j <;> simp <;> omega

theorem mc_lt (A : Matrix (Fin 3) (Fin 3) K) : C.mc A < 2 ^ 18 := by
  have h0 := C.enc_lt (A 0 0); have h1 := C.enc_lt (A 0 1); have h2 := C.enc_lt (A 0 2)
  have h3 := C.enc_lt (A 1 0); have h4 := C.enc_lt (A 1 1); have h5 := C.enc_lt (A 1 2)
  have h6 := C.enc_lt (A 2 0); have h7 := C.enc_lt (A 2 1); have h8 := C.enc_lt (A 2 2)
  unfold KCoding.mc
  norm_num
  omega

theorem mc_inj {A B : Matrix (Fin 3) (Fin 3) K} (h : C.mc A = C.mc B) : A = B := by
  ext i j
  have := congrArg (fun x => kent x (6 * i.val + 2 * j.val)) h
  simp only [kent_mc] at this
  have e := congrArg C.dec this
  simpa [C.dec_enc] using e

theorem enc_zero : C.enc 0 = 0 := by
  have h := C.enc_dec 0 (by norm_num)
  rwa [C.dec_zero] at h

theorem enc_one : C.enc 1 = 1 := by
  have h := C.enc_dec 1 (by norm_num)
  rwa [C.dec_one] at h

theorem enc_add (x y : K) : C.enc (x + y) = Nat.xor (C.enc x) (C.enc y) := by
  have h := C.dec_xor (C.enc x) (C.enc y) (C.enc_lt x) (C.enc_lt y)
  rw [C.dec_enc, C.dec_enc] at h
  have hlt : Nat.xor (C.enc x) (C.enc y) < 4 := Nat.xor_lt_two_pow (n := 2) (C.enc_lt x) (C.enc_lt y)
  rw [← h]
  exact C.enc_dec _ hlt

theorem enc_mul (x y : K) : C.enc (x * y) = smul (C.enc x) (C.enc y) := by
  have h := C.dec_smul (C.enc x) (C.enc y) (C.enc_lt x) (C.enc_lt y)
  rw [C.dec_enc, C.dec_enc] at h
  have hlt : smul (C.enc x) (C.enc y) < 4 := smul_lt4 _ (C.enc_lt x) _ (C.enc_lt y)
  rw [← h]
  exact C.enc_dec _ hlt

theorem kent_vc (w : Fin 3 → K) (j : Fin 3) : kent (C.vc w) (2 * j.val) = C.enc (w j) := by
  have h0 := C.enc_lt (w 0)
  have h1 := C.enc_lt (w 1)
  have h2 := C.enc_lt (w 2)
  rw [kent_eq_div_mod]
  unfold KCoding.vc
  fin_cases j <;> simp <;> omega

theorem vc_lt (w : Fin 3 → K) : C.vc w < 64 := by
  have h0 := C.enc_lt (w 0)
  have h1 := C.enc_lt (w 1)
  have h2 := C.enc_lt (w 2)
  unfold KCoding.vc
  omega

theorem vc_inj {w w' : Fin 3 → K} (h : C.vc w = C.vc w') : w = w' := by
  funext j
  have := congrArg (fun x => kent x (2 * j.val)) h
  simp only [kent_vc] at this
  have e := congrArg C.dec this
  simpa [C.dec_enc] using e

theorem vc_surj {v : Nat} (hv : v < 64) : ∃ w : Fin 3 → K, C.vc w = v := by
  refine ⟨fun j => C.dec (kent v (2 * j.val)), ?_⟩
  apply eq_of_kent_eq6 (C.vc_lt _) hv
  intro j hj
  have h := C.kent_vc (fun j : Fin 3 => C.dec (kent v (2 * j.val))) ⟨j, hj⟩
  rw [h]
  exact C.enc_dec _ (kent_lt4 _ _)

theorem vc_add (w w' : Fin 3 → K) : C.vc (w + w') = Nat.xor (C.vc w) (C.vc w') := by
  refine eq_of_kent_eq6 (b := Nat.xor (C.vc w) (C.vc w')) (C.vc_lt _)
    (Nat.xor_lt_two_pow (n := 6) (C.vc_lt w) (C.vc_lt w')) ?_
  intro j hj
  have h := C.kent_vc (w + w') ⟨j, hj⟩
  have h1 := C.kent_vc w ⟨j, hj⟩
  have h2 := C.kent_vc w' ⟨j, hj⟩
  rw [kent_xor, h1, h2, h]
  exact C.enc_add _ _

theorem mc_one : C.mc (1 : Matrix (Fin 3) (Fin 3) K) = kid := by
  unfold KCoding.mc
  simp [C.enc_zero, C.enc_one]
  rfl

theorem mc_surj {c : Nat} (hc : c < 2 ^ 18) : ∃ A : Matrix (Fin 3) (Fin 3) K, C.mc A = c := by
  refine ⟨Matrix.of fun i j => C.dec (kent c (6 * i.val + 2 * j.val)), ?_⟩
  apply eq_of_kent_eq_fin (C.mc_lt _) hc
  intro i j
  rw [C.kent_mc]
  exact C.enc_dec _ (kent_lt4 _ _)

theorem mc_mul (A B : Matrix (Fin 3) (Fin 3) K) : C.mc (A * B) = kmul (C.mc A) (C.mc B) := by
  apply eq_of_kent_eq_fin (C.mc_lt _) (kmul_lt _ _)
  intro i j
  have a0 : kent (C.mc A) (6 * i.val) = C.enc (A i 0) := by simpa using C.kent_mc A i 0
  have a1 : kent (C.mc A) (6 * i.val + 2) = C.enc (A i 1) := by simpa using C.kent_mc A i 1
  have a2 : kent (C.mc A) (6 * i.val + 4) = C.enc (A i 2) := by simpa using C.kent_mc A i 2
  have b0 : kent (C.mc B) (2 * j.val) = C.enc (B 0 j) := by simpa using C.kent_mc B 0 j
  have b1 : kent (C.mc B) (6 + 2 * j.val) = C.enc (B 1 j) := by simpa using C.kent_mc B 1 j
  have b2 : kent (C.mc B) (12 + 2 * j.val) = C.enc (B 2 j) := by simpa using C.kent_mc B 2 j
  rw [C.kent_mc, kent_kmul _ _ i.val j.val i.2 j.2, a0, a1, a2, b0, b1, b2, ← C.enc_mul, ← C.enc_mul, ← C.enc_mul,
    ← C.enc_add, ← C.enc_add]
  congr 1
  simp [Matrix.mul_apply, Fin.sum_univ_three]

theorem mc_apply (A : Matrix (Fin 3) (Fin 3) K) (w : Fin 3 → K) :
    C.vc (A *ᵥ w) = kapply (C.mc A) (C.vc w) := by
  refine eq_of_kent_eq6 (C.vc_lt _) (kapply_lt _ _) ?_
  intro j hj
  obtain ⟨i, rfl⟩ : ∃ i : Fin 3, i.val = j := ⟨⟨j, hj⟩, rfl⟩
  have a0 : kent (C.mc A) (6 * i.val) = C.enc (A i 0) := by simpa using C.kent_mc A i 0
  have a1 : kent (C.mc A) (6 * i.val + 2) = C.enc (A i 1) := by simpa using C.kent_mc A i 1
  have a2 : kent (C.mc A) (6 * i.val + 4) = C.enc (A i 2) := by simpa using C.kent_mc A i 2
  have v0 : kent (C.vc w) 0 = C.enc (w 0) := by simpa using C.kent_vc w 0
  have v1 : kent (C.vc w) 2 = C.enc (w 1) := by simpa using C.kent_vc w 1
  have v2 : kent (C.vc w) 4 = C.enc (w 2) := by simpa using C.kent_vc w 2
  rw [C.kent_vc, kent_kapply _ _ i.val i.2]
  unfold kX fmul
  rw [a0, a1, a2, v0, v1, v2, ← C.enc_mul, ← C.enc_mul, ← C.enc_mul, ← C.enc_add, ← C.enc_add]
  congr 1
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three]

theorem mc_smul_one (c : K) : C.mc (c • (1 : Matrix (Fin 3) (Fin 3) K)) = C.enc c * 65793 := by
  unfold KCoding.mc
  simp [C.enc_zero]
  omega

theorem mc_scalar (A : Matrix (Fin 3) (Fin 3) K) :
    isScalK (C.mc A) = true ↔ ∃ c : K, c ≠ 0 ∧ A = c • (1 : Matrix (Fin 3) (Fin 3) K) := by
  constructor
  · intro h
    have key : ∀ k, 0 < k → k < 4 → C.mc A = k * 65793 → ∃ c : K, c ≠ 0 ∧ A = c • (1 : Matrix (Fin 3) (Fin 3) K) := by
      intro k hk0 hk4 hk
      refine ⟨C.dec k, ?_, C.mc_inj (by rw [hk, C.mc_smul_one, C.enc_dec k hk4])⟩
      intro h0
      have := C.enc_dec k hk4
      rw [h0, C.enc_zero] at this
      omega
    unfold isScalK at h
    simp only [Bool.or_eq_true] at h
    rcases h with (h | h) | h
    · exact key 1 (by omega) (by omega) (by rw [Nat.eq_of_beq_eq_true h]; rfl)
    · exact key 2 (by omega) (by omega) (by rw [Nat.eq_of_beq_eq_true h]; rfl)
    · exact key 3 (by omega) (by omega) (by rw [Nat.eq_of_beq_eq_true h]; rfl)
  · rintro ⟨c, hc, rfl⟩
    rw [C.mc_smul_one]
    have h0 : C.enc c ≠ 0 := by
      intro h0
      have := C.dec_enc c
      rw [h0, C.dec_zero] at this
      exact hc this.symm
    have h4 := C.enc_lt c
    generalize C.enc c = e at h0 h4 ⊢
    interval_cases e <;> first | exact absurd rfl h0 | decide

end KCoding

theorem expand_kmul {a b : Nat} (ha : a < 2 ^ 18) (hb : b < 2 ^ 18) :
    expand (kmul a b) = bmul (expand a) (expand b) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hK : Nat.card (GaloisField 2 2) = 4 := by
    rw [GaloisField.card 2 2 (by norm_num)]
    norm_num
  obtain ⟨C⟩ := exists_kcoding (GaloisField 2 2) hK
  obtain ⟨A, rfl⟩ := C.mc_surj ha
  obtain ⟨B, rfl⟩ := C.mc_surj hb
  apply toM_inj (expand_lt _) (bmul_lt _ _)
  rw [toM_bmul, Matrix.ext_iff_mulVec]
  intro v
  obtain ⟨v', hv', rfl⟩ := vecOfBits_surj v
  obtain ⟨w, rfl⟩ := C.vc_surj hv'
  rw [← Matrix.mulVec_mulVec, toM_expand_mulVec, toM_expand_mulVec, toM_expand_mulVec, ← C.mc_mul, ← C.mc_apply,
    ← C.mc_apply, ← C.mc_apply, Matrix.mulVec_mulVec]

end CFSG.Quasithin.D35ValChk

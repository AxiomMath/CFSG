module

public import CFSG.Sporadic.Ly.KeySpec
public import CFSG.Sporadic.Th.TableSpec
public import CFSG.Sporadic.Ly.RREF

public section

namespace CFSG.Sporadic.Ly

open Native Matrix Finset
open CFSG.Sporadic.He.Native (toMat fold_add_eq_sum)
open CFSG.Sporadic.Th (allIn_eq_true)

@[expose] def mat7 (X : Array ℕ) : Matrix (Fin 7) (Fin 7) (ZMod 5) :=
  Matrix.of fun a b => (X[7 * a.val + b.val]! : ZMod 5)

theorem ofFn49_get {f : Fin 49 → ℕ} {a b : ℕ} (ha : a < 7) (hb : b < 7) :
    (Array.ofFn f)[7 * a + b]! = f ⟨7 * a + b, by omega⟩ := by
  rw [getElem!_pos _ (7 * a + b) (by simp; omega), Array.getElem_ofFn]

theorem fold7_cast (f : ℕ → ℕ) :
    ((Nat.fold 7 (fun l _ acc => acc + f l) 0 : ℕ) : ZMod 5) = ∑ l : Fin 7, (f l.val : ZMod 5) := by
  rw [fold_add_eq_sum, Nat.cast_sum, ← Fin.sum_univ_eq_sum_range (fun l => (f l : ZMod 5)) 7]

theorem mat7_mul7 (X Y : Array ℕ) : mat7 (mul7 X Y) = mat7 X * mat7 Y := by
  ext a b
  rw [mat7, of_apply, mul_apply]
  unfold mul7
  rw [ofFn49_get a.isLt b.isLt]
  simp only
  rw [show (7 * a.val + b.val) / 7 = a.val by omega, show (7 * a.val + b.val) % 7 = b.val by omega,
    ZMod.natCast_mod, fold7_cast]
  refine Finset.sum_congr rfl fun l _ => ?_
  simp only [mat7, of_apply]
  push_cast
  ring

theorem mat7_congr7 (P S : Array ℕ) : mat7 (congr7 P S) = mat7 P * mat7 S * (mat7 P)ᵀ := by
  ext a b
  rw [← mat7_mul7, mat7, of_apply, mul_apply]
  unfold congr7
  rw [ofFn49_get a.isLt b.isLt]
  simp only
  rw [show (7 * a.val + b.val) / 7 = a.val by omega, show (7 * a.val + b.val) % 7 = b.val by omega,
    ZMod.natCast_mod, fold7_cast]
  refine Finset.sum_congr rfl fun l _ => ?_
  simp only [mat7, of_apply, transpose_apply]
  push_cast
  ring

theorem keyS_get (key : ByteArray) {t : ℕ} (ht : t < 49) :
    (keyS key)[t]! = keyDigit key (777 + t) := by
  unfold keyS
  rw [getElem!_pos _ t (by simp; omega), Array.getElem_ofFn]
  simp only
  rw [show 777 + t = 3 * (259 + t / 3) + t % 3 by omega,
    keyDigit_byte key (259 + t / 3) (t % 3) (Nat.mod_lt t (by norm_num : 3 > 0))]
  have h3 := Nat.mod_lt t (show 0 < 3 by norm_num)
  interval_cases h : t % 3
  · simp
  · simp
  · simp only [show (5 : ℕ) ^ 2 = 25 by norm_num, ite_eq_right (show ¬ (2 = 0) by norm_num),
      ite_eq_right (show ¬ (2 = 1) by norm_num)]

theorem mat7_keyS (key : ByteArray) : mat7 (keyS key) = keyC key := by
  ext a b
  rw [mat7, of_apply, keyC, of_apply, keyS_get key (by omega)]
  congr 2
  ring

theorem fold_add_lane_le (f : ℕ → W14) (B : ℕ) :
    ∀ n, n * B < 256 → (∀ g < n, ∀ i < 112, (f g).lane i ≤ B) → ∀ i < 112,
      (Nat.fold n (fun g _ acc => acc.add (f g)) W14.zero).lane i =
        ∑ g ∈ range n, (f g).lane i ∧
      (Nat.fold n (fun g _ acc => acc.add (f g)) W14.zero).lane i ≤ n * B := by
  intro n
  induction n with
  | zero => intro _ _ i _; simp [W14.lane_zero]
  | succ n ih =>
    intro hn hf i hi
    rw [Nat.fold_succ]
    have hnB : n * B < 256 := lt_of_le_of_lt (Nat.mul_le_mul_right B (Nat.le_succ n)) hn
    have ih' := ih hnB (fun g hg => hf g (by omega))
    have hb : ∀ j < 112, (Nat.fold n (fun g _ acc => acc.add (f g)) W14.zero).lane j +
        (f n).lane j < 256 := by
      intro j hj
      have h1 := (ih' j hj).2
      have h2 := hf n (by omega) j hj
      have : n * B + B = (n + 1) * B := by ring
      omega
    rw [W14.lane_add hb hi, (ih' i hi).1, Finset.sum_range_succ]
    refine ⟨rfl, ?_⟩
    have h1 := (ih' i hi).2
    have h2 := hf n (by omega) i hi
    rw [← (ih' i hi).1]
    have : n * B + B = (n + 1) * B := by ring
    omega

theorem actYs_size (T : Array W14) (key : ByteArray) : (actYs T key).size = 7 := by
  simp [actYs]

theorem actYs_get (T : Array W14) (key : ByteArray) {k : ℕ} (hk : k < 7) :
    (actYs T key)[k]! = (rowProd T key k).red := by
  unfold actYs
  rw [getElem!_pos _ k (by simp [hk]), Array.getElem_ofFn]

theorem actYs_lane_le (M : Array (Array ℕ)) (key : ByteArray) {k i : ℕ} (hk : k < 7)
    (hi : i < 112) : ((actYs (frTable M) key)[k]!).lane i ≤ 4 := by
  rw [actYs_get _ _ hk, W14.lane_red _ hi]; omega

theorem actYs_lane_cast (M : Array (Array ℕ)) {key : ByteArray} (hv : ValidKey key) (k : Fin 7)
    (i : Fin 111) :
    (((actYs (frTable M) key)[k.val]!).lane i.val : ZMod 5) = (toMat 5 111 M * keyU key) i k := by
  rw [actYs_get _ _ k.isLt, W14.lane_red _ (by omega), ZMod.natCast_mod,
    rowProd_lane_cast M hv k i]

theorem pivMat_get (ys : Array W14) (piv : Array ℕ) {m k : ℕ} (hm : m < 7) (hk : k < 7) :
    (pivMat ys piv)[7 * m + k]! = ys[k]!.lane piv[m]! % 5 := by
  unfold pivMat
  rw [ofFn49_get hm hk]
  simp only
  rw [show (7 * m + k) % 7 = k by omega, show (7 * m + k) / 7 = m by omega]

theorem combine_size (ys : Array W14) (Pinv : Array ℕ) : (combine ys Pinv).size = 7 := by
  simp [combine]

theorem combine_get (ys : Array W14) (Pinv : Array ℕ)
    (hys : ∀ k < 7, ∀ i < 112, (ys[k]!).lane i ≤ 4) {m j : ℕ} (hm : m < 7) (hj : j < 112) :
    ((combine ys Pinv)[m]!.get! j).toNat =
      (∑ k ∈ range 7, (Pinv[7 * k + m]! % 5) * (ys[k]!).lane j) % 5 := by
  unfold combine
  rw [getElem!_pos _ m (by simp [hm]), Array.getElem_ofFn]
  simp only
  rw [W14.digits_get _ hj]
  have hc : ∀ k, (UInt64.ofNat (Pinv[7 * k + m]! % 5)).toNat = Pinv[7 * k + m]! % 5 := by
    intro k
    rw [UInt64.toNat_ofNat_of_lt' (by
      have := Nat.mod_lt (Pinv[7 * k + m]!) (show 0 < 5 by norm_num)
      unfold UInt64.size; omega)]
  have hsm : ∀ k < 7, ∀ i < 112,
      (W14.smul (UInt64.ofNat (Pinv[7 * k + m]! % 5)) ys[k]!).lane i ≤ 16 := by
    intro k hk i hi
    rw [W14.lane_smul (fun j hj => by
      rw [hc]
      have := hys k hk j hj
      have := Nat.mod_lt (Pinv[7 * k + m]!) (show 0 < 5 by norm_num)
      nlinarith) hi, hc]
    have := hys k hk i hi
    have := Nat.mod_lt (Pinv[7 * k + m]!) (show 0 < 5 by norm_num)
    nlinarith
  rw [(fold_add_lane_le (fun k => W14.smul (UInt64.ofNat (Pinv[7 * k + m]! % 5)) ys[k]!) 16 7
    (by norm_num) hsm j hj).1]
  congr 1
  refine Finset.sum_congr rfl fun k hk => ?_
  have hk' := Finset.mem_range.1 hk
  rw [W14.lane_smul (fun i hi => by
    rw [hc]
    have := hys k hk' i hi
    have := Nat.mod_lt (Pinv[7 * k + m]!) (show 0 < 5 by norm_num)
    nlinarith) hj, hc]

theorem rrefOK_spec {ds : Array ByteArray} {piv : Array ℕ} (h : rrefOK ds piv = true) :
    piv.size = 7 ∧ ds.size = 7 ∧ (∀ m < 7, piv[m]! < 111 ∧ (m + 1 = 7 ∨ piv[m]! < piv[m + 1]!)) ∧
      (∀ m < 7, ∀ l < 7, (ds[m]!.get! piv[l]!).toNat = if l = m then 1 else 0) ∧
      ∀ m < 7, ∀ j < piv[m]!, (ds[m]!.get! j).toNat = 0 := by
  unfold rrefOK at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨h1, h2⟩, -⟩, h4⟩, h5⟩, h6⟩ := h
  refine ⟨h1, h2, fun m hm => ?_, fun m hm l hl => ?_, fun m hm j hj => ?_⟩
  · have := (allIn_eq_true.1 h4) m (Nat.zero_le _) hm
    simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true, beq_iff_eq] at this
    exact this
  · have := (allIn_eq_true.1 ((allIn_eq_true.1 h5) m (Nat.zero_le _) hm)) l (Nat.zero_le _) hl
    simp only [beq_iff_eq] at this
    rw [this]
  · have := (allIn_eq_true.1 ((allIn_eq_true.1 h6) m (Nat.zero_le _) hm)) j (Nat.zero_le _) hj
    simpa using this

theorem pivFun_strictMono {f : Fin 7 → Fin 111} (h : ∀ m : Fin 7, ∀ hm : m.val + 1 < 7,
    f m < f ⟨m.val + 1, hm⟩) : StrictMono f := by
  refine Fin.strictMono_iff_lt_succ.2 fun i => ?_
  have hi : i.castSucc.val + 1 < 7 := by have := i.isLt; simp only [Fin.val_castSucc]; omega
  have e : (⟨i.castSucc.val + 1, hi⟩ : Fin 7) = i.succ := Fin.ext (by simp)
  have := h i.castSucc hi
  rwa [e] at this

theorem keyU_encode (us : Array ByteArray) (s : Array ℕ) (j : Fin 111) (m : Fin 7) :
    keyU (encodeDigits (keyFun us s)) j m = ((us[m.val]!.get! j.val).toNat : ZMod 5) := by
  rw [keyU, of_apply, keyDigit_encodeDigits _ (by omega), ZMod.natCast_mod]
  unfold keyFun
  rw [ite_eq_left (by omega), show (111 * m.val + j.val) / 111 = m.val by omega,
    show (111 * m.val + j.val) % 111 = j.val by omega]

theorem keyC_encode (us : Array ByteArray) (s : Array ℕ) :
    keyC (encodeDigits (keyFun us s)) = mat7 s := by
  ext a b
  rw [keyC, of_apply, keyDigit_encodeDigits _ (by omega), ZMod.natCast_mod, mat7, of_apply]
  unfold keyFun
  rw [ite_eq_right (by omega), ite_eq_left (by omega),
    show 777 + 7 * a.val + b.val - 777 = 7 * a.val + b.val by omega]

theorem actKey_spec (M : Array (Array ℕ)) {key key' : ByteArray} (hv : ValidKey key)
    (h : actKey (frTable M) key = some key') :
    ValidKey key' ∧ (∃ p, IsRREF (keyU key') p) ∧
      ∃ P Pi : Matrix (Fin 7) (Fin 7) (ZMod 5), P * Pi = 1 ∧
        keyU key' * P = toMat 5 111 M * keyU key ∧ keyC key' = P * keyC key * Pᵀ := by
  unfold actKey at h
  simp only at h
  split at h
  next hr =>
    have hk' := (Option.some.inj h).symm
    subst hk'
    set ys := actYs (frTable M) key with hys
    set piv := pivots (ys.map W14.digits) with hpiv
    set P := pivMat ys piv with hP
    set us := combine ys (inv7 P) with hus
    obtain ⟨-, -, hpb, hid, hz⟩ := rrefOK_spec hr
    have hylane : ∀ k < 7, ∀ i < 112, (ys[k]!).lane i ≤ 4 :=
      fun k hk i hi => actYs_lane_le M key hk hi
    let pf : Fin 7 → Fin 111 := fun m => ⟨piv[m.val]!, (hpb m.val m.isLt).1⟩
    let Pim : Matrix (Fin 7) (Fin 7) (ZMod 5) :=
      Matrix.of fun k m => ((inv7 P)[7 * k.val + m.val]! : ZMod 5)
    have hU' : keyU (encodeDigits (keyFun us (congr7 P (keyS key)))) =
        toMat 5 111 M * keyU key * Pim := by
      ext j m
      rw [keyU_encode, combine_get ys (inv7 P) hylane m.isLt (by omega), ZMod.natCast_mod,
        Nat.cast_sum, mul_apply]
      rw [← Fin.sum_univ_eq_sum_range
        (fun k => (((inv7 P)[7 * k + m.val]! % 5 * (ys[k]!).lane j.val : ℕ) : ZMod 5)) 7]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [Nat.cast_mul, ZMod.natCast_mod, hys, actYs_lane_cast M hv k j]
      simp only [Pim, of_apply]
      ring
    have hPm : ∀ m k : Fin 7, mat7 P m k = (toMat 5 111 M * keyU key) (pf m) k := by
      intro m k
      simp only [mat7, of_apply]
      rw [hP, pivMat_get ys piv m.isLt k.isLt, ZMod.natCast_mod, hys]
      exact actYs_lane_cast M hv k (pf m)
    have hR : IsRREF (keyU (encodeDigits (keyFun us (congr7 P (keyS key))))) pf := by
      refine ⟨pivFun_strictMono fun m hm => ?_, fun l m => ?_, fun m j hj => ?_⟩
      · rcases (hpb m.val m.isLt).2 with h7 | hlt
        · omega
        · exact Fin.mk_lt_mk.2 hlt
      · rw [keyU_encode]
        show ((us[m.val]!.get! piv[l.val]!).toNat : ZMod 5) = _
        rw [hid m.val m.isLt l.val l.isLt]
        split_ifs with h1 h2 h2 <;> simp_all [Fin.ext_iff]
      · rw [keyU_encode]
        have hj' : j.val < piv[m.val]! := Fin.lt_def.1 hj
        rw [hz m.val m.isLt j.val hj']; simp
    have hPP : mat7 P * Pim = 1 := by
      ext l m
      have e := hR.2.1 l m
      rw [hU', mul_apply] at e
      rw [mul_apply, one_apply, ← e]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [hPm l k]
    have hPP' : Pim * mat7 P = 1 := mul_eq_one_comm.1 hPP
    refine ⟨validKey_encodeDigits _, ⟨pf, hR⟩, mat7 P, Pim, hPP, ?_, ?_⟩
    · rw [hU', Matrix.mul_assoc, hPP', Matrix.mul_one]
    · rw [keyC_encode, mat7_congr7, mat7_keyS]
  next => exact absurd h (by simp)

theorem keyT_actKey (M : Array (Array ℕ)) {key key' : ByteArray} (hv : ValidKey key)
    (h : actKey (frTable M) key = some key') :
    keyT key' = toMat 5 111 M * keyT key * (toMat 5 111 M)ᵀ := by
  obtain ⟨-, -, P, Pi, -, hU, hC⟩ := actKey_spec M hv h
  unfold keyT
  rw [hC]
  calc keyU key' * (P * keyC key * Pᵀ) * (keyU key')ᵀ =
        (keyU key' * P) * keyC key * (keyU key' * P)ᵀ := by
        rw [Matrix.transpose_mul]; simp only [Matrix.mul_assoc]
    _ = toMat 5 111 M * (keyU key * keyC key * (keyU key)ᵀ) * (toMat 5 111 M)ᵀ := by
        rw [hU, Matrix.transpose_mul]; simp only [Matrix.mul_assoc]

theorem keyC_inv_actKey (M : Array (Array ℕ)) {key key' : ByteArray} (hv : ValidKey key)
    (h : actKey (frTable M) key = some key') {Si : Matrix (Fin 7) (Fin 7) (ZMod 5)}
    (hS : keyC key * Si = 1) : ∃ Si', keyC key' * Si' = 1 := by
  obtain ⟨-, -, P, Pi, hPP, -, hC⟩ := actKey_spec M hv h
  have hPP' : Pi * P = 1 := mul_eq_one_comm.1 hPP
  refine ⟨Piᵀ * Si * Pi, ?_⟩
  rw [hC]
  calc P * keyC key * Pᵀ * (Piᵀ * Si * Pi) = P * keyC key * (Pi * P)ᵀ * Si * Pi := by
        rw [Matrix.transpose_mul]; simp only [Matrix.mul_assoc]
    _ = 1 := by rw [hPP', Matrix.transpose_one, Matrix.mul_one, Matrix.mul_assoc P, hS,
          Matrix.mul_one, hPP]

end CFSG.Sporadic.Ly

module

public import Mathlib.Data.Fintype.Perm
public import Mathlib.Data.List.Permutation
import CFSG.Certificates.Kernel.Common.Harness
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF84K

open Equiv

@[expose] def rd (c i : ℕ) : ℕ := Nat.land (Nat.shiftRight c (Nat.mul 4 i)) 15

@[expose] noncomputable def encF (a : ℕ → ℕ) (k : ℕ) : ℕ :=
  Nat.rec (motive := fun _ => ℕ) 0 (fun i acc => Nat.add acc (Nat.shiftLeft (a i) (Nat.mul 4 i))) k

theorem encF_zero (a : ℕ → ℕ) : encF a 0 = 0 := rfl

theorem encF_succ (a : ℕ → ℕ) (k : ℕ) : encF a (k + 1) = encF a k + a k * 16 ^ k := by
  change encF a k + a k <<< (4 * k) = _
  rw [Nat.shiftLeft_eq, pow_mul]
  norm_num

theorem encF_succ' (a : ℕ → ℕ) (k : ℕ) :
    encF a (k + 1) = a 0 + encF (fun i => a (i + 1)) k * 16 := by
  induction k with
  | zero => simp [encF_succ, encF_zero]
  | succ k ih =>
    rw [encF_succ a (k + 1), ih, encF_succ (fun i => a (i + 1)) k, pow_succ]
    ring

theorem rd_eq (c i : ℕ) : rd c i = c / 16 ^ i % 16 := by
  change (c >>> (4 * i)) &&& (2 ^ 4 - 1) = _
  rw [Nat.and_two_pow_sub_one_eq_mod, Nat.shiftRight_eq_div_pow, pow_mul]
  norm_num

theorem encF_lt {a : ℕ → ℕ} {k : ℕ} (h : ∀ i < k, a i < 16) : encF a k < 16 ^ k := by
  induction k with
  | zero => simp [encF_zero]
  | succ k ih =>
    rw [encF_succ, pow_succ]
    have h1 := ih fun i hi => h i (by omega)
    have h2 : a k * 16 ^ k ≤ 15 * 16 ^ k := Nat.mul_le_mul_right _ (by have := h k (by omega); omega)
    linarith

theorem rd_encF {a : ℕ → ℕ} {k : ℕ} (h : ∀ i < k, a i < 16) {j : ℕ} (hj : j < k) :
    rd (encF a k) j = a j := by
  rw [rd_eq]
  induction k with
  | zero => omega
  | succ k ih =>
    rw [encF_succ]
    rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | rfl
    · have ih' := ih (fun i hi => h i (by omega)) hj
      have hk : a k * 16 ^ k = 16 ^ j * (16 * (16 ^ (k - j - 1) * a k)) := by
        have e : 16 ^ k = 16 ^ j * 16 ^ (k - j - 1) * 16 := by
          rw [← pow_add, ← pow_succ]
          congr 1
          omega
        rw [e]
        ring
      rw [hk, Nat.add_mul_div_left _ _ (by positivity), Nat.add_mul_mod_self_left, ih']
    · rw [mul_comm, Nat.add_mul_div_left _ _ (by positivity),
        Nat.div_eq_of_lt (encF_lt fun i hi => h i (by omega)), zero_add,
        Nat.mod_eq_of_lt (h j (by omega))]

theorem encF_congr {a b : ℕ → ℕ} {k : ℕ} (h : ∀ i < k, a i = b i) : encF a k = encF b k := by
  induction k with
  | zero => rfl
  | succ k ih => rw [encF_succ, encF_succ, ih fun i hi => h i (by omega), h k (by omega)]

@[expose] noncomputable def enc (σ : Perm (Fin 8)) : ℕ :=
  encF (fun i => if h : i < 8 then (σ ⟨i, h⟩ : ℕ) else 0) 8

@[expose] noncomputable def mulK (c d : ℕ) : ℕ := encF (fun i => rd c (rd d i)) 8

theorem rd_enc (σ : Perm (Fin 8)) (i : Fin 8) : rd (enc σ) i = σ i := by
  rw [enc, rd_encF (fun j hj => by rw [dif_pos hj]; exact lt_of_lt_of_le (Fin.isLt _) (by norm_num))
    i.isLt]
  simp

theorem enc_mul (σ τ : Perm (Fin 8)) : enc (σ * τ) = mulK (enc σ) (enc τ) := by
  rw [mulK]
  conv_lhs => rw [enc]
  refine encF_congr fun i hi => ?_
  have h1 : rd (enc τ) i = τ ⟨i, hi⟩ := rd_enc τ ⟨i, hi⟩
  rw [dif_pos hi, Perm.mul_apply, h1, rd_enc σ]

theorem enc_inj {σ τ : Perm (Fin 8)} (h : enc σ = enc τ) : σ = τ :=
  Equiv.ext fun i => Fin.ext (by rw [← rd_enc σ i, ← rd_enc τ i, h])

theorem enc_lt (σ : Perm (Fin 8)) : enc σ < 2 ^ 32 := by
  have h := encF_lt (a := fun i => if h : i < 8 then (σ ⟨i, h⟩ : ℕ) else 0) (k := 8)
    (fun i hi => by rw [dif_pos hi]; exact lt_of_lt_of_le (Fin.isLt _) (by norm_num))
  rw [enc]
  calc _ < 16 ^ 8 := h
    _ = 2 ^ 32 := by norm_num

@[expose] def idK : ℕ := 1985229328

theorem enc_one : enc 1 = idK := by decide +kernel

@[expose] noncomputable def sqK (c : ℕ) : ℕ := mulK c c

@[expose] noncomputable def p8K (c : ℕ) : ℕ := sqK (sqK (sqK c))

theorem enc_pow8 (σ : Perm (Fin 8)) : enc (σ ^ 8) = p8K (enc σ) := by
  have : σ ^ 8 = (σ * σ) * (σ * σ) * ((σ * σ) * (σ * σ)) := by
    simp only [pow_succ, pow_zero, one_mul, mul_assoc]
  rw [this, enc_mul, enc_mul, enc_mul, p8K, sqK, sqK, sqK]

@[expose] noncomputable def encL (l : List ℕ) : ℕ :=
  List.rec (motive := fun _ => ℕ) 0 (fun a _ r => Nat.add a (Nat.shiftLeft r 4)) l

theorem encL_eq (l : List ℕ) : encL l = encF (fun i => l.getD i 0) l.length := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    change a + encL l <<< 4 = _
    rw [List.length_cons, encF_succ', ih, Nat.shiftLeft_eq]
    simp

@[expose] def permsL : List (List ℕ) := (List.range 8).permutations'

theorem enc_mem (σ : Perm (Fin 8)) : ∃ l ∈ permsL, encL l = enc σ := by
  refine ⟨List.ofFn fun i : Fin 8 => (σ i : ℕ), ?_, ?_⟩
  · rw [permsL, List.mem_permutations']
    refine (List.perm_ext_iff_of_nodup
      (List.nodup_ofFn.2 fun i j h => σ.injective (Fin.ext h)) List.nodup_range).2 fun a => ?_
    rw [List.mem_ofFn, List.mem_range]
    constructor
    · rintro ⟨i, rfl⟩
      exact (σ i).isLt
    · intro ha
      exact ⟨σ.symm ⟨a, ha⟩, by simp⟩
  · rw [encL_eq, List.length_ofFn, enc]
    refine encF_congr fun i hi => ?_
    rw [dif_pos hi, List.getD_eq_getElem?_getD, List.getElem?_ofFn]
    simp [hi]

@[expose] def ifB (b x y : Bool) : Bool := Bool.rec y x b

theorem ifB_true (x y : Bool) : ifB true x y = x := rfl

theorem ifB_false (x y : Bool) : ifB false x y = y := rfl

@[expose] noncomputable def allP (f : ℕ → Bool) (L : List (List ℕ)) : Bool :=
  List.rec (motive := fun _ => Bool) true (fun l _ r => ifB (f (encL l)) r false) L

theorem allP_sound {f : ℕ → Bool} {L : List (List ℕ)} (h : allP f L = true) :
    ∀ l ∈ L, f (encL l) = true := by
  induction L with
  | nil => simp
  | cons a L ih =>
    change ifB (f (encL a)) (allP f L) false = true at h
    cases ha : f (encL a)
    · rw [ha, ifB_false] at h
      exact absurd h Bool.false_ne_true
    · rw [ha, ifB_true] at h
      intro l hl
      rcases List.mem_cons.1 hl with rfl | hl
      · exact ha
      · exact ih h l hl

theorem forall_perm {f : ℕ → Bool} (h : allP f permsL = true) (σ : Perm (Fin 8)) :
    f (enc σ) = true := by
  obtain ⟨l, hl, e⟩ := enc_mem σ
  rw [← e]
  exact allP_sound h l hl

@[expose] noncomputable def memK (c : ℕ) (L : List ℕ) : Bool :=
  List.rec (motive := fun _ => Bool) false (fun a _ r => ifB (Nat.beq a c) true r) L

@[expose] noncomputable def anyK (f : ℕ → Bool) (L : List ℕ) : Bool :=
  List.rec (motive := fun _ => Bool) false (fun a _ r => ifB (f a) true r) L

theorem memK_sound {c : ℕ} {L : List ℕ} (h : memK c L = true) : c ∈ L := by
  induction L with
  | nil => exact absurd h Bool.false_ne_true
  | cons a L ih =>
    change ifB (Nat.beq a c) true (memK c L) = true at h
    cases ha : Nat.beq a c
    · rw [ha, ifB_false] at h
      exact List.mem_cons_of_mem _ (ih h)
    · rw [Nat.beq_eq] at ha
      rw [ha]
      exact List.mem_cons_self

theorem anyK_sound {f : ℕ → Bool} {L : List ℕ} (h : anyK f L = true) : ∃ a ∈ L, f a = true := by
  induction L with
  | nil => exact absurd h Bool.false_ne_true
  | cons a L ih =>
    change ifB (f a) true (anyK f L) = true at h
    cases ha : f a
    · rw [ha, ifB_false] at h
      obtain ⟨b, hb, e⟩ := ih h
      exact ⟨b, List.mem_cons_of_mem _ hb, e⟩
    · exact ⟨a, List.mem_cons_self, ha⟩

@[expose] noncomputable def zOf (c d t : Perm (Fin 8)) : List ℕ :=
  (List.range 3).flatMap fun i => (List.range 3).flatMap fun j =>
    [enc (c ^ i * d ^ j), enc (c ^ i * d ^ j * t)]

@[expose] noncomputable def cenB (C D : ℕ) (Z : List ℕ) (x : ℕ) : Bool :=
  ifB (Nat.beq (mulK x C) (mulK C x))
    (ifB (Nat.beq (mulK x D) (mulK D x)) (memK x Z) true) true

theorem cen_sound (c d t : Perm (Fin 8)) (C D : ℕ) (Z : List ℕ) (hC : enc c = C)
    (hD : enc d = D) (hZ : (zOf c d t == Z) = true) (h : allP (cenB C D Z) permsL = true) :
    ∀ z : Perm (Fin 8), z * c = c * z → z * d = d * z →
      ∃ i < 3, ∃ j < 3, (z = c ^ i * d ^ j ∨ z = c ^ i * d ^ j * t) := by
  intro z hzc hzd
  have hz := forall_perm h z
  have e1 : Nat.beq (mulK (enc z) C) (mulK C (enc z)) = true := by
    rw [Nat.beq_eq, ← hC, ← enc_mul, ← enc_mul, hzc]
  have e2 : Nat.beq (mulK (enc z) D) (mulK D (enc z)) = true := by
    rw [Nat.beq_eq, ← hD, ← enc_mul, ← enc_mul, hzd]
  rw [cenB, e1, ifB_true, e2, ifB_true] at hz
  have hm := memK_sound hz
  rw [← beq_iff_eq.1 hZ, zOf] at hm
  simp only [List.mem_flatMap, List.mem_range, List.mem_cons, List.not_mem_nil, or_false] at hm
  obtain ⟨i, hi, j, hj, hm⟩ := hm
  exact ⟨i, hi, j, hj, hm.imp enc_inj enc_inj⟩

@[expose] noncomputable def pairE (y : Perm (Fin 8)) : ℕ :=
  Nat.add (enc y) (Nat.shiftLeft (enc y⁻¹) 32)

@[expose] def loK (p : ℕ) : ℕ := Nat.land p 4294967295

@[expose] def hiK (p : ℕ) : ℕ := Nat.shiftRight p 32

theorem loK_pairE (y : Perm (Fin 8)) : loK (pairE y) = enc y := by
  change (enc y + enc y⁻¹ <<< 32) &&& (2 ^ 32 - 1) = _
  rw [Nat.and_two_pow_sub_one_eq_mod, Nat.shiftLeft_eq, Nat.add_mul_mod_self_right,
    Nat.mod_eq_of_lt (enc_lt y)]

theorem hiK_pairE (y : Perm (Fin 8)) : hiK (pairE y) = enc y⁻¹ := by
  change (enc y + enc y⁻¹ <<< 32) >>> 32 = _
  rw [Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq, Nat.add_mul_div_right _ _ (by positivity),
    Nat.div_eq_of_lt (enc_lt y), zero_add]

@[expose] noncomputable def notTwoB (x p : ℕ) : Bool :=
  ifB (Nat.beq (p8K (mulK x (mulK (mulK (loK p) x) (hiK p)))) idK) false true

@[expose] noncomputable def keyB (T : ℕ) (YP : List ℕ) (x : ℕ) : Bool :=
  ifB (Nat.beq (mulK x T) (mulK T x))
    (ifB (Nat.beq x idK) true
      (ifB (Nat.beq x T) true
        (ifB (Nat.beq (p8K x) idK) (anyK (notTwoB x) YP) true))) true

theorem key_sound (t : Perm (Fin 8)) (ys : List (Perm (Fin 8))) (T : ℕ) (YP : List ℕ)
    (hT : enc t = T) (hY : (ys.map pairE == YP) = true) (h : allP (keyB T YP) permsL = true) :
    ∀ x : Perm (Fin 8), x * t = t * x → x ^ 8 = 1 → x ≠ 1 → x ≠ t →
      ∃ y ∈ ys, (x * (y * x * y⁻¹)) ^ 8 ≠ 1 := by
  intro x hxt h8 h1 ht
  have hx := forall_perm h x
  have e1 : Nat.beq (mulK (enc x) T) (mulK T (enc x)) = true := by
    rw [Nat.beq_eq, ← hT, ← enc_mul, ← enc_mul, hxt]
  have e2 : Nat.beq (enc x) idK = false := Bool.eq_false_iff.2 fun hb =>
    h1 (enc_inj ((Nat.eq_of_beq_eq_true hb).trans enc_one.symm))
  have e3 : Nat.beq (enc x) T = false := Bool.eq_false_iff.2 fun hb =>
    ht (enc_inj ((Nat.eq_of_beq_eq_true hb).trans hT.symm))
  have e4 : Nat.beq (p8K (enc x)) idK = true := by
    rw [Nat.beq_eq, ← enc_pow8, h8, enc_one]
  rw [keyB, e1, ifB_true, e2, ifB_false, e3, ifB_false, e4, ifB_true] at hx
  obtain ⟨p, hp, hn⟩ := anyK_sound hx
  rw [← beq_iff_eq.1 hY, List.mem_map] at hp
  obtain ⟨y, hy, rfl⟩ := hp
  refine ⟨y, hy, fun e => ?_⟩
  rw [notTwoB, loK_pairE, hiK_pairE, ← enc_mul, ← enc_mul, ← enc_mul, ← enc_pow8, e,
    enc_one] at hn
  rw [Nat.beq_refl, ifB_true] at hn
  exact Bool.false_ne_true hn

@[expose] noncomputable def allK (f : ℕ → Bool) (L : List ℕ) : Bool :=
  List.rec (motive := fun _ => Bool) true (fun a _ r => ifB (f a) r false) L

theorem allK_sound {f : ℕ → Bool} {L : List ℕ} (h : allK f L = true) : ∀ a ∈ L, f a = true := by
  induction L with
  | nil => simp
  | cons a L ih =>
    change ifB (f a) (allK f L) false = true at h
    cases ha : f a
    · rw [ha, ifB_false] at h
      exact absurd h Bool.false_ne_true
    · rw [ha, ifB_true] at h
      intro b hb
      rcases List.mem_cons.1 hb with rfl | hb
      · exact ha
      · exact ih h b hb

theorem comm_sound (t : Perm (Fin 8)) (ys : List (Perm (Fin 8))) (T : ℕ) (YP : List ℕ)
    (hT : enc t = T) (hY : (ys.map pairE == YP) = true)
    (h : allK (fun p => Nat.beq (mulK (loK p) T) (mulK T (loK p))) YP = true) :
    ∀ y ∈ ys, y * t = t * y := by
  intro y hy
  have hp : pairE y ∈ YP := by
    rw [← beq_iff_eq.1 hY]
    exact List.mem_map_of_mem hy
  have e := Nat.eq_of_beq_eq_true (allK_sound h _ hp)
  rw [loK_pairE, ← hT, ← enc_mul, ← enc_mul] at e
  exact enc_inj e

set_option maxRecDepth 100000 in
theorem cen_check : allP (cenB 1985228833 1983201808 [1985229328, 1733571088, 1983201808,
    1731543568, 1984123408, 1732465168, 1985228833, 1733570593, 1983201313, 1731543073, 1984122913,
    1732464673, 1985229058, 1733570818, 1983201538, 1731543298, 1984123138, 1732464898])
    permsL = true := by
  quickRfl

set_option maxRecDepth 100000 in
theorem key_check : allP (keyB 1733571088 [8526493881164116001, 7445367247193981456,
    8526160806450053651, 8508480595045921361, 8526459800598610481, 8526475262480876306])
    permsL = true := by
  quickRfl

theorem comm_check : allK (fun p => Nat.beq (mulK (loK p) 1733571088) (mulK 1733571088 (loK p)))
    [8526493881164116001, 7445367247193981456, 8526160806450053651, 8508480595045921361,
      8526459800598610481, 8526475262480876306] = true := by
  quickRfl

theorem ofFn_surj (l : List (Fin 8)) (hl : l ∈ (List.finRange 8).permutations') :
    ∃ σ : Perm (Fin 8), List.ofFn (fun i => σ i) = l := by
  have hp := List.mem_permutations'.1 hl
  have hlen : l.length = 8 := by rw [hp.length_eq, List.length_finRange]
  have hnd : l.Nodup := hp.nodup_iff.2 (List.nodup_finRange 8)
  let f : Fin 8 → Fin 8 := fun i => l[i.val]'(by rw [hlen]; exact i.isLt)
  have hf : Function.Injective f := fun i j h => Fin.ext (hnd.getElem_inj_iff.1 h)
  refine ⟨Equiv.ofBijective f (Finite.injective_iff_bijective.1 hf), ?_⟩
  refine List.ext_getElem (by rw [List.length_ofFn, hlen]) fun n h1 h2 => ?_
  rw [List.getElem_ofFn]
  rfl

end CFSG.RankThree.PartTwo.Sec21.FF84K

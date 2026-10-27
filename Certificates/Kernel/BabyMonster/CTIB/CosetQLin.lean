module

public import Certificates.Kernel.BabyMonster.CTIB.CosetQStep

public section

namespace CertificateChecks.KernelBM.CTIB.CosetQ

open CFSG.KC.BM CFSG.KC.BM.CosetQ CFSG.Monster.B.CTIB.Native CertificateChecks.KernelBM.CTIB

set_option exponentiation.threshold 1024

theorem andB_true {a b : Bool} : andB a b = true ↔ a = true ∧ b = true := by
  cases a <;> cases b <;> decide

theorem notB_true {a : Bool} : notB a = true ↔ a = false := by
  cases a <;> decide

theorem beq_true {a b : ℕ} : Nat.beq a b = true ↔ a = b :=
  ⟨Nat.eq_of_beq_eq_true, fun h => h ▸ Nat.beq_refl a⟩

theorem blt_true {a b : ℕ} : Nat.blt a b = true ↔ a < b := Iff.of_eq Nat.blt_eq

theorem ble_true {a b : ℕ} : Nat.ble a b = true ↔ a ≤ b := Iff.of_eq Nat.ble_eq

theorem allLt_true {n : ℕ} {f : ℕ → Bool} : allLt n f = true ↔ ∀ i < n, f i = true := by
  induction n with
  | zero => exact ⟨fun _ i hi => absurd hi (Nat.not_lt_zero i), fun _ => rfl⟩
  | succ n ih =>
    change andB (allLt n f) (f n) = true ↔ _
    rw [andB_true, ih]
    constructor
    · rintro ⟨h1, h2⟩ i hi
      rcases Nat.lt_succ_iff_lt_or_eq.1 hi with h | rfl
      · exact h1 i h
      · exact h2
    · intro h
      exact ⟨fun i hi => h i (Nat.lt_succ_of_lt hi), h n (Nat.lt_succ_self n)⟩

theorem brec_eq {α : Sort _} (x y : α) (b : Bool) :
    Bool.rec (motive := fun _ => α) x y b = if b = true then y else x := by
  cases b <;> rfl

@[expose] def halfX (a n : ℕ) : ℕ := Nat.xor (Nat.land a (2 ^ n - 1)) (Nat.shiftRight a n)

theorem halfX_lt {a n : ℕ} (h : a < 2 ^ (2 * n)) : halfX a n < 2 ^ n := by
  refine Nat.xor_lt_two_pow (Nat.and_lt_two_pow _ (Nat.sub_lt (Nat.two_pow_pos n) Nat.one_pos)) ?_
  change a >>> n < 2 ^ n
  rw [Nat.shiftRight_eq_div_pow, Nat.div_lt_iff_lt_mul (Nat.two_pow_pos n), ← Nat.pow_add,
    ← Nat.two_mul]
  exact h

theorem fold5_eq (x : ℕ) :
    fold5 x = halfX (halfX (halfX (halfX (halfX x 512) 256) 128) 64) 32 := rfl

theorem xorFields_lt (T v : ℕ) : xorFields T v < 2 ^ 32 := by
  rw [xorFields_eq, fold5_eq]
  have h0 : Nat.land T (Nat.mul (Nat.land (Nat.mul v SPR31) S32) 4294967295) < 2 ^ 1024 := by
    refine lt_of_le_of_lt Nat.and_le_right (lt_of_le_of_lt (Nat.mul_le_mul_right _
      Nat.and_le_right) ?_)
    decide +kernel
  exact halfX_lt (halfX_lt (halfX_lt (halfX_lt (halfX_lt h0))))

theorem xorFields_xor (T : ℕ) {u v : ℕ} (hu : u < 2 ^ 22) (hv : v < 2 ^ 22) :
    xorFields T (u ^^^ v) = xorFields T u ^^^ xorFields T v := by
  have huv : u ^^^ v < 2 ^ 22 := Nat.xor_lt_two_pow hu hv
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i < 32
  · rw [Nat.testBit_xor, xorFields_bit22 T huv hi, xorFields_bit22 T hu hi, xorFields_bit22 T hv hi,
      ← bx_xor]
    refine bx_congr fun m _ => ?_
    rw [Nat.testBit_xor]
    cases u.testBit m <;> cases v.testBit m <;> cases (fld32 T m).testBit i <;> rfl
  · have h1 : ∀ x, (xorFields T x).testBit i = false := fun x =>
      Nat.testBit_lt_two_pow (lt_of_lt_of_le (xorFields_lt T x)
        (Nat.pow_le_pow_right (by decide) (by omega)))
    rw [Nat.testBit_xor, h1, h1, h1]
    rfl

theorem xorFields_zero (T : ℕ) : xorFields T 0 = 0 := by
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i < 32
  · rw [xorFields_bit22 T (by decide) hi, Nat.zero_testBit]
    exact bx_false fun _ _ => by rw [Nat.zero_testBit, Bool.false_and]
  · rw [Nat.zero_testBit, Nat.testBit_lt_two_pow (lt_of_lt_of_le (xorFields_lt T 0)
      (Nat.pow_le_pow_right (by decide) (by omega)))]

theorem xorFields_two_pow (T : ℕ) {t : ℕ} (ht : t < 22) : xorFields T (2 ^ t) = fld32 T t := by
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i < 32
  · rw [xorFields_bit22 T (Nat.pow_lt_pow_right (by decide) ht) hi]
    simp only [Nat.testBit_two_pow]
    rw [bx_single (fun m => (fld32 T m).testBit i), decide_eq_true ht, Bool.true_and]
  · rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le (xorFields_lt T _)
      (Nat.pow_le_pow_right (by decide) (by omega))), fld32_eq, Nat.testBit_and,
      testBit_two_pow_sub_one', decide_eq_false hi, Bool.and_false]

@[expose] def xsum (g : ℕ → ℕ) (c : ℕ) : ℕ → ℕ
  | 0 => 0
  | m + 1 => xsum g c m ^^^ (if c.testBit m then g m else 0)

theorem mod_succ_xor (c m : ℕ) :
    c % 2 ^ (m + 1) = c % 2 ^ m ^^^ (if c.testBit m then 2 ^ m else 0) := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_xor, Nat.testBit_mod_two_pow, Nat.testBit_mod_two_pow]
  have e : (if c.testBit m then 2 ^ m else 0 : ℕ).testBit i = (c.testBit m && decide (m = i)) := by
    split_ifs with h
    · rw [Nat.testBit_two_pow, h, Bool.true_and]
    · rw [Nat.zero_testBit, Bool.eq_false_iff.2 h, Bool.false_and]
  rw [e]
  rcases Nat.lt_trichotomy i m with hi | rfl | hi
  · rw [decide_eq_true (by omega : i < m + 1), decide_eq_true hi,
      decide_eq_false (by omega : ¬ m = i)]
    simp
  · rw [decide_eq_true (by omega : i < i + 1), decide_eq_false (Nat.lt_irrefl i)]
    simp
  · rw [decide_eq_false (by omega : ¬ i < m + 1), decide_eq_false (by omega : ¬ i < m),
      decide_eq_false (by omega : ¬ m = i)]
    simp

theorem mod_lt22 (c : ℕ) {m : ℕ} (hm : m ≤ 22) : c % 2 ^ m < 2 ^ 22 :=
  lt_of_lt_of_le (Nat.mod_lt _ (Nat.two_pow_pos m)) (Nat.pow_le_pow_right (by decide) hm)

theorem additive_expand {f : ℕ → ℕ} (hf : ∀ u < 2 ^ 22, ∀ v < 2 ^ 22, f (u ^^^ v) = f u ^^^ f v)
    (h0 : f 0 = 0) {c : ℕ} (hc : c < 2 ^ 22) : f c = xsum (fun m => f (2 ^ m)) c 22 := by
  have key : ∀ m ≤ 22, f (c % 2 ^ m) = xsum (fun m => f (2 ^ m)) c m := by
    intro m
    induction m with
    | zero => intro _; rw [Nat.pow_zero, Nat.mod_one, h0]; rfl
    | succ m ih =>
      intro hm
      rw [mod_succ_xor, hf _ (mod_lt22 c (by omega)) _ (by
        split_ifs
        · exact Nat.pow_lt_pow_right (by decide) (by omega)
        · exact Nat.two_pow_pos 22), ih (by omega), xsum]
      split_ifs
      · rfl
      · rw [h0]
  rw [← key 22 (Nat.le_refl 22), Nat.mod_eq_of_lt hc]

theorem xorFields_xsum (T : ℕ) {c : ℕ} (hc : c < 2 ^ 22) :
    xorFields T c = xsum (fld32 T) c 22 := by
  rw [additive_expand (fun u hu v hv => xorFields_xor T hu hv) (xorFields_zero T) hc]
  have : ∀ m, xsum (fun m => xorFields T (2 ^ m)) c m = xsum (fld32 T) c m := by
    intro m
    induction m with
    | zero => rfl
    | succ m ih =>
      rw [xsum, xsum, ih]
      by_cases hm : m < 22
      · rw [xorFields_two_pow T hm]
      · have : c.testBit m = false := Nat.testBit_lt_two_pow
          (lt_of_lt_of_le hc (Nat.pow_le_pow_right (by decide) (by omega)))
        simp [this]
  exact this 22

theorem xsum_two_pow (c : ℕ) : ∀ m, xsum (fun m => 2 ^ m) c m = c % 2 ^ m
  | 0 => by rw [Nat.pow_zero, Nat.mod_one]; rfl
  | m + 1 => by rw [xsum, xsum_two_pow c m, mod_succ_xor]

theorem xsum_congr {g g' : ℕ → ℕ} (c : ℕ) (h : ∀ m < 22, g m = g' m) :
    ∀ m ≤ 22, xsum g c m = xsum g' c m
  | 0, _ => rfl
  | m + 1, hm => by rw [xsum, xsum, xsum_congr c h m (by omega), h m (by omega)]

theorem additive_ext {f f' : ℕ → ℕ} (hf : ∀ u < 2 ^ 22, ∀ v < 2 ^ 22, f (u ^^^ v) = f u ^^^ f v)
    (hf' : ∀ u < 2 ^ 22, ∀ v < 2 ^ 22, f' (u ^^^ v) = f' u ^^^ f' v) (h0 : f 0 = 0) (h0' : f' 0 = 0)
    (h : ∀ t < 22, f (2 ^ t) = f' (2 ^ t)) {c : ℕ} (hc : c < 2 ^ 22) : f c = f' c := by
  rw [additive_expand hf h0 hc, additive_expand hf' h0' hc]
  exact xsum_congr c h 22 (Nat.le_refl 22)

theorem xorFields_lt22 {T : ℕ} (hT : ∀ m < 22, fld32 T m < 2 ^ 22) (c : ℕ) :
    xorFields T (c % 2 ^ 22) < 2 ^ 22 := by
  apply Nat.lt_pow_two_of_testBit
  intro i hi
  by_cases hi' : i < 32
  · rw [xorFields_bit22 T (Nat.mod_lt _ (Nat.two_pow_pos 22)) hi']
    exact bx_false fun m hm => by
      rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le (hT m hm) (Nat.pow_le_pow_right (by decide) hi)),
        Bool.and_false]
  · exact Nat.testBit_lt_two_pow (lt_of_lt_of_le (xorFields_lt T _)
      (Nat.pow_le_pow_right (by decide) (by omega)))

theorem xorFields_lt22' {T : ℕ} (hT : ∀ m < 22, fld32 T m < 2 ^ 22) {c : ℕ} (hc : c < 2 ^ 22) :
    xorFields T c < 2 ^ 22 := by
  have := xorFields_lt22 hT c
  rwa [Nat.mod_eq_of_lt hc] at this

@[expose] def mv (G A : Array ℕ) (v : ℕ) : ℕ := autApply G A v % 2 ^ 22

theorem mv_bit (G A : Array ℕ) (v i : ℕ) :
    (mv G A v).testBit i = (decide (i < 22) && bx (fun s => v.testBit s && (A.getD s 0).testBit i) 22) := by
  rw [mv, Nat.testBit_mod_two_pow]
  by_cases hi : i < 22
  · rw [autApply_bit G A v hi]
  · simp [hi]

theorem mv_xor (G A : Array ℕ) (u v : ℕ) : mv G A (u ^^^ v) = mv G A u ^^^ mv G A v := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_xor, mv_bit, mv_bit, mv_bit, ← Bool.and_xor_distrib_left, ← bx_xor]
  congr 1
  refine bx_congr fun s _ => ?_
  rw [Nat.testBit_xor]
  cases u.testBit s <;> cases v.testBit s <;> cases (A.getD s 0).testBit i <;> rfl

theorem mv_zero (G A : Array ℕ) : mv G A 0 = 0 := by
  rw [mv, autApply_zero, Nat.zero_mod]

theorem mv_two_pow (G A : Array ℕ) {t : ℕ} (ht : t < 22) : mv G A (2 ^ t) = A.getD t 0 % 2 ^ 22 := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [mv_bit, Nat.testBit_mod_two_pow]
  simp only [Nat.testBit_two_pow]
  rw [bx_single (fun s => (A.getD s 0).testBit i), decide_eq_true ht, Bool.true_and]

theorem mv_lt (G A : Array ℕ) (v : ℕ) : mv G A v < 2 ^ 22 := Nat.mod_lt _ (Nat.two_pow_pos 22)

theorem mv_mod (G A : Array ℕ) (v : ℕ) : mv G A (v % 2 ^ 22) = mv G A v := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [mv_bit, mv_bit]
  congr 1
  exact bx_congr fun s hs => by rw [Nat.testBit_mod_two_pow, decide_eq_true hs, Bool.true_and]

theorem autApply_id (G : Array ℕ) {n : ℕ} (hn : n < 2 ^ 23) :
    autApply G (arrOf (id32 22)) n = n := by
  have hI : ∀ s < 22, (arrOf (id32 22)).getD s 0 = 2 ^ s := by
    have : ∀ s < 22, fld32 (id32 22) s = 2 ^ s := by decide +kernel
    exact fun s hs => by rw [arrOf_getD _ hs, this s hs]
  refine code_ext (autApply_lt _ _ _) hn (fun i hi => ?_) ?_
  · rw [autApply_bit G _ _ hi, bx_congr (g := fun s => decide (i = s) && n.testBit s)
      (fun s hs => by
        rw [hI s hs, Nat.testBit_two_pow, Bool.and_comm, decide_eq_decide.2 eq_comm]),
      bx_single, decide_eq_true hi, Bool.true_and]
  · rw [autApply_bit22, bx_false fun s hs => by
        rw [hI s hs, Nat.testBit_two_pow_of_ne (by omega), Bool.and_false], Bool.xor_false, quadA,
      dsum_false fun s hs j hj => by
        simp only [cc]
        rw [hI s hs, hI j hj, corr_two_pow G hj hs]
        simp only [gam]
        by_cases h : j < s
        · simp [h, Nat.lt_asymm h]
        · simp [h], Bool.xor_false]

structure Setup (G : Array ℕ) (AP k Bs T : ℕ) : Prop where
  symm : SymG G
  rel : RelOK G (arrOf AP)
  wf : ∀ i < 22, fld32 AP i < 2 ^ 23
  sq : ∀ n < 2 ^ 23, autApply G (arrOf AP) (autApply G (arrOf AP) n) = n
  bwf : ∀ t < 22, fld32 Bs t < 2 ^ 22
  twf : ∀ t < 22, fld32 T t < 2 ^ 22
  tb : ∀ c < 2 ^ 22, xorFields T (xorFields Bs c) = c
  bt : ∀ v < 2 ^ 22, xorFields Bs (xorFields T v) = v
  nm : ∀ v < 2 ^ 22, mv G (arrOf AP) v ^^^ v = xorFields Bs (xorFields T v >>> (22 - k))

theorem betaK_eq (G : Array ℕ) (hG : SymG G) (a b : ℕ) : betaK (loOf G) a b = (corr G a b).toNat := by
  have hb := betaK_bit G hG a b
  have hl := betaK_lt (loOf G) a b
  rcases Nat.lt_succ_iff.1 hl |> Nat.le_one_iff_eq_zero_or_eq_one.1 with h | h
  · rw [h, Nat.zero_testBit] at hb
    rw [h, ← hb]
    rfl
  · rw [h, Nat.testBit_one_zero] at hb
    rw [h, ← hb]
    rfl

theorem relOK_spec (G : Array ℕ) (hG : SymG G) {AP : ℕ} (h : relOK (loOf G) AP = true) :
    (∀ i < 22, fld32 AP i < 2 ^ 23) ∧ RelOK G (arrOf AP) := by
  unfold relOK at h
  rw [allLt_true] at h
  have e1 : ∀ i, Nat.shiftLeft 1 i = 2 ^ i := fun i => by
    rw [shl_eq, Nat.shiftLeft_eq, Nat.one_mul]
  have hb : ∀ x y : Bool, Nat.xor x.toNat y.toNat = (x ^^ y).toNat := by decide
  refine ⟨fun i hi => ?_, fun i hi => ?_, fun i hi j hj => ?_⟩
  · have := (andB_true.1 (h i hi)).1
    rw [beq_true, shr_eq, Nat.shiftRight_eq_div_pow, Nat.div_eq_zero_iff_lt (Nat.two_pow_pos 23)]
      at this
    exact this
  · have := (andB_true.1 (andB_true.1 (h i hi)).2).1
    rw [beq_true, betaK_eq G hG] at this
    simp only [cc]
    rw [arrOf_getD _ hi]
    cases hc : corr G (fld32 AP i) (fld32 AP i)
    · rfl
    · rw [hc] at this
      exact absurd this (by decide)
  · have := (andB_true.1 (andB_true.1 (h i hi)).2).2
    rw [allLt_true] at this
    have h2 := this j hj
    rw [beq_true, betaK_eq G hG, betaK_eq G hG, betaK_eq G hG, betaK_eq G hG, e1, e1, hb, hb,
      corr_two_pow G hi hj, corr_two_pow G hj hi] at h2
    simp only [cc]
    rw [arrOf_getD _ hi, arrOf_getD _ hj]
    revert h2
    cases corr G (fld32 AP i) (fld32 AP j) <;> cases corr G (fld32 AP j) (fld32 AP i) <;>
      cases gam G i j <;> cases gam G j i <;> decide

theorem setup_of {G : Array ℕ} (hG : SymG G) {AP k Bs T : ℕ}
    (h : setupOK (loOf G) AP k Bs T = true) : Setup G AP k Bs T := by
  unfold setupOK at h
  rw [andB_true, andB_true, beq_true, allLt_true] at h
  obtain ⟨hr, hsq, hb⟩ := h
  obtain ⟨hwf, hrel⟩ := relOK_spec G hG hr
  have e1 : ∀ i, Nat.shiftLeft 1 i = 2 ^ i := fun i => by
    rw [shl_eq, Nat.shiftLeft_eq, Nat.one_mul]
  have hb' : ∀ t < 22, xorFields T (fld32 Bs t) = 2 ^ t ∧ xorFields Bs (fld32 T t) = 2 ^ t ∧
      fld32 Bs t < 2 ^ 22 ∧ fld32 T t < 2 ^ 22 ∧
      mv G (arrOf AP) (fld32 Bs t) ^^^ fld32 Bs t =
        (if t < 22 - k then 0 else fld32 Bs (t - (22 - k))) := by
    intro t ht
    have h := hb t ht
    simp only [andB_true, beq_true, brec_eq, e1, blt_true] at h
    obtain ⟨h1, h2, h3, h4, h5⟩ := h
    have lt22 : ∀ x, Nat.shiftRight x 22 = 0 → x < 2 ^ 22 := fun x hx => by
      rw [shr_eq, Nat.shiftRight_eq_div_pow, Nat.div_eq_zero_iff_lt (Nat.two_pow_pos 22)] at hx
      exact hx
    refine ⟨h1, h2, lt22 _ h3, lt22 _ h4, ?_⟩
    simp only [sub_eq, xor_eq, land_eq, M22_eq, Nat.and_two_pow_sub_one_eq_mod] at h5
    rw [mv, ← autQ_loOf G hG]
    exact h5
  have bwf : ∀ t < 22, fld32 Bs t < 2 ^ 22 := fun t ht => (hb' t ht).2.2.1
  have twf : ∀ t < 22, fld32 T t < 2 ^ 22 := fun t ht => (hb' t ht).2.2.2.1
  have addT : ∀ u < 2 ^ 22, ∀ v < 2 ^ 22, xorFields T (u ^^^ v) = xorFields T u ^^^ xorFields T v :=
    fun u hu v hv => xorFields_xor T hu hv
  have addB : ∀ u < 2 ^ 22, ∀ v < 2 ^ 22, xorFields Bs (u ^^^ v) = xorFields Bs u ^^^ xorFields Bs v :=
    fun u hu v hv => xorFields_xor Bs hu hv
  have tb : ∀ c < 2 ^ 22, xorFields T (xorFields Bs c) = c := by
    intro c hc
    have := additive_ext (f := fun c => xorFields T (xorFields Bs c)) (f' := fun c => c)
      (fun u hu v hv => by
        rw [addB u hu v hv, addT _ (xorFields_lt22' bwf hu) _ (xorFields_lt22' bwf hv)])
      (fun _ _ _ _ => rfl) (by rw [xorFields_zero, xorFields_zero]) rfl
      (fun t ht => by
        rw [xorFields_two_pow _ ht, (hb' t ht).1]) hc
    exact this
  have bt : ∀ v < 2 ^ 22, xorFields Bs (xorFields T v) = v := by
    intro c hc
    have := additive_ext (f := fun c => xorFields Bs (xorFields T c)) (f' := fun c => c)
      (fun u hu v hv => by
        rw [addT u hu v hv, addB _ (xorFields_lt22' twf hu) _ (xorFields_lt22' twf hv)])
      (fun _ _ _ _ => rfl) (by rw [xorFields_zero, xorFields_zero]) rfl
      (fun t ht => by
        rw [xorFields_two_pow _ ht, (hb' t ht).2.1]) hc
    exact this
  have shr_lt : ∀ c < 2 ^ 22, c >>> (22 - k) < 2 ^ 22 := fun c hc =>
    lt_of_le_of_lt (by rw [Nat.shiftRight_eq_div_pow]; exact Nat.div_le_self _ _) hc
  have nmB : ∀ c < 2 ^ 22, mv G (arrOf AP) (xorFields Bs c) ^^^ xorFields Bs c =
      xorFields Bs (c >>> (22 - k)) := by
    intro c hc
    refine additive_ext (f := fun c => mv G (arrOf AP) (xorFields Bs c) ^^^ xorFields Bs c)
      (f' := fun c => xorFields Bs (c >>> (22 - k))) (fun u hu v hv => ?_) (fun u hu v hv => ?_)
      ?_ ?_ (fun t ht => ?_) hc
    · rw [addB u hu v hv, mv_xor]
      ac_rfl
    · rw [Nat.shiftRight_xor_distrib, addB _ (shr_lt u hu) _ (shr_lt v hv)]
    · rw [xorFields_zero, mv_zero, Nat.xor_self]
    · rw [Nat.zero_shiftRight, xorFields_zero]
    · rw [xorFields_two_pow _ ht, (hb' t ht).2.2.2.2]
      split_ifs with h
      · rw [Nat.shiftRight_eq_div_pow, Nat.div_eq_of_lt (Nat.pow_lt_pow_right (by decide) h),
          xorFields_zero]
      · rw [Nat.shiftRight_eq_div_pow, Nat.pow_div (by omega) (by decide),
          xorFields_two_pow _ (by omega)]
  refine ⟨hG, hrel, hwf, fun n hn => ?_, bwf, twf, tb, bt, fun v hv => ?_⟩
  · have e := compAut_loOf G hG AP AP
    rw [hsq] at e
    rw [← autApply_autComp hrel, ← e, autApply_id G hn]
  · have := nmB (xorFields T v) (xorFields_lt22' twf hv)
    rwa [bt v hv] at this

end CertificateChecks.KernelBM.CTIB.CosetQ

end

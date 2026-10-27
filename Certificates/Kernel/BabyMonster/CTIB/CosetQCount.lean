module

public import Certificates.Kernel.BabyMonster.CTIB.CosetQGrp
public import Mathlib.Data.Nat.Count

public section

namespace CertificateChecks.KernelBM.CTIB.CosetQ

open CFSG.KC.BM CFSG.KC.BM.CosetQ CFSG.Monster.B.CTIB.Native CertificateChecks.KernelBM.CTIB

set_option exponentiation.threshold 1024

variable {G : Array ℕ} {AP k Bs T : ℕ}

theorem xor_mod (a b : ℕ) : (a ^^^ b) % 2 ^ 22 = a % 2 ^ 22 ^^^ b % 2 ^ 22 := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [Nat.testBit_mod_two_pow, Nat.testBit_xor]
  cases decide (i < 22) <;> simp

theorem lt_iff_shr_zero {x n : ℕ} : x < 2 ^ n ↔ x >>> n = 0 := by
  rw [Nat.shiftRight_eq_div_pow, Nat.div_eq_zero_iff_lt (Nat.two_pow_pos n)]

theorem xor_lt_iff {a b n : ℕ} : a ^^^ b < 2 ^ n ↔ a >>> n = b >>> n := by
  rw [lt_iff_shr_zero, Nat.shiftRight_xor_distrib]
  exact ⟨xor_cancel_of, fun h => by rw [h, Nat.xor_self]⟩

theorem shl_lt {c k : ℕ} (hc : c < 2 ^ k) (hk : k ≤ 22) : c <<< (22 - k) < 2 ^ 22 := by
  rw [Nat.shiftLeft_eq]
  calc c * 2 ^ (22 - k) < 2 ^ k * 2 ^ (22 - k) :=
        Nat.mul_lt_mul_of_pos_right hc (Nat.two_pow_pos _)
    _ = 2 ^ 22 := by rw [← Nat.pow_add]; congr 1; omega

theorem shl_shr (c r : ℕ) : (c <<< r) >>> r = c := by
  rw [Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow, Nat.mul_div_cancel _ (Nat.two_pow_pos r)]

@[expose] def nv (G A : Array ℕ) (v : ℕ) : ℕ := mv G A v ^^^ v

theorem nv_lt (G A : Array ℕ) {v : ℕ} (hv : v < 2 ^ 22) : nv G A v < 2 ^ 22 :=
  Nat.xor_lt_two_pow (mv_lt _ _ _) hv

theorem nv_xor (G A : Array ℕ) (u v : ℕ) : nv G A (u ^^^ v) = nv G A u ^^^ nv G A v := by
  unfold nv
  rw [mv_xor]
  ac_rfl

theorem T_lt (hS : Setup G AP k Bs T) {v : ℕ} (hv : v < 2 ^ 22) : xorFields T v < 2 ^ 22 :=
  xorFields_lt22' hS.twf hv

theorem B_lt (hS : Setup G AP k Bs T) {c : ℕ} (hc : c < 2 ^ 22) : xorFields Bs c < 2 ^ 22 :=
  xorFields_lt22' hS.bwf hc

theorem B_inj (hS : Setup G AP k Bs T) {c c' : ℕ} (hc : c < 2 ^ 22) (hc' : c' < 2 ^ 22)
    (h : xorFields Bs c = xorFields Bs c') : c = c' := by
  rw [← hS.tb c hc, ← hS.tb c' hc', h]

theorem im_char (hS : Setup G AP k Bs T) (hk : k ≤ 22) {v : ℕ} (hv : v < 2 ^ 22) :
    (∃ e : QC G, nv G (arrOf AP) (piQ e) = v) ↔ xorFields T v < 2 ^ k := by
  constructor
  · rintro ⟨e, rfl⟩
    have hu := piQ_lt e
    have hs : xorFields T (piQ e) >>> (22 - k) < 2 ^ 22 := lt_of_le_of_lt (by
      rw [Nat.shiftRight_eq_div_pow]
      exact Nat.div_le_self _ _) (T_lt hS hu)
    rw [nv, hS.nm _ hu, hS.tb _ hs]
    rw [Nat.shiftRight_eq_div_pow, Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _), ← Nat.pow_add,
      (by omega : k + (22 - k) = 22)]
    exact T_lt hS hu
  · intro hc
    have h1 := shl_lt hc hk
    refine ⟨ofV (xorFields Bs (xorFields T v <<< (22 - k))) (B_lt hS h1), ?_⟩
    rw [piQ_ofV, nv, hS.nm _ (B_lt hS h1), hS.tb _ h1, shl_shr, hS.bt v hv]

theorem ker_char (hS : Setup G AP k Bs T) {v : ℕ} (hv : v < 2 ^ 22) :
    nv G (arrOf AP) v = 0 ↔ xorFields T v >>> (22 - k) = 0 := by
  rw [nv, hS.nm v hv]
  have hs : xorFields T v >>> (22 - k) < 2 ^ 22 := lt_of_le_of_lt (by
    rw [Nat.shiftRight_eq_div_pow]; exact Nat.div_le_self _ _) (T_lt hS hv)
  constructor
  · intro h
    exact B_inj hS hs (by decide) (by rw [h, xorFields_zero])
  · intro h
    rw [h, xorFields_zero]

@[expose] noncomputable def phiS (hS : Setup G AP k Bs T) : QC G →* QC G := homOf G (arrOf AP) hS.rel

theorem phiS_sq (hS : Setup G AP k Bs T) (y : QC G) : phiS hS (phiS hS y) = y :=
  QC.ext' (by rw [phiS, homOf_val, homOf_val]; exact hS.sq _ y.2)

theorem piQ_cjS (hS : Setup G AP k Bs T) (e n : QC G) :
    piQ (cjQ (phiS hS) e n) = piQ n ^^^ nv G (arrOf AP) (piQ e) := piQ_cjQ hS.rel e n

@[expose] def wQ (w : ℕ) (hw : w = 0 ∨ w = 2 ^ 22) : QC G :=
  mkQ w (by rcases hw with rfl | rfl <;> decide)

theorem wQ_comm {w : ℕ} (hw : w = 0 ∨ w = 2 ^ 22) (y : QC G) : wQ w hw * y = y * wQ w hw := by
  rcases hw with rfl | rfl
  · have e : wQ (G := G) 0 (Or.inl rfl) = 1 := QC.ext' (by rw [wQ, mkQ_val, QC.one_val])
    rw [e, one_mul, mul_one]
  · have e : wQ (G := G) (2 ^ 22) (Or.inr rfl) = xQ := QC.ext' rfl
    rw [e, xQ_comm]

theorem inv_const (hS : Setup G AP k Bs T) (hk : k ≤ 22) {w : ℕ} (hw : w = 0 ∨ w = 2 ^ 22)
    {n n' : QC G} (h : xorFields T (piQ n) >>> k = xorFields T (piQ n') >>> k) :
    isInv G (arrOf AP) w n.1 = isInv G (arrOf AP) w n'.1 := by
  have hv : piQ n ^^^ piQ n' < 2 ^ 22 := Nat.xor_lt_two_pow (piQ_lt n) (piQ_lt n')
  have hT : xorFields T (piQ n ^^^ piQ n') < 2 ^ k := by
    rw [xorFields_xor T (piQ_lt n) (piQ_lt n')]
    exact xor_lt_iff.2 h
  obtain ⟨e, he⟩ := (im_char hS hk hv).2 hT
  have hp : piQ (cjQ (phiS hS) e n') = piQ n := by
    rw [piQ_cjS, he, ← Nat.xor_assoc, Nat.xor_comm (piQ n'), Nat.xor_assoc, Nat.xor_self,
      Nat.xor_zero]
  have key : invQ (phiS hS) (wQ w hw) n ↔ invQ (phiS hS) (wQ w hw) n' := by
    rw [← invQ_cj (phiS_sq hS) (wQ_comm hw) e n']
    rcases eq_or_x hp with h1 | h1
    · rw [h1]
    · rw [h1, invQ_x (φ := phiS hS) (hom_x hS.rel)]
  apply Bool.eq_iff_iff.2
  have i1 := isInv_iff (G := G) hS.rel (wQ w hw) n
  have i2 := isInv_iff (G := G) hS.rel (wQ w hw) n'
  rw [wQ, mkQ_val] at i1 i2
  rw [i1, i2]
  exact key

theorem andB_eq (a b : Bool) : andB a b = (a && b) := by cases a <;> rfl

theorem notB_eq (a : Bool) : notB a = !a := by cases a <;> rfl

theorem brec_false_eq (a b : Bool) : Bool.rec (motive := fun _ => Bool) false b a = (a && b) := by
  cases a <;> rfl

@[expose] noncomputable def vEnt0 (VT j : ℕ) : ℕ := Nat.land (Nat.shiftRight (fld32 VT j) 2) 1023

@[expose] noncomputable def vEnt1 (VT j : ℕ) : ℕ := Nat.land (Nat.shiftRight (fld32 VT j) 12) 1023

@[expose] noncomputable def vSpl (VT j : ℕ) : ℕ := Nat.land (Nat.shiftRight (fld32 VT j) 1) 1

abbrev vInv (VT j : ℕ) : Prop := Nat.land (fld32 VT j) 1 = 1

theorem vOK_spec {LO A w Bs VT PT npts j : ℕ} (h : vOK LO A w k Bs T VT PT npts j = true) :
    (vInv VT j → vEnt0 VT j < npts ∧ vixOf k T PT (vEnt0 VT j) = j ∧
      splitOf PT (vEnt0 VT j) = vSpl VT j ∧
      (vSpl VT j = 1 → vEnt1 VT j < npts ∧ vixOf k T PT (vEnt1 VT j) = j ∧
        splitOf PT (vEnt1 VT j) = 1 ∧ vEnt0 VT j ≠ vEnt1 VT j)) ∧
    (¬ vInv VT j → isInvK LO A w (xorFields Bs (Nat.shiftLeft j k)) = false) := by
  unfold vOK at h
  simp only [andB_eq, notB_eq, brec_eq, beq_true] at h
  unfold vInv vEnt0 vEnt1 vSpl
  by_cases hb : Nat.land (fld32 VT j) 1 = 1
  · rw [ite_eq_left hb] at h
    simp only [Bool.and_eq_true, beq_true, blt_true] at h
    obtain ⟨h1, h2, h3, h4⟩ := h
    refine ⟨fun _ => ⟨h1, h2, h3, fun hs => ?_⟩, fun h' => absurd hb h'⟩
    rw [ite_eq_left hs] at h4
    simp only [Bool.and_eq_true, beq_true, blt_true] at h4
    obtain ⟨g1, g2, g3, g4⟩ := h4
    refine ⟨g1, g2, g3, fun e => ?_⟩
    have g5 : Nat.beq (Nat.land (Nat.shiftRight (fld32 VT j) 2) 1023)
        (Nat.land (Nat.shiftRight (fld32 VT j) 12) 1023) = true := beq_true.2 e
    rw [g5] at g4
    exact absurd g4 (by decide)
  · rw [ite_eq_right hb] at h
    exact ⟨fun h' => absurd h' hb, fun _ => by simpa using h⟩

theorem cntV_eq (VT : ℕ) : ∀ n, cntV VT n = Nat.count (fun j => vInv VT j) n
  | 0 => rfl
  | n + 1 => by
    rw [Nat.count_succ, ← cntV_eq VT n]
    change Nat.add (cntV VT n) (Nat.land (fld32 VT n) 1) = _
    have hl : Nat.land (fld32 VT n) 1 < 2 := lt_of_le_of_lt Nat.and_le_right (by decide)
    unfold vInv
    rcases Nat.lt_succ_iff.1 hl |> Nat.le_one_iff_eq_zero_or_eq_one.1 with h | h
    · rw [h, ite_eq_right (by omega)]
    · rw [h, ite_eq_left rfl]

theorem ptOK_spec {LO A w Bs PT p : ℕ} (h : ptOK LO A w k Bs T PT p = true) :
    isInvK LO A w (repOf PT p) = true ∧
    xorFields T (repOf PT p % 2 ^ 22) >>> (22 - k) = 0 ∧
    (splitOf PT p = 1 → (∀ t < 22 - k, conjK LO A (fld32 Bs t) (repOf PT p) = repOf PT p) ∧
      ∀ c < 2 ^ k, repOf PT p ≤ conjK LO A (xorFields Bs (c <<< (22 - k))) (repOf PT p)) ∧
    (splitOf PT p ≠ 1 → witOf PT p < 22 - k ∧
      conjK LO A (fld32 Bs (witOf PT p)) (repOf PT p) = repOf PT p ^^^ 2 ^ 22 ∧
      repOf PT p < 2 ^ 22 ∧ ∀ c < 2 ^ k, repOf PT p ≤ repOf PT p ^^^ xorFields Bs c) := by
  unfold ptOK at h
  simp only [andB_eq, brec_eq, Bool.and_eq_true, beq_true] at h
  obtain ⟨h1, h2, h3⟩ := h
  have e1 : ∀ x, Nat.shiftLeft 1 x = 2 ^ x := fun x => by
    rw [shl_eq, Nat.shiftLeft_eq, Nat.one_mul]
  have e2 : Nat.land (repOf PT p) 4194303 = repOf PT p % 2 ^ 22 := by
    rw [land_eq, M22_eq, Nat.and_two_pow_sub_one_eq_mod]
  rw [e2, shr_eq, sub_eq] at h2
  refine ⟨h1, h2, fun hs => ?_, fun hs => ?_⟩
  · rw [ite_eq_left hs] at h3
    simp only [Bool.and_eq_true, beq_true, ble_true, allLt_true, e1, sub_eq, shl_eq] at h3
    exact h3
  · rw [ite_eq_right hs] at h3
    simp only [Bool.and_eq_true, beq_true, blt_true, ble_true, allLt_true, e1, sub_eq,
      xor_eq] at h3
    obtain ⟨g1, g2, g3, g4⟩ := h3
    exact ⟨g1, g2, g3, g4⟩

theorem count_congr' {p q : ℕ → Prop} [DecidablePred p] [DecidablePred q] {n : ℕ}
    (h : ∀ m < n, p m ↔ q m) : Nat.count p n = Nat.count q n := by
  rw [Nat.count_eq_card_filter_range, Nat.count_eq_card_filter_range]
  congr 1
  exact Finset.filter_congr fun m hm => h m (Finset.mem_range.1 hm)

theorem count_false {p : ℕ → Prop} [DecidablePred p] {n : ℕ} (h : ∀ m < n, ¬ p m) :
    Nat.count p n = 0 := by
  rw [Nat.count_eq_card_filter_range, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  exact fun m hm => h m (Finset.mem_range.1 hm)

theorem count_mod (R : ℕ → Prop) [DecidablePred R] (M : ℕ) : ∀ N,
    Nat.count (fun m => R (m % M)) (M * N) = N * Nat.count R M
  | 0 => by simp
  | N + 1 => by
    rw [Nat.mul_succ, Nat.count_add, count_mod R M N, Nat.succ_mul]
    congr 1
    exact count_congr' fun m hm => by rw [Nat.mul_add_mod, Nat.mod_eq_of_lt hm]

theorem count_div (R : ℕ → Prop) [DecidablePred R] {M : ℕ} (hM : 0 < M) : ∀ N,
    Nat.count (fun m => R (m / M)) (M * N) = M * Nat.count R N
  | 0 => by simp
  | N + 1 => by
    rw [Nat.mul_succ, Nat.count_add, count_div R hM N, Nat.count_succ, Nat.mul_add]
    congr 1
    rw [count_congr' (q := fun _ => R N) fun m hm => by
      rw [Nat.mul_add_div hM, Nat.div_eq_of_lt hm, Nat.add_zero]]
    by_cases h : R N
    · rw [ite_eq_left h, Nat.mul_one, Nat.count_eq_card_filter_range, Finset.filter_true_of_mem
        (fun _ _ => h), Finset.card_range]
    · rw [ite_eq_right h, Nat.mul_zero, count_false fun _ _ => h]

theorem actGo_bit (rows : Array ℕ) (v : ℕ) : ∀ n acc t,
    (CFSG.Monster.VisCert.Native.actGo rows v n acc).testBit t =
      (acc.testBit t ^^ bx (fun i => v.testBit i && rows[i]!.testBit t) n)
  | 0, acc, t => by simp [CFSG.Monster.VisCert.Native.actGo, bx]
  | n + 1, acc, t => by
    rw [CFSG.Monster.VisCert.Native.actGo, actGo_bit rows v n, bx]
    by_cases h : v.testBit n
    · rw [ite_eq_left h, Nat.testBit_xor, h, Bool.true_and]
      cases acc.testBit t <;> cases rows[n]!.testBit t <;>
        cases bx (fun i => v.testBit i && rows[i]!.testBit t) n <;> rfl
    · rw [ite_eq_right h, Bool.eq_false_iff.2 h, Bool.false_and, Bool.xor_false]

theorem act22_eq {L : Array ℕ} (hL : ∀ i < 22, L[i]! = fld32 AP i % 2 ^ 22) (v : ℕ) :
    CFSG.Monster.B.Max2.Native.act22 L v = mv G (arrOf AP) v := by
  apply Nat.eq_of_testBit_eq
  intro t
  rw [CFSG.Monster.B.Max2.Native.act22, actGo_bit, Nat.zero_testBit, Bool.false_xor, mv_bit,
    and_bx]
  refine bx_congr fun i hi => ?_
  rw [hL i hi, arrOf_getD _ hi, Nat.testBit_mod_two_pow]
  cases v.testBit i <;> cases decide (t < 22) <;> cases (fld32 AP i).testBit t <;> rfl

theorem countBelow_eq (p : ℕ → Bool) :
    ∀ n acc, countBelow p n acc = acc + Nat.count (fun m => p m = true) n
  | 0, acc => rfl
  | n + 1, acc => by
    rw [countBelow, countBelow_eq p n, Nat.count_succ]
    rcases Bool.eq_false_or_eq_true (p n) with h | h
    · simp only [h, ite_true]
      omega
    · simp only [h, Bool.false_eq_true, ite_false]
      omega

theorem count_bij {P Q : ℕ → Prop} [DecidablePred P] [DecidablePred Q] {N : ℕ} (f g : ℕ → ℕ)
    (hf : ∀ m < N, f m < N) (hg : ∀ m < N, g m < N) (hgf : ∀ m < N, g (f m) = m)
    (hfg : ∀ m < N, f (g m) = m) (hP : ∀ m < N, P m ↔ Q (f m)) :
    Nat.count P N = Nat.count Q N := by
  rw [Nat.count_eq_card_filter_range, Nat.count_eq_card_filter_range]
  apply Finset.card_nbij' f g
  · intro m hm
    rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_range] at hm ⊢
    exact ⟨hf m hm.1, (hP m hm.1).1 hm.2⟩
  · intro m hm
    rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_range] at hm ⊢
    refine ⟨hg m hm.1, (hP _ (hg m hm.1)).2 ?_⟩
    rw [hfg m hm.1]
    exact hm.2
  · intro m hm
    rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_range] at hm
    exact hgf m hm.1
  · intro m hm
    rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_range] at hm
    exact hfg m hm.1

theorem repOf_lt (PT p : ℕ) : repOf PT p < 2 ^ 23 :=
  lt_of_le_of_lt Nat.and_le_right (by decide)

theorem land_mod (x : ℕ) : Nat.land x 4194303 = x % 2 ^ 22 := by
  rw [land_eq, M22_eq, Nat.and_two_pow_sub_one_eq_mod]

theorem split_add {x : ℕ} (hx : x < 2 ^ 22) (s : ℕ) :
    (x + 2 ^ 22 * s) % 2 ^ 22 = x ∧ (x + 2 ^ 22 * s) / 2 ^ 22 = s := by
  refine ⟨by rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hx], ?_⟩
  rw [Nat.add_mul_div_left _ _ (Nat.two_pow_pos 22), Nat.div_eq_of_lt hx, Nat.zero_add]

theorem countInv_eq (hG : SymG G) (hS : Setup G AP k Bs T) (hk : k ≤ 11) {w : ℕ}
    (hw : w = 0 ∨ w = 2 ^ 22) {L : Array ℕ} (hL : ∀ i < 22, L[i]! = fld32 AP i % 2 ^ 22)
    {VT PT npts : ℕ} (hv : ∀ j < 2 ^ (22 - 2 * k), vOK (loOf G) AP w k Bs T VT PT npts j = true)
    (hpt : ∀ p < npts, ptOK (loOf G) AP w k Bs T PT p = true) :
    countInv G (arrOf AP) L w = 2 ^ (k + 1) * cntV VT (2 ^ (22 - 2 * k)) := by
  have hm22 : ∀ n, n % 2 ^ 22 < 2 ^ 22 := fun n => Nat.mod_lt _ (Nat.two_pow_pos 22)
  have key : ∀ n < 2 ^ 23, isInvF G (arrOf AP) L w n = true ↔
      (xorFields T (n % 2 ^ 22) >>> (22 - k) = 0 ∧ vInv VT (xorFields T (n % 2 ^ 22) >>> k)) := by
    intro n hn
    have hv22 := hm22 n
    unfold isInvF
    rw [Bool.and_eq_true, beq_iff_eq, act22_eq hL]
    have hK : mv G (arrOf AP) (n % 2 ^ 22) = n % 2 ^ 22 ↔
        xorFields T (n % 2 ^ 22) >>> (22 - k) = 0 := by
      rw [← ker_char hS hv22, nv]
      exact ⟨fun h => by rw [h, Nat.xor_self], xor_cancel_of⟩
    rw [hK]
    apply and_congr_right
    intro hk0
    have hTl : xorFields T (n % 2 ^ 22) < 2 ^ (22 - k) := lt_iff_shr_zero.2 hk0
    have hj : xorFields T (n % 2 ^ 22) >>> k < 2 ^ (22 - 2 * k) := by
      rw [Nat.shiftRight_eq_div_pow, Nat.div_lt_iff_lt_mul (Nat.two_pow_pos k), ← Nat.pow_add,
        (by omega : 22 - 2 * k + k = 22 - k)]
      exact hTl
    obtain ⟨hv1, hv2⟩ := vOK_spec (hv _ hj)
    have hN : piQ (mkQ (G := G) n hn) = n % 2 ^ 22 := by rw [piQ, mkQ_val]
    by_cases hi : vInv VT (xorFields T (n % 2 ^ 22) >>> k)
    · obtain ⟨hp0, hvix, -, -⟩ := hv1 hi
      obtain ⟨hinv, -⟩ := ptOK_spec (hpt _ hp0)
      have hR : piQ (mkQ (G := G) (repOf PT (vEnt0 VT (xorFields T (n % 2 ^ 22) >>> k)))
          (repOf_lt _ _)) = repOf PT (vEnt0 VT (xorFields T (n % 2 ^ 22) >>> k)) % 2 ^ 22 := by
        rw [piQ, mkQ_val]
      have hc := inv_const hS (by omega) hw (n := mkQ n hn) (n' := mkQ _ (repOf_lt PT
        (vEnt0 VT (xorFields T (n % 2 ^ 22) >>> k)))) (by
          rw [hN, hR]
          unfold vixOf at hvix
          rw [shr_eq, land_mod] at hvix
          exact hvix.symm)
      have hrep : isInv G (arrOf AP) w (repOf PT (vEnt0 VT (xorFields T (n % 2 ^ 22) >>> k))) =
          true := by
        rw [← isInvK_eq hG]
        exact hinv
      have hc' : isInv G (arrOf AP) w n =
          isInv G (arrOf AP) w (repOf PT (vEnt0 VT (xorFields T (n % 2 ^ 22) >>> k))) := hc
      exact ⟨fun _ => hi, fun _ => hc'.trans hrep⟩
    · have hf := hv2 hi
      have hjk : (xorFields T (n % 2 ^ 22) >>> k) <<< k < 2 ^ 22 := by
        rw [Nat.shiftLeft_eq]
        calc (xorFields T (n % 2 ^ 22) >>> k) * 2 ^ k < 2 ^ (22 - 2 * k) * 2 ^ k :=
              Nat.mul_lt_mul_of_pos_right hj (Nat.two_pow_pos k)
          _ ≤ 2 ^ 22 := by rw [← Nat.pow_add]; exact Nat.pow_le_pow_right (by decide) (by omega)
      have hcv := B_lt hS hjk
      have h2223 : (2 : ℕ) ^ 22 < 2 ^ 23 := Nat.pow_lt_pow_right (by decide) (by decide)
      have hC : piQ (mkQ (G := G) (xorFields Bs ((xorFields T (n % 2 ^ 22) >>> k) <<< k))
          (lt_trans hcv h2223)) = xorFields Bs ((xorFields T (n % 2 ^ 22) >>> k) <<< k) := by
        rw [piQ, mkQ_val, Nat.mod_eq_of_lt hcv]
      have hc := inv_const hS (by omega) hw (n := mkQ n hn) (n' := mkQ _ (lt_trans hcv
        h2223)) (by rw [hN, hC, hS.tb _ hjk, shl_shr])
      have hf' : isInv G (arrOf AP) w (xorFields Bs ((xorFields T (n % 2 ^ 22) >>> k) <<< k)) =
          false := by
        rw [← isInvK_eq hG]
        exact hf
      have hc' : isInv G (arrOf AP) w n =
          isInv G (arrOf AP) w (xorFields Bs ((xorFields T (n % 2 ^ 22) >>> k) <<< k)) := hc
      rw [hf'] at hc'
      exact ⟨fun h => absurd (hc'.symm.trans h) (by decide), fun h => absurd h hi⟩
  have h1 : Nat.count (fun n => isInvF G (arrOf AP) L w n = true) (2 ^ 23) =
      Nat.count (fun m => xorFields T (m % 2 ^ 22) >>> (22 - k) = 0 ∧
        vInv VT (xorFields T (m % 2 ^ 22) >>> k)) (2 ^ 23) :=
    count_congr' key
  have h2 : Nat.count (fun m => xorFields T (m % 2 ^ 22) >>> (22 - k) = 0 ∧
        vInv VT (xorFields T (m % 2 ^ 22) >>> k)) (2 ^ 23) =
      Nat.count (fun m => (m % 2 ^ 22) >>> (22 - k) = 0 ∧ vInv VT ((m % 2 ^ 22) >>> k))
        (2 ^ 23) := by
    have hdiv : ∀ m < 2 ^ 23, m / 2 ^ 22 < 2 := fun m hm =>
      (Nat.div_lt_iff_lt_mul (Nat.two_pow_pos 22)).2 (by omega)
    refine count_bij (fun m => xorFields T (m % 2 ^ 22) + 2 ^ 22 * (m / 2 ^ 22))
      (fun m => xorFields Bs (m % 2 ^ 22) + 2 ^ 22 * (m / 2 ^ 22)) (fun m hm => ?_)
      (fun m hm => ?_) (fun m hm => ?_) (fun m hm => ?_) (fun m hm => ?_)
    · have := T_lt hS (hm22 m)
      have := hdiv m hm
      omega
    · have := B_lt hS (hm22 m)
      have := hdiv m hm
      omega
    · rw [(split_add (T_lt hS (hm22 m)) _).1, (split_add (T_lt hS (hm22 m)) _).2,
        hS.bt _ (hm22 m), Nat.mod_add_div]
    · rw [(split_add (B_lt hS (hm22 m)) _).1, (split_add (B_lt hS (hm22 m)) _).2,
        hS.tb _ (hm22 m), Nat.mod_add_div]
    · rw [(split_add (T_lt hS (hm22 m)) _).1]
  have h3 : Nat.count (fun m => (m % 2 ^ 22) >>> (22 - k) = 0 ∧ vInv VT ((m % 2 ^ 22) >>> k))
      (2 ^ 23) = 2 * Nat.count (fun c => c >>> (22 - k) = 0 ∧ vInv VT (c >>> k)) (2 ^ 22) :=
    count_mod (fun c => c >>> (22 - k) = 0 ∧ vInv VT (c >>> k)) (2 ^ 22) 2
  have h4 : Nat.count (fun c => c >>> (22 - k) = 0 ∧ vInv VT (c >>> k)) (2 ^ 22) =
      Nat.count (fun c => vInv VT (c / 2 ^ k)) (2 ^ k * 2 ^ (22 - 2 * k)) := by
    have hle : (2 : ℕ) ^ (22 - k) ≤ 2 ^ 22 := Nat.pow_le_pow_right (by decide) (by omega)
    have e : (2 ^ 22 : ℕ) = 2 ^ (22 - k) + (2 ^ 22 - 2 ^ (22 - k)) := (Nat.add_sub_cancel' hle).symm
    have e2 : (2 : ℕ) ^ k * 2 ^ (22 - 2 * k) = 2 ^ (22 - k) := by
      rw [← Nat.pow_add, (by omega : k + (22 - 2 * k) = 22 - k)]
    have hz : Nat.count (fun m => (2 ^ (22 - k) + m) >>> (22 - k) = 0 ∧
        vInv VT ((2 ^ (22 - k) + m) >>> k)) (2 ^ 22 - 2 ^ (22 - k)) = 0 :=
      count_false fun m _ h => by
        have := lt_iff_shr_zero.2 h.1
        omega
    rw [e, Nat.count_add, hz, Nat.add_zero, e2]
    exact count_congr' fun c hc => by
      rw [← Nat.shiftRight_eq_div_pow]
      exact ⟨fun h => h.2, fun h => ⟨lt_iff_shr_zero.1 hc, h⟩⟩
  rw [countInv, countBelow_eq, Nat.zero_add, h1, h2, h3, h4,
    count_div (fun j => vInv VT j) (Nat.two_pow_pos k), cntV_eq, Nat.pow_succ,
    Nat.mul_comm (2 ^ k) 2, Nat.mul_assoc]

end CertificateChecks.KernelBM.CTIB.CosetQ

end

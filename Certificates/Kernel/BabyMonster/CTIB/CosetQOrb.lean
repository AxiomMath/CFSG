module

public import Certificates.Kernel.BabyMonster.CTIB.CosetQCount

public section

namespace CertificateChecks.KernelBM.CTIB.CosetQ

open CFSG.KC.BM CFSG.KC.BM.CosetQ CFSG.Monster.B.CTIB.Native CertificateChecks.KernelBM.CTIB

set_option exponentiation.threshold 1024

inductive Reach (act : ℕ → ℕ → ℕ) (ngen root : ℕ) : ℕ → Prop
  | root : Reach act ngen root root
  | step {n : ℕ} (i : ℕ) : i < ngen → Reach act ngen root n → Reach act ngen root (act i n)

variable {G : Array ℕ} {AP k Bs T : ℕ}

theorem wfA (hS : Setup G AP k Bs T) : ∀ i < 22, (arrOf AP).getD i 0 < 2 ^ 23 :=
  fun i hi => by rw [arrOf_getD _ hi]; exact hS.wf i hi

theorem phiS_x (hS : Setup G AP k Bs T) : phiS hS xQ = xQ := hom_x hS.rel

theorem reach_qconj (hS : Setup G AP k Bs T) (n : QC G) (m : ℕ) :
    Reach (qconj G (arrOf AP)) 22 n.1 m ↔ ∃ e : QC G, m = (cjQ (phiS hS) e n).1 := by
  constructor
  · intro h
    induction h with
    | root => exact ⟨1, by rw [cjQ_one]⟩
    | step i hi _ ih =>
      obtain ⟨e, rfl⟩ := ih
      refine ⟨e * eK i hi, ?_⟩
      rw [cjQ_mul]
      exact qconj_eq hS.rel (wfA hS) hi _
  · rintro ⟨e, rfl⟩
    refine gen_induct (fun e => Reach (qconj G (arrOf AP)) 22 n.1 (cjQ (phiS hS) e n).1)
      ?_ ?_ (fun a m hm h => ?_) e
    · rw [cjQ_one]
      exact Reach.root
    · rw [cjQ_x (phiS_x hS)]
      exact Reach.root
    · have e1 : (cjQ (phiS hS) (a * eK m hm) n).1 = qconj G (arrOf AP) m (cjQ (phiS hS) a n).1 := by
        rw [cjQ_mul]
        exact (qconj_eq hS.rel (wfA hS) hm _).symm
      rw [e1]
      exact Reach.step m hm h

theorem mul_x_val (a : QC G) : (a * xQ).1 = a.1 ^^^ 2 ^ 22 := by
  rw [QC.mul_val]
  refine code_ext (qmul_lt _ _ _) (Nat.xor_lt_two_pow a.2 (by decide)) (fun i hi => ?_) ?_
  · rw [qmul_bit G _ _ hi, Nat.testBit_xor]
    rfl
  · rw [qmul_bit22, Nat.testBit_xor]
    change ((a.1.testBit 22 ^^ Nat.testBit (2 ^ 22) 22) ^^ corr G a.1 (2 ^ 22)) =
      (a.1.testBit 22 ^^ Nat.testBit (2 ^ 22) 22)
    rw [corr_x_right, Bool.xor_false]

theorem piQ_mkQ {n : ℕ} (h : n < 2 ^ 23) : piQ (mkQ (G := G) n h) = n % 2 ^ 22 := by
  rw [piQ, mkQ_val]

theorem orbit_full (hS : Setup G AP k Bs T) (hk : k ≤ 22) {n f : QC G}
    (hfx : cjQ (phiS hS) f n = n * xQ) (m : ℕ) :
    (∃ e : QC G, m = (cjQ (phiS hS) e n).1) ↔
      m < 2 ^ 23 ∧ xorFields T ((m ^^^ n.1) % 2 ^ 22) < 2 ^ k := by
  constructor
  · rintro ⟨e, rfl⟩
    refine ⟨(cjQ (phiS hS) e n).2, ?_⟩
    have hv : (((cjQ (phiS hS) e n).1 ^^^ n.1) % 2 ^ 22) = nv G (arrOf AP) (piQ e) := by
      rw [xor_mod]
      change piQ (cjQ (phiS hS) e n) ^^^ piQ n = _
      rw [piQ_cjS, Nat.xor_comm (piQ n), Nat.xor_assoc, Nat.xor_self, Nat.xor_zero]
    rw [hv]
    exact (im_char hS hk (nv_lt _ _ (piQ_lt e))).1 ⟨e, rfl⟩
  · rintro ⟨hm, hT⟩
    obtain ⟨e, he⟩ := (im_char hS hk (Nat.mod_lt _ (Nat.two_pow_pos 22))).2 hT
    have hp : piQ (cjQ (phiS hS) e n) = piQ (mkQ (G := G) m hm) := by
      rw [piQ_cjS, he, xor_mod, piQ_mkQ]
      change piQ n ^^^ (m % 2 ^ 22 ^^^ piQ n) = m % 2 ^ 22
      rw [Nat.xor_comm, Nat.xor_assoc, Nat.xor_self, Nat.xor_zero]
    rcases eq_or_x hp with h | h
    · exact ⟨e, by rw [h, mkQ_val]⟩
    · refine ⟨f * e, ?_⟩
      rw [cjQ_mul, hfx, cjQ_mulx, h, mul_assoc, xQ_sq, mul_one, mkQ_val]

theorem count_lt_eq {a n : ℕ} (h : a ≤ n) : Nat.count (fun c => c < a) n = a := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
  have hz : Nat.count (fun m => a + m < a) d = 0 := count_false fun m _ hm => by omega
  rw [Nat.count_add, hz, Nat.add_zero, Nat.count_eq_card_filter_range,
    Finset.filter_true_of_mem fun m hm => Finset.mem_range.1 hm, Finset.card_range]

theorem card_full (hS : Setup G AP k Bs T) (hk : k ≤ 22) (n : QC G) :
    ((Finset.range (2 ^ 23)).filter
      (fun m => xorFields T ((m ^^^ n.1) % 2 ^ 22) < 2 ^ k)).card = 2 ^ (k + 1) := by
  have hm22 : ∀ x, x % 2 ^ 22 < 2 ^ 22 := fun x => Nat.mod_lt _ (Nat.two_pow_pos 22)
  have hdiv : ∀ m < 2 ^ 23, m / 2 ^ 22 < 2 := fun m hm =>
    (Nat.div_lt_iff_lt_mul (Nat.two_pow_pos 22)).2 (by omega)
  have hpn : n.1 % 2 ^ 22 = piQ n := rfl
  rw [← Nat.count_eq_card_filter_range]
  have hT : ∀ m, xorFields T ((m ^^^ n.1) % 2 ^ 22) < 2 ^ 22 := fun m => T_lt hS (hm22 _)
  have hB : ∀ m, xorFields Bs (m % 2 ^ 22) ^^^ piQ n < 2 ^ 22 := fun m =>
    Nat.xor_lt_two_pow (B_lt hS (hm22 m)) (piQ_lt n)
  rw [count_bij (Q := fun m => m % 2 ^ 22 < 2 ^ k)
    (fun m => xorFields T ((m ^^^ n.1) % 2 ^ 22) + 2 ^ 22 * (m / 2 ^ 22))
    (fun m => (xorFields Bs (m % 2 ^ 22) ^^^ piQ n) + 2 ^ 22 * (m / 2 ^ 22))
    (fun m hm => by have := hT m; have := hdiv m hm; omega)
    (fun m hm => by have := hB m; have := hdiv m hm; omega)
    (fun m hm => by
      rw [(split_add (hT m) _).1, (split_add (hT m) _).2, xor_mod, hpn,
        hS.bt _ (Nat.xor_lt_two_pow (hm22 m) (piQ_lt n)), Nat.xor_assoc, Nat.xor_self,
        Nat.xor_zero, Nat.mod_add_div])
    (fun m hm => by
      rw [(split_add (hB m) _).2, xor_mod, (split_add (hB m) _).1, hpn, Nat.xor_assoc,
        Nat.xor_self, Nat.xor_zero, hS.tb _ (hm22 m), Nat.mod_add_div])
    (fun m hm => by rw [(split_add (hT m) _).1])]
  have e : (2 : ℕ) ^ 23 = 2 ^ 22 * 2 := by rw [Nat.pow_succ]
  rw [e, count_mod (fun c => c < 2 ^ k) (2 ^ 22) 2,
    count_lt_eq (Nat.pow_le_pow_right (by decide) hk), Nat.pow_succ, Nat.mul_comm]

@[expose] noncomputable def eIm (hS : Setup G AP k Bs T) (c : ℕ) : QC G :=
  ofV (xorFields Bs ((c <<< (22 - k)) % 2 ^ 22)) (xorFields_lt22 hS.bwf _)

theorem eIm_val (hS : Setup G AP k Bs T) (hk : k ≤ 22) {c : ℕ} (hc : c < 2 ^ k) :
    (eIm hS c).1 = xorFields Bs (c <<< (22 - k)) := by
  change xorFields Bs ((c <<< (22 - k)) % 2 ^ 22) = _
  rw [Nat.mod_eq_of_lt (shl_lt hc hk)]

theorem nv_eIm (hS : Setup G AP k Bs T) (hk : k ≤ 22) {c : ℕ} (hc : c < 2 ^ k) :
    nv G (arrOf AP) (piQ (eIm hS c)) = xorFields Bs c := by
  have h1 := shl_lt hc hk
  have hp : piQ (eIm hS c) = xorFields Bs (c <<< (22 - k)) := by
    rw [piQ, eIm_val hS hk hc, Nat.mod_eq_of_lt (B_lt hS h1)]
  rw [hp, nv, hS.nm _ (B_lt hS h1), hS.tb _ h1, shl_shr]

theorem piQ_autB (hS : Setup G AP k Bs T) {c : ℕ} (hc : c < 2 ^ 22) :
    piQ (mkQ (G := G) (autApply G (arrOf Bs) c) (autApply_lt _ _ _)) = xorFields Bs c := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [piQ_mkQ, Nat.testBit_mod_two_pow]
  by_cases hi : i < 22
  · rw [decide_eq_true hi, Bool.true_and, autApply_bit G _ _ hi, xorFields_bit22 Bs hc (by omega)]
    exact bx_congr fun s hs => by rw [arrOf_getD _ hs]
  · rw [decide_eq_false hi, Bool.false_and, Nat.testBit_lt_two_pow (lt_of_lt_of_le (B_lt hS hc)
      (Nat.pow_le_pow_right (by decide) (by omega)))]

theorem fix_K (hS : Setup G AP k Bs T) {n : QC G}
    (hfix : ∀ t (ht : t < 22 - k), cjQ (phiS hS) (ofV (fld32 Bs t) (hS.bwf t (by omega))) n = n)
    {f : QC G} (hf : nv G (arrOf AP) (piQ f) = 0) : cjQ (phiS hS) f n = n := by
  have hc : xorFields T (piQ f) < 2 ^ (22 - k) :=
    lt_iff_shr_zero.2 ((ker_char hS (piQ_lt f)).1 hf)
  have hc22 : xorFields T (piQ f) < 2 ^ 22 := T_lt hS (piQ_lt f)
  have prod : ∀ m ≤ 22, cjQ (phiS hS) (mkQ (autApplyN G (arrOf Bs) (xorFields T (piQ f)) m)
      (autApplyN_lt _ _ _ _)) n = n := by
    intro m
    induction m with
    | zero =>
      intro _
      have e : mkQ (G := G) (autApplyN G (arrOf Bs) (xorFields T (piQ f)) 0)
          (autApplyN_lt _ _ _ _) = 1 := by
        refine QC.ext' ?_
        rw [mkQ_val, autApplyN.eq_1, ite_eq_right (by
          rw [Nat.testBit_lt_two_pow hc22]
          decide), QC.one_val]
      rw [e, cjQ_one]
    | succ m ih =>
      intro hm
      by_cases hb : (xorFields T (piQ f)).testBit m
      · have hmk : m < 22 - k := by
          by_contra hcon
          rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le hc
            (Nat.pow_le_pow_right (by decide) (by omega)))] at hb
          exact absurd hb (by decide)
        have e : mkQ (G := G) (autApplyN G (arrOf Bs) (xorFields T (piQ f)) (m + 1))
            (autApplyN_lt _ _ _ _) = mkQ (autApplyN G (arrOf Bs) (xorFields T (piQ f)) m)
              (autApplyN_lt _ _ _ _) * ofV (fld32 Bs m) (hS.bwf m (by omega)) := by
          refine QC.ext' ?_
          rw [mkQ_val, autApplyN.eq_2, ite_eq_left hb, QC.mul_val, mkQ_val, arrOf_getD _ (by omega)]
          rfl
        rw [e, cjQ_mul, ih (by omega), hfix m hmk]
      · have e : mkQ (G := G) (autApplyN G (arrOf Bs) (xorFields T (piQ f)) (m + 1))
            (autApplyN_lt _ _ _ _) = mkQ (autApplyN G (arrOf Bs) (xorFields T (piQ f)) m)
              (autApplyN_lt _ _ _ _) := by
          refine QC.ext' ?_
          rw [mkQ_val, mkQ_val, autApplyN.eq_2, ite_eq_right hb]
        rw [e]
        exact ih (by omega)
  have hP := prod 22 (Nat.le_refl 22)
  have hp : piQ f = piQ (mkQ (G := G) (autApply G (arrOf Bs) (xorFields T (piQ f)))
      (autApply_lt _ _ _)) := by
    rw [piQ_autB hS hc22, hS.bt _ (piQ_lt f)]
  have hP' : cjQ (phiS hS) (mkQ (G := G) (autApply G (arrOf Bs) (xorFields T (piQ f)))
      (autApply_lt _ _ _)) n = n := hP
  rcases eq_or_x hp with h | h
  · rw [h]
    exact hP'
  · rw [h, cjQ_mul, hP', cjQ_x (phiS_x hS)]

theorem orbit_split (hS : Setup G AP k Bs T) (hk : k ≤ 22) {n : QC G}
    (hfix : ∀ t (ht : t < 22 - k), cjQ (phiS hS) (ofV (fld32 Bs t) (hS.bwf t (by omega))) n = n)
    (m : ℕ) :
    (∃ e : QC G, m = (cjQ (phiS hS) e n).1) ↔ ∃ c < 2 ^ k, m = (cjQ (phiS hS) (eIm hS c) n).1 := by
  constructor
  · rintro ⟨e, rfl⟩
    have hu := nv_lt G (arrOf AP) (piQ_lt e)
    have hc := (im_char hS hk hu).1 ⟨e, rfl⟩
    refine ⟨_, hc, ?_⟩
    have he : nv G (arrOf AP) (piQ (eIm hS (xorFields T (nv G (arrOf AP) (piQ e))))) =
        nv G (arrOf AP) (piQ e) := by
      rw [nv_eIm hS hk hc, hS.bt _ hu]
    have hf : nv G (arrOf AP) (piQ (e * (eIm hS (xorFields T (nv G (arrOf AP) (piQ e))))⁻¹)) =
        0 := by
      rw [piQ_mul, piQ_inv, nv_xor, he, Nat.xor_self]
    have hee : e = (e * (eIm hS (xorFields T (nv G (arrOf AP) (piQ e))))⁻¹) *
        eIm hS (xorFields T (nv G (arrOf AP) (piQ e))) := by
      rw [mul_assoc, inv_mul_cancel, mul_one]
    conv_lhs => rw [hee]
    rw [cjQ_mul, fix_K hS hfix hf]
  · rintro ⟨c, -, rfl⟩
    exact ⟨_, rfl⟩

theorem piQ_split (hS : Setup G AP k Bs T) (hk : k ≤ 22) (n : QC G) {c : ℕ} (hc : c < 2 ^ k) :
    piQ (cjQ (phiS hS) (eIm hS c) n) = piQ n ^^^ xorFields Bs c := by
  rw [piQ_cjS, nv_eIm hS hk hc]

theorem card_split (hS : Setup G AP k Bs T) (hk : k ≤ 22) (n : QC G) :
    ((Finset.range (2 ^ k)).image (fun c => (cjQ (phiS hS) (eIm hS c) n).1)).card = 2 ^ k := by
  rw [Finset.card_image_of_injOn, Finset.card_range]
  intro c hc c' hc' h
  have hc1 : c < 2 ^ k := Finset.mem_range.1 hc
  have hc2 : c' < 2 ^ k := Finset.mem_range.1 hc'
  have h1 : piQ (cjQ (phiS hS) (eIm hS c) n) = piQ (cjQ (phiS hS) (eIm hS c') n) :=
    congrArg (fun x => x % 2 ^ 22) h
  rw [piQ_split hS hk n hc1, piQ_split hS hk n hc2] at h1
  have h2 : xorFields Bs c = xorFields Bs c' := by
    have := congrArg (fun x => piQ n ^^^ x) h1
    simpa only [← Nat.xor_assoc, Nat.xor_self, Nat.zero_xor] using this
  have hk22 : (2 : ℕ) ^ k ≤ 2 ^ 22 := Nat.pow_le_pow_right (by decide) hk
  exact B_inj hS (by omega) (by omega) h2

theorem valid_conj (hS : Setup G AP k Bs T) {w : ℕ} (hw : w = 0 ∨ w = 2 ^ 22) {n : QC G}
    (hn : isInv G (arrOf AP) w n.1 = true) (e : QC G) :
    isInv G (arrOf AP) w (cjQ (phiS hS) e n).1 = true := by
  have i1 := isInv_iff (G := G) hS.rel (wQ w hw) (cjQ (phiS hS) e n)
  have i2 := isInv_iff (G := G) hS.rel (wQ w hw) n
  rw [wQ, mkQ_val] at i1 i2
  rw [i1]
  rw [i2] at hn
  exact (invQ_cj (phiS_sq hS) (wQ_comm hw) e n).2 hn

@[expose] noncomputable def repQ (PT p : ℕ) : QC G := mkQ (repOf PT p) (repOf_lt PT p)

theorem repQ_val (PT p : ℕ) : (repQ (G := G) PT p).1 = repOf PT p := rfl

@[expose] noncomputable def sizeOf (k PT p : ℕ) : ℕ := if splitOf PT p = 1 then 2 ^ k else 2 ^ (k + 1)

theorem fix_of_spec (hG : SymG G) (hS : Setup G AP k Bs T) {PT p : ℕ}
    (h : ∀ t < 22 - k, conjK (loOf G) AP (fld32 Bs t) (repOf PT p) = repOf PT p) :
    ∀ t (ht : t < 22 - k), cjQ (phiS hS) (ofV (fld32 Bs t) (hS.bwf t (by omega))) (repQ PT p) =
      repQ PT p :=
  fun t ht => QC.ext' ((conjK_eq hG hS.rel _ _).symm.trans (h t ht))

theorem wit_of_spec (hG : SymG G) (hS : Setup G AP k Bs T) {PT p : ℕ} (hwit : witOf PT p < 22 - k)
    (h : conjK (loOf G) AP (fld32 Bs (witOf PT p)) (repOf PT p) = repOf PT p ^^^ 2 ^ 22) :
    cjQ (phiS hS) (ofV (fld32 Bs (witOf PT p)) (hS.bwf _ (by omega))) (repQ PT p) =
      repQ PT p * xQ :=
  QC.ext' (by rw [mul_x_val]; exact (conjK_eq hG hS.rel _ _).symm.trans h)

theorem qorb_facts (hG : SymG G) (hS : Setup G AP k Bs T) (hk : k ≤ 11) {w : ℕ}
    (hw : w = 0 ∨ w = 2 ^ 22) {PT p : ℕ} (hp : ptOK (loOf G) AP w k Bs T PT p = true) :
    ∃ S : Finset ℕ, (∀ m, m ∈ S ↔ Reach (qconj G (arrOf AP)) 22 (repOf PT p) m) ∧
      S.card = sizeOf k PT p ∧
      ∀ m ∈ S, (m < 2 ^ 23 ∧ isInv G (arrOf AP) w m = true) ∧ repOf PT p ≤ m := by
  obtain ⟨hinv, -, hspl, hfull⟩ := ptOK_spec hp
  have hinvR : isInv G (arrOf AP) w (repQ (G := G) PT p).1 = true := by
    rw [← isInvK_eq hG]
    exact hinv
  have hreach : ∀ m, Reach (qconj G (arrOf AP)) 22 (repOf PT p) m ↔
      ∃ e : QC G, m = (cjQ (phiS hS) e (repQ PT p)).1 := reach_qconj hS (repQ PT p)
  by_cases hs : splitOf PT p = 1
  · obtain ⟨hfix0, hleast⟩ := hspl hs
    have hfix := fix_of_spec hG hS hfix0
    refine ⟨(Finset.range (2 ^ k)).image (fun c => (cjQ (phiS hS) (eIm hS c) (repQ PT p)).1),
      fun m => ?_, ?_, fun m hm => ?_⟩
    · rw [hreach, orbit_split hS (by omega) hfix, Finset.mem_image]
      exact ⟨fun ⟨c, hc, h⟩ => ⟨c, Finset.mem_range.1 hc, h.symm⟩,
        fun ⟨c, hc, h⟩ => ⟨c, Finset.mem_range.2 hc, h.symm⟩⟩
    · rw [card_split hS (by omega), sizeOf, ite_eq_left hs]
    · obtain ⟨c, hc, rfl⟩ := Finset.mem_image.1 hm
      have hc' := Finset.mem_range.1 hc
      refine ⟨⟨(cjQ (phiS hS) (eIm hS c) (repQ PT p)).2, valid_conj hS hw hinvR _⟩, ?_⟩
      have h2 : conjK (loOf G) AP (eIm hS c).1 (repOf PT p) =
          (cjQ (phiS hS) (eIm hS c) (repQ PT p)).1 := conjK_eq hG hS.rel (eIm hS c) (repQ PT p)
      have := hleast c hc'
      rw [← eIm_val hS (by omega) hc', h2] at this
      exact this
  · obtain ⟨hwit, hwx, hrep22, hleast⟩ := hfull hs
    have hfx := wit_of_spec hG hS hwit hwx
    refine ⟨(Finset.range (2 ^ 23)).filter
      (fun m => xorFields T ((m ^^^ (repQ (G := G) PT p).1) % 2 ^ 22) < 2 ^ k),
      fun m => ?_, ?_, fun m hm => ?_⟩
    · rw [hreach, orbit_full hS (by omega) hfx, Finset.mem_filter, Finset.mem_range]
    · rw [card_full hS (by omega), sizeOf, ite_eq_right hs]
    · have hm' := hm
      rw [Finset.mem_filter, Finset.mem_range] at hm'
      obtain ⟨e, he⟩ := (orbit_full hS (by omega) hfx m).2 hm'
      refine ⟨⟨hm'.1, by rw [he]; exact valid_conj hS hw hinvR e⟩, ?_⟩
      have hv : (m ^^^ repOf PT p) % 2 ^ 22 < 2 ^ 22 := Nat.mod_lt _ (Nat.two_pow_pos 22)
      have hm2 := hm'.2
      rw [repQ_val] at hm2
      have hl := hleast _ hm2
      have hb : xorFields Bs (xorFields T ((m ^^^ repOf PT p) % 2 ^ 22)) =
          m % 2 ^ 22 ^^^ repOf PT p := by
        rw [hS.bt _ hv, xor_mod, Nat.mod_eq_of_lt hrep22]
      rw [hb, Nat.xor_comm (m % 2 ^ 22), ← Nat.xor_assoc, Nat.xor_self, Nat.zero_xor] at hl
      exact le_trans hl (Nat.mod_le _ _)

end CertificateChecks.KernelBM.CTIB.CosetQ

end

module

public import Certificates.Data.Kernel.SlpPcCl

public section

namespace CFSG.KC.SlpPc

open CFSG.KC.Ord

abbrev Store := List (List Nat) × List Nat × Nat

@[expose] noncomputable def stepS (mul : Nat → Nat → Nat) (ONE : Nat) (p : Nat × Nat)
    (s : Store) : Store :=
  (fun x => Bool.rec (motive := fun _ => Store) (s.1, List.cons x s.2.1, Nat.succ s.2.2)
      (List.cons (List.cons x s.2.1) s.1, List.nil, Nat.succ s.2.2)
      (Nat.beq (Nat.land (Nat.succ s.2.2) 63) 0))
    (mul (lk ONE s.1 s.2.1 s.2.2 p.1) (lk ONE s.1 s.2.1 s.2.2 p.2))

@[expose] noncomputable def stP (mul : Nat → Nat → Nat) (ONE : Nat) :
    List (Nat × Nat) → Store → Store
  | [], s => s
  | p :: ps, s => stP mul ONE ps (stepS mul ONE p s)

theorem sB_eq (y : Nat) (k : Nat → Bool) : sB y k = k y := by
  cases y <;> rfl

theorem runP_eq (mul : Nat → Nat → Nat) (ONE : Nat) : ∀ (prg : List (Nat × Nat))
    (bl : List (List Nat)) (cur : List Nat) (n : Nat) (k : List (List Nat) → List Nat → Nat → Bool),
    runP mul ONE prg bl cur n k = k (stP mul ONE prg (bl, cur, n)).1
      (stP mul ONE prg (bl, cur, n)).2.1 (stP mul ONE prg (bl, cur, n)).2.2
  | [], _, _, _, _ => rfl
  | p :: ps, bl, cur, n, k => by
    change sB (mul (lk ONE bl cur n p.1) (lk ONE bl cur n p.2)) (fun x => sB (Nat.succ n)
      fun n1 => Bool.rec (motive := fun _ => Bool) (runP mul ONE ps bl (List.cons x cur) n1 k)
        (runP mul ONE ps (List.cons (List.cons x cur) bl) List.nil n1 k)
        (Nat.beq (Nat.land n1 63) 0)) = _
    rw [sB_eq, sB_eq]
    change _ = k (stP mul ONE ps (stepS mul ONE p (bl, cur, n))).1
      (stP mul ONE ps (stepS mul ONE p (bl, cur, n))).2.1
      (stP mul ONE ps (stepS mul ONE p (bl, cur, n))).2.2
    unfold stepS
    dsimp only
    cases Nat.beq (Nat.land (Nat.succ n) 63) 0
    · exact runP_eq mul ONE ps _ _ _ k
    · exact runP_eq mul ONE ps _ _ _ k

theorem stP_append (mul : Nat → Nat → Nat) (ONE : Nat) : ∀ (p q : List (Nat × Nat)) (s : Store),
    stP mul ONE (p ++ q) s = stP mul ONE q (stP mul ONE p s)
  | [], _, _ => rfl
  | a :: p, q, s => stP_append mul ONE p q (stepS mul ONE a s)

theorem andB_eq_true {a b : Bool} (h : andB a b = true) : a = true ∧ b = true := by
  cases a <;> cases b <;> simp_all [andB]

@[expose] noncomputable def stEq (s t : Store) : Bool :=
  andB (s.1 == t.1) (andB (s.2.1 == t.2.1) (Nat.beq s.2.2 t.2.2))

theorem eq_of_stEq {s t : Store} (h : stEq s t = true) : s = t := by
  obtain ⟨h1, h2⟩ := andB_eq_true h
  obtain ⟨h2, h3⟩ := andB_eq_true h2
  obtain ⟨a, b, c⟩ := s
  obtain ⟨a', b', c'⟩ := t
  rw [beq_iff_eq] at h1 h2
  rw [Nat.beq_eq] at h3
  dsimp only at h1 h2 h3
  rw [h1, h2, h3]

@[expose] noncomputable def chkS (mul : Nat → Nat → Nat) (ONE : Nat) (c : List (Nat × Nat))
    (s t : Store) : Bool :=
  runP mul ONE c s.1 s.2.1 s.2.2 fun bl cur n => stEq (bl, cur, n) t

theorem stP_of_chkS {mul : Nat → Nat → Nat} {ONE : Nat} {c : List (Nat × Nat)} {s t : Store}
    (h : chkS mul ONE c s t = true) : stP mul ONE c s = t := by
  rw [chkS, runP_eq] at h
  exact eq_of_stEq h

theorem stP_of_chunks {mul : Nat → Nat → Nat} {ONE : Nat} {prg : List (Nat × Nat)} {K m : Nat}
    {S : Nat → Store} (hm : prg.length ≤ K * m)
    (h : ∀ i < m, chkS mul ONE ((prg.drop (K * i)).take K) (S i) (S (i + 1)) = true) :
    stP mul ONE prg (S 0) = S m := by
  have key : ∀ j ≤ m, stP mul ONE (prg.take (K * j)) (S 0) = S j := by
    intro j
    induction j with
    | zero => intro _; rfl
    | succ j ih =>
      intro hj
      rw [Nat.mul_succ, List.take_add, stP_append, ih (by omega)]
      exact stP_of_chkS (h j (by omega))
  have e := key m (Nat.le_refl m)
  rwa [List.take_of_length_le hm] at e

@[expose] noncomputable def stOf (VR : List Nat) (BL : List (List Nat)) (n : Nat) : Store :=
  (BL.drop (BL.length - n / 64), (VR.drop (VR.length - n)).take (n % 64), n)

theorem mapS_eq {α : Type} (f : α → Nat) : ∀ (l : List α) (k : List Nat → Bool),
    mapS f l k = k (l.map f)
  | [], _ => rfl
  | a :: l, k => by
    change sB (f a) (fun x => mapS f l fun xs => k (List.cons x xs)) = _
    rw [sB_eq, mapS_eq f l]
    rfl

theorem map_of_mapS {α : Type} {f : α → Nat} {l : List α} {X : List Nat}
    (h : mapS f l (fun xs => xs == X) = true) : l.map f = X := by
  rw [mapS_eq] at h
  exact beq_iff_eq.mp h

@[expose] noncomputable def powsL (mul : Nat → Nat → Nat) (ONE : Nat) (hs : List Nat) :
    List (List Nat) :=
  hs.map fun h => [ONE, h, mul h h, mul (mul h h) h, mul (mul (mul h h) h) h,
    mul (mul (mul (mul h h) h) h) h]

theorem pows_eq (mul : Nat → Nat → Nat) (ONE : Nat) : ∀ (hs : List Nat)
    (k : List (List Nat) → Bool), pows mul ONE hs k = k (powsL mul ONE hs)
  | [], _ => rfl
  | h :: hs, k => by
    change sB (mul h h) (fun h2 => sB (mul h2 h) fun h3 => sB (mul h3 h) fun h4 =>
      sB (mul h4 h) fun h5 => pows mul ONE hs fun ps => k (List.cons [ONE, h, h2, h3, h4, h5] ps))
      = _
    rw [sB_eq, sB_eq, sB_eq, sB_eq, pows_eq mul ONE hs]
    rfl

theorem powsL_of_pows {mul : Nat → Nat → Nat} {ONE : Nat} {hs : List Nat} {PW : List (List Nat)}
    (h : pows mul ONE hs (fun pw => pw == PW) = true) : powsL mul ONE hs = PW := by
  rw [pows_eq] at h
  exact beq_iff_eq.mp h

@[expose] noncomputable def relsIdx (rel : List (List Nat)) : Nat → Nat → Bool :=
  List.rec (motive := fun _ => Nat → Nat → Bool) (fun i _ => Nat.beq i 6)
    (fun r _ ih i j => andB (Nat.beq (nthD 0 r 0) i) (andB (Nat.beq (nthD 0 r 1) j)
      (Bool.rec (motive := fun _ => Bool) (ih i (Nat.succ j)) (ih (Nat.succ i) (Nat.succ i))
        (Nat.beq j 5)))) rel

@[expose] noncomputable def relE (mul : Nat → Nat → Nat) (ONE : Nat) (hs : List Nat)
    (pw : List (List Nat)) (rel : List (List Nat)) (t : Nat) : Bool :=
  relOK mul ONE hs pw (nthD 0 (nthD List.nil rel t) 0) (nthD 0 (nthD List.nil rel t) 1)
    (tl (tl (nthD List.nil rel t)))

theorem relsOK_of {mul : Nat → Nat → Nat} {ONE : Nat} {hs : List Nat} {pw : List (List Nat)} :
    ∀ (rel : List (List Nat)) (i j : Nat), relsIdx rel i j = true →
      (∀ t < rel.length, relE mul ONE hs pw rel t = true) → relsOK mul ONE hs pw rel i j = true
  | [], _, _, h, _ => h
  | r :: rs, i, j, h, hr => by
    obtain ⟨h1, h2⟩ := andB_eq_true h
    obtain ⟨h2, h3⟩ := andB_eq_true h2
    have e0 := hr 0 (by simp)
    change relOK mul ONE hs pw (nthD 0 r 0) (nthD 0 r 1) (tl (tl r)) = true at e0
    rw [Nat.beq_eq] at h1 h2
    rw [h1, h2] at e0
    have hr' : ∀ t < rs.length, relE mul ONE hs pw rs t = true := fun t ht =>
      hr (t + 1) (by simp; omega)
    change andB (Nat.beq (nthD 0 r 0) i) (andB (Nat.beq (nthD 0 r 1) j)
      (andB (relOK mul ONE hs pw i j (tl (tl r)))
        (Bool.rec (motive := fun _ => Bool) (relsOK mul ONE hs pw rs i (Nat.succ j))
          (relsOK mul ONE hs pw rs (Nat.succ i) (Nat.succ i)) (Nat.beq j 5)))) = true
    rw [Nat.beq_eq.mpr h1, Nat.beq_eq.mpr h2, e0]
    revert h3
    cases Nat.beq j 5
    · intro h3
      rw [relsOK_of rs i (Nat.succ j) h3 hr']
      rfl
    · intro h3
      rw [relsOK_of rs (Nat.succ i) (Nat.succ i) h3 hr']
      rfl

@[expose] noncomputable def fusE (mul : Nat → Nat → Nat) (ONE : Nat) (R : Nat → Nat)
    (pw : List (List Nat)) (wr : List Nat) (f : List Nat) : Bool :=
  andB (ltUpTo f 5 6) (andB (Nat.blt (nthD 0 f 7) 5)
    ((fun C => Nat.beq (mul (nfM mul ONE pw f) C) (mul C (R (nthD 0 wr (nthD 0 f 7)))))
      (R (nthD 0 f 6))))

theorem fusOK_of {mul : Nat → Nat → Nat} {ONE : Nat} {R : Nat → Nat} {pw : List (List Nat)}
    {wr : List Nat} : ∀ (fus : List (List Nat)),
      (∀ t < fus.length, fusE mul ONE R pw wr (nthD List.nil fus t) = true) →
        fusOK mul ONE R pw wr fus = true
  | [], _ => rfl
  | f :: fs, h => by
    change andB (fusE mul ONE R pw wr f) (fusOK mul ONE R pw wr fs) = true
    have h0 : fusE mul ONE R pw wr f = true := h 0 (by simp)
    rw [h0, fusOK_of fs fun t ht => h (t + 1) (by simp; omega)]
    rfl

@[expose] noncomputable def entsAll (mul : Nat → Nat → Nat) (ONE : Nat) (R : Nat → Nat)
    (pw : List (List Nat)) (X : Nat) (es : List (List Nat)) : Bool :=
  List.rec (motive := fun _ => Bool) true (fun e _ ih => andB (entOK mul ONE R pw X e) ih) es

@[expose] noncomputable def clInit (ONE : Nat) (R : Nat → Nat) (hs : List Nat)
    (es : List (List Nat)) : Store :=
  (List.nil, revOnto ((zsOf es).map R) (revOnto hs [ONE]),
    lenN (revOnto ((zsOf es).map R) (revOnto hs [ONE])))

theorem clK_of {mul : Nat → Nat → Nat} {ONE A B : Nat} {R : Nat → Nat} {pw : List (List Nat)}
    {hs : List Nat} {X : Nat} {es : List (List Nat)} {lp : List (Nat × Nat)} {ab : List Nat}
    (SL : Store) (hE : entsAll mul ONE R pw X es = true)
    (hrun : stP mul ONE lp (clInit ONE R hs es) = SL)
    (hab : andB (Nat.beq (lk ONE SL.1 SL.2.1 SL.2.2 (nthD 0 ab 0)) A)
      (Nat.beq (lk ONE SL.1 SL.2.1 SL.2.2 (nthD 0 ab 1)) B) = true) :
    clK mul ONE A B R pw hs X es lp ab = true := by
  unfold clK
  rw [mapS_eq]
  change andB (entsAll mul ONE R pw X es) (runP mul ONE lp (clInit ONE R hs es).1
    (clInit ONE R hs es).2.1 (clInit ONE R hs es).2.2 fun bl cur n =>
      andB (Nat.beq (lk ONE bl cur n (nthD 0 ab 0)) A)
        (Nat.beq (lk ONE bl cur n (nthD 0 ab 1)) B)) = true
  rw [runP_eq, hE, hrun, hab]
  rfl

theorem clsOK_of {mul : Nat → Nat → Nat} {ONE A B : Nat} {R : Nat → Nat} {pw : List (List Nat)}
    {hs wr : List Nat} {lp : List (List (Nat × Nat))} {lab : List (List Nat)} :
    ∀ (ce : List (List (List Nat))) (k : Nat), ce.length + k = 5 →
      (∀ t < ce.length, nthD List.nil lp (k + t) = List.nil ∨
        clK mul ONE A B R pw hs (R (nthD 0 wr (k + t))) (nthD List.nil ce t)
          (nthD List.nil lp (k + t)) (nthD List.nil lab (k + t)) = true) →
      clsOK mul ONE A B R pw hs wr lp lab ce k = true
  | [], k, h5, _ => by
    change Nat.beq k 5 = true
    simp only [List.length_nil, Nat.zero_add] at h5
    rw [h5]
    rfl
  | es :: ce, k, h5, h => by
    change andB (sB (R (nthD 0 wr k)) fun X => List.rec (motive := fun _ => Bool) true
      (fun _ _ _ => clK mul ONE A B R pw hs X es (nthD List.nil lp k) (nthD List.nil lab k))
        (nthD List.nil lp k)) (clsOK mul ONE A B R pw hs wr lp lab ce (Nat.succ k)) = true
    rw [sB_eq]
    have h0 : List.rec (motive := fun _ => Bool) true (fun _ _ _ => clK mul ONE A B R pw hs
        (R (nthD 0 wr k)) es (nthD List.nil lp k) (nthD List.nil lab k)) (nthD List.nil lp k) =
        true := by
      have := h 0 (by simp)
      rw [Nat.add_zero] at this
      generalize nthD List.nil lp k = l at this ⊢
      cases l with
      | nil => rfl
      | cons => exact this.resolve_left (by simp)
    rw [h0, clsOK_of ce (Nat.succ k) (by simp at h5; omega) fun t ht => by
      have := h (t + 1) (by simp; omega)
      rwa [Nat.add_succ, ← Nat.succ_add] at this]
    rfl

theorem chkJCl_of {mul vec : Nat → Nat → Nat} {A B ONE L LV HV RM L9 H9 : Nat}
    {prg px : List (Nat × Nat)} {wg wr : List Nat} {hw rel fus : List (List Nat)} {bw : Nat}
    {hwm : List Nat} {ce : List (List (List Nat))} {lp : List (List (Nat × Nat))}
    {lab : List (List Nat)} (SF : Store) (HS : List Nat) (PW : List (List Nat))
    (hrun : stP mul ONE (prg ++ px) (List.nil, [B, A, ONE], 3) = SF)
    (hHS : hw.map (fun w => wordP mul ONE (fun l => lk ONE SF.1 SF.2.1 SF.2.2 (nthD 0 wg l)) w)
      = HS)
    (hPW : powsL mul ONE HS = PW) (h6 : Nat.beq HS.length 6 = true)
    (hrI : relsIdx rel 0 0 = true) (hr : ∀ t < rel.length, relE mul ONE HS PW rel t = true)
    (hwmT : hwmOK L9 H9 hwm = true) (hbw : bwOK L bw = true)
    (hinv : invOK vec LV HV RM bw HS hwm = true)
    (hf : ∀ t < fus.length,
      fusE mul ONE (lk ONE SF.1 SF.2.1 SF.2.2) PW wr (nthD List.nil fus t) = true)
    (hc5 : ce.length = 5)
    (hc : ∀ k < ce.length, nthD List.nil lp k = List.nil ∨
      clK mul ONE A B (lk ONE SF.1 SF.2.1 SF.2.2) PW HS
      (lk ONE SF.1 SF.2.1 SF.2.2 (nthD 0 wr k)) (nthD List.nil ce k) (nthD List.nil lp k)
      (nthD List.nil lab k) = true) :
    chkJCl mul vec A B ONE L LV HV RM L9 H9 prg px wg wr hw rel fus bw hwm ce lp lab = true := by
  unfold chkJCl
  rw [runP_eq, runP_eq, ← stP_append, hrun, mapS_eq, hHS, pows_eq, hPW, h6, relsOK_of rel 0 0 hrI hr, hwmT,
    hbw, hinv, fusOK_of fus hf,
    clsOK_of ce 0 (by rw [hc5]) fun t ht => by rw [Nat.zero_add]; exact hc t ht]
  rfl

end CFSG.KC.SlpPc

end

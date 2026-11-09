module

public import Certificates.Data.Kernel.Cert690.Base

public section

namespace CFSG.KC.C690

open CFSG.KC.Enum

@[expose] noncomputable def bfsPoint (ix : Nat → Nat) (gs : List Nat) (x : Nat)
    (ih : Nat → Nat → List Nat → List (Nat × Nat) → Bool) :
    Nat → Nat → List Nat → List (Nat × Nat) → Bool :=
  fun i c Er Pr => strictB i fun i => strictB c fun c =>
    bAnd(Nat.blt i c, bfsGen ix x i (fun c Er Pr => ih (Nat.succ i) c Er Pr) gs (nat_lit 0) c Er Pr)

@[expose] noncomputable def bfsSeg (ix : Nat → Nat) (gs xs : List Nat)
    (k : Nat → Nat → List Nat → List (Nat × Nat) → Bool) :
    Nat → Nat → List Nat → List (Nat × Nat) → Bool :=
  List.rec (motive := fun _ => Nat → Nat → List Nat → List (Nat × Nat) → Bool) k
    (fun x _ ih => bfsPoint ix gs x ih) xs

@[expose] noncomputable def dropR {α : Type} (n : Nat) (l : List α) : List α :=
  Nat.rec (motive := fun _ => List α → List α) (fun l => l) (fun _ ih l => ih l.tail) n l

@[expose] noncomputable def takeR {α : Type} (n : Nat) (l : List α) : List α :=
  Nat.rec (motive := fun _ => List α → List α) (fun _ => [])
    (fun _ ih l => List.rec (motive := fun _ => List α) [] (fun x t _ => x :: ih t) l) n l

theorem dropR_eq {α : Type} : ∀ (n : Nat) (l : List α), dropR n l = l.drop n
  | 0, _ => rfl
  | n + 1, [] => by
    change dropR n [] = []
    rw [dropR_eq n [], List.drop_nil]
  | n + 1, x :: t => by
    change dropR n t = t.drop n
    rw [dropR_eq n t]

theorem takeR_eq {α : Type} : ∀ (n : Nat) (l : List α), takeR n l = l.take n
  | 0, _ => rfl
  | _ + 1, [] => rfl
  | n + 1, x :: t => by
    change x :: takeR n t = x :: t.take n
    rw [takeR_eq n t]

private theorem gcSB (y : Nat) (k : Nat → Bool) : strictB y k = k y := by cases y <;> rfl

private theorem gcBA (a b : Bool) : bAnd(a, b) = (a && b) := by cases a <;> rfl

private theorem gcAK (a b : Bool) : andK a b = (a && b) := by cases a <;> rfl

private theorem gcSplit {α : Type} (L : List α) (a k : Nat) :
    L.drop a = (L.drop a).take k ++ L.drop (a + k) := by
  rw [← List.drop_drop]
  exact (List.take_append_drop k (L.drop a)).symm

private theorem gcTakeLen {α : Type} {L : List α} {a k : Nat} (h : a + k ≤ L.length) :
    ((L.drop a).take k).length = k := by
  simp only [List.length_take, List.length_drop]
  omega

theorem bfsRun_eq_seg (ix : Nat → Nat) (gs : List Nat) (n : Nat) :
    ∀ xs, bfsRun ix gs n xs = bfsSeg ix gs xs (fun _ c _ _ => Nat.beq c n)
  | [] => rfl
  | x :: xs => by
    change bfsPoint ix gs x (bfsRun ix gs n xs) = bfsPoint ix gs x (bfsSeg ix gs xs _)
    rw [bfsRun_eq_seg ix gs n xs]

theorem bfsSeg_append (ix : Nat → Nat) (gs : List Nat)
    (k : Nat → Nat → List Nat → List (Nat × Nat) → Bool) :
    ∀ xs ys, bfsSeg ix gs (xs ++ ys) k = bfsSeg ix gs xs (bfsSeg ix gs ys k)
  | [], _ => rfl
  | x :: xs, ys => by
    change bfsPoint ix gs x (bfsSeg ix gs (xs ++ ys) k) =
      bfsPoint ix gs x (bfsSeg ix gs xs (bfsSeg ix gs ys k))
    rw [bfsSeg_append ix gs k xs ys]

private theorem gcGenCons (ix : Nat → Nat) (x i : Nat)
    (k : Nat → List Nat → List (Nat × Nat) → Bool) (g : Nat) (L : List Nat) (j c : Nat)
    (Er : List Nat) (Pr : List (Nat × Nat)) :
    bfsGen ix x i k (g :: L) j c Er Pr =
      bIf(Nat.blt (ix (mulF x g)) c, bfsGen ix x i k L (Nat.succ j) c Er Pr,
        bAnd(Nat.beq (ix (mulF x g)) c,
          List.rec (motive := fun _ => Bool) false
            (fun e Er' _ => List.rec (motive := fun _ => Bool) false
              (fun p Pr' _ => bAnd(bAnd(Nat.beq e (mulF x g), bAnd(Nat.beq p.1 i, Nat.beq p.2 j)),
                bfsGen ix x i k L (Nat.succ j) (Nat.succ c) Er' Pr')) Pr) Er)) := by
  simp only [bfsGen, gcSB]

theorem bfsGen_mono {ix : Nat → Nat} {x i : Nat} {E : List Nat} {P : List (Nat × Nat)}
    {k k' : Nat → List Nat → List (Nat × Nat) → Bool}
    (hk : ∀ c, k c (E.drop c) (P.drop c) = true → k' c (E.drop c) (P.drop c) = true) :
    ∀ (L : List Nat) (j c : Nat), bfsGen ix x i k L j c (E.drop c) (P.drop c) = true →
      bfsGen ix x i k' L j c (E.drop c) (P.drop c) = true
  | [], _, c, h => hk c h
  | g :: L, j, c, h => by
    rw [gcGenCons] at h ⊢
    cases hb : Nat.blt (ix (mulF x g)) c with
    | true =>
      rw [hb] at h
      exact bfsGen_mono hk L (Nat.succ j) c h
    | false =>
      rw [hb] at h
      cases hb2 : Nat.beq (ix (mulF x g)) c with
      | false =>
        rw [hb2] at h
        exact absurd h Bool.false_ne_true
      | true =>
        rw [hb2] at h
        have hE1 : (E.drop c).tail = E.drop (c + 1) := List.tail_drop
        have hP1 : (P.drop c).tail = P.drop (c + 1) := List.tail_drop
        revert h hE1 hP1
        rcases E.drop c with _ | ⟨e, Er'⟩ <;> rcases P.drop c with _ | ⟨p, Pr'⟩ <;>
          intro h hE1 hP1
        · exact absurd h Bool.false_ne_true
        · exact absurd h Bool.false_ne_true
        · exact absurd h Bool.false_ne_true
        · change bAnd(bAnd(Nat.beq e (mulF x g), bAnd(Nat.beq p.1 i, Nat.beq p.2 j)),
            bfsGen ix x i k L (Nat.succ j) (Nat.succ c) Er' Pr') = true at h
          change bAnd(bAnd(Nat.beq e (mulF x g), bAnd(Nat.beq p.1 i, Nat.beq p.2 j)),
            bfsGen ix x i k' L (Nat.succ j) (Nat.succ c) Er' Pr') = true
          change Er' = E.drop (c + 1) at hE1
          change Pr' = P.drop (c + 1) at hP1
          rw [gcBA, Bool.and_eq_true] at h ⊢
          rw [hE1, hP1] at h ⊢
          exact ⟨h.1, bfsGen_mono hk L (Nat.succ j) (c + 1) h.2⟩

theorem bfsSeg_mono {ix : Nat → Nat} {gs : List Nat} {E : List Nat} {P : List (Nat × Nat)}
    {k k' : Nat → Nat → List Nat → List (Nat × Nat) → Bool} :
    ∀ (xs : List Nat) (i c : Nat),
      (∀ c', k (i + xs.length) c' (E.drop c') (P.drop c') = true →
        k' (i + xs.length) c' (E.drop c') (P.drop c') = true) →
      bfsSeg ix gs xs k i c (E.drop c) (P.drop c) = true →
        bfsSeg ix gs xs k' i c (E.drop c) (P.drop c) = true
  | [], _, c, hk, h => hk c h
  | x :: xs, i, c, hk, h => by
    change bfsPoint ix gs x (bfsSeg ix gs xs k) i c (E.drop c) (P.drop c) = true at h
    change bfsPoint ix gs x (bfsSeg ix gs xs k') i c (E.drop c) (P.drop c) = true
    simp only [bfsPoint, gcSB, gcBA, Bool.and_eq_true] at h ⊢
    have e : Nat.succ i + xs.length = i + (x :: xs).length := by
      rw [List.length_cons]
      omega
    refine ⟨h.1, bfsGen_mono (fun c' hc => bfsSeg_mono xs (Nat.succ i) c' (fun c'' h'' => ?_) hc)
      gs 0 c h.2⟩
    rw [e] at h'' ⊢
    exact hk c'' h''

theorem bfsSeg_chunk {ix : Nat → Nat} {gs : List Nat} {E : List Nat} {P : List (Nat × Nat)}
    {L : List Nat} {K : Nat → Nat → List Nat → List (Nat × Nat) → Bool} {a k c0 c1 : Nat}
    (hlen : a + k ≤ L.length)
    (hc : bfsSeg ix gs ((L.drop a).take k) (fun _ c _ _ => Nat.beq c c1) a c0 (E.drop c0)
      (P.drop c0) = true)
    (ht : bfsSeg ix gs (L.drop (a + k)) K (a + k) c1 (E.drop c1) (P.drop c1) = true) :
    bfsSeg ix gs (L.drop a) K a c0 (E.drop c0) (P.drop c0) = true := by
  rw [gcSplit L a k, bfsSeg_append]
  refine bfsSeg_mono _ a c0 (fun c' h' => ?_) hc
  rw [gcTakeLen hlen]
  obtain rfl := Nat.eq_of_beq_eq_true h'
  exact ht

theorem bfsSeg_chunkR {ix : Nat → Nat} {gs : List Nat} {E : List Nat} {P : List (Nat × Nat)}
    {L : List Nat} {K : Nat → Nat → List Nat → List (Nat × Nat) → Bool} {a k c0 c1 : Nat}
    (hlen : a + k ≤ L.length)
    (hc : bfsSeg ix gs (takeR k (dropR a L)) (fun _ c _ _ => Nat.beq c c1) a c0 (dropR c0 E)
      (dropR c0 P) = true)
    (ht : bfsSeg ix gs (L.drop (a + k)) K (a + k) c1 (E.drop c1) (P.drop c1) = true) :
    bfsSeg ix gs (L.drop a) K a c0 (E.drop c0) (P.drop c0) = true := by
  simp only [takeR_eq, dropR_eq] at hc
  exact bfsSeg_chunk hlen hc ht

theorem bfsSeg_base {ix : Nat → Nat} {gs : List Nat} {L : List Nat} {a n c : Nat}
    (hlen : L.length ≤ a) (hc : Nat.beq c n = true) (Er : List Nat) (Pr : List (Nat × Nat)) :
    bfsSeg ix gs (L.drop a) (fun _ c _ _ => Nat.beq c n) a c Er Pr = true := by
  rw [List.drop_eq_nil_of_le hlen]
  exact hc

theorem bfsOK_of_seg {ix : Nat → Nat} {gs E : List Nat} {P : List (Nat × Nat)}
    (h0 : E.head? = some oneF) (hp : P.head? = some (0, 0)) (hl : P.length = E.length)
    (hr : bfsSeg ix gs (E.drop 0) (fun _ c _ _ => Nat.beq c E.length) 0 1 (E.drop 1)
      (P.drop 1) = true) :
    bfsOK ix gs E P = true := by
  rw [List.drop_zero, ← bfsRun_eq_seg] at hr
  cases E with
  | nil => simp at h0
  | cons e Er =>
    cases P with
    | nil => simp at hp
    | cons p Pr =>
      simp only [List.head?_cons, Option.some.injEq] at h0 hp
      subst h0 hp
      change bAnd(bAnd(Nat.beq oneF oneF, bAnd(Nat.beq 0 0, Nat.beq 0 0)),
        bAnd(Nat.beq (Pr.length + 1) (Er.length + 1),
          bfsRun ix gs (Er.length + 1) (oneF :: Er) 0 1 Er Pr)) = true
      simp only [gcBA, Bool.and_eq_true, Nat.beq_refl]
      exact ⟨Nat.beq_eq_true_eq _ _ ▸ (by simpa using hl), hr⟩

theorem invK_append (T : IT) (n : Nat) :
    ∀ (E1 C1 I1 E2 C2 I2 : List Nat), C1.length = E1.length → I1.length = E1.length →
      invK T n E1 C1 I1 = true → invK T n E2 C2 I2 = true →
        invK T n (E1 ++ E2) (C1 ++ C2) (I1 ++ I2) = true
  | [], [], [], _, _, _, _, _, _, h2 => h2
  | [], _ :: _, _, _, _, _, hc, _, _, _ => absurd hc (by simp)
  | [], [], _ :: _, _, _, _, _, hi, _, _ => absurd hi (by simp)
  | _ :: _, [], _, _, _, _, hc, _, _, _ => absurd hc (by simp)
  | _ :: _, _ :: _, [], _, _, _, _, hi, _, _ => absurd hi (by simp)
  | x :: E1, y :: C1, j :: I1, E2, C2, I2, hc, hi, h1, h2 => by
    change andK (andK (Nat.beq (T.find y n) j) (andK (Nat.blt j n) (Nat.beq (mulF x y) oneF)))
      (invK T n E1 C1 I1) = true at h1
    change andK (andK (Nat.beq (T.find y n) j) (andK (Nat.blt j n) (Nat.beq (mulF x y) oneF)))
      (invK T n (E1 ++ E2) (C1 ++ C2) (I1 ++ I2)) = true
    rw [gcAK, Bool.and_eq_true] at h1 ⊢
    simp only [List.length_cons, Nat.add_right_cancel_iff] at hc hi
    exact ⟨h1.1, invK_append T n E1 C1 I1 E2 C2 I2 hc hi h1.2 h2⟩

theorem invK_chunk {T : IT} {n : Nat} {E C I : List Nat} {a k : Nat} (hE : a + k ≤ E.length)
    (hC : a + k ≤ C.length) (hI : a + k ≤ I.length)
    (hc : invK T n ((E.drop a).take k) ((C.drop a).take k) ((I.drop a).take k) = true)
    (ht : invK T n (E.drop (a + k)) (C.drop (a + k)) (I.drop (a + k)) = true) :
    invK T n (E.drop a) (C.drop a) (I.drop a) = true := by
  rw [gcSplit E a k, gcSplit C a k, gcSplit I a k]
  exact invK_append T n _ _ _ _ _ _ (by rw [gcTakeLen hC, gcTakeLen hE])
    (by rw [gcTakeLen hI, gcTakeLen hE]) hc ht

theorem invK_base {T : IT} {n : Nat} {E C I : List Nat} {a : Nat} (hE : E.length ≤ a)
    (hC : C.length ≤ a) (hI : I.length ≤ a) : invK T n (E.drop a) (C.drop a) (I.drop a) = true := by
  rw [List.drop_eq_nil_of_le hE, List.drop_eq_nil_of_le hC, List.drop_eq_nil_of_le hI]
  rfl

theorem invK_of_drop {T : IT} {n : Nat} {E C I : List Nat}
    (h : invK T n (E.drop 0) (C.drop 0) (I.drop 0) = true) : invK T n E C I = true := by
  rwa [List.drop_zero, List.drop_zero, List.drop_zero] at h

theorem ixAllK_append (T : IT) (n : Nat) :
    ∀ (E1 E2 : List Nat) (i : Nat), ixAllK T n E1 i = true →
      ixAllK T n E2 (i + E1.length) = true → ixAllK T n (E1 ++ E2) i = true
  | [], _, _, _, h2 => h2
  | x :: E1, E2, i, h1, h2 => by
    change strictB i (fun i => bAnd(Nat.beq (T.find x n) i, ixAllK T n E1 (Nat.succ i))) = true
      at h1
    change strictB i (fun i => bAnd(Nat.beq (T.find x n) i, ixAllK T n (E1 ++ E2) (Nat.succ i)))
      = true
    rw [gcSB, gcBA, Bool.and_eq_true] at h1 ⊢
    have e : i + (x :: E1).length = Nat.succ i + E1.length := by
      rw [List.length_cons]
      omega
    rw [e] at h2
    exact ⟨h1.1, ixAllK_append T n E1 E2 (Nat.succ i) h1.2 h2⟩

theorem ixAllK_chunk {T : IT} {n : Nat} {E : List Nat} {a k : Nat} (hE : a + k ≤ E.length)
    (hc : ixAllK T n ((E.drop a).take k) a = true) (ht : ixAllK T n (E.drop (a + k)) (a + k) = true) :
    ixAllK T n (E.drop a) a = true := by
  rw [gcSplit E a k]
  exact ixAllK_append T n _ _ a hc (by rw [gcTakeLen hE]; exact ht)

theorem ixAllK_base {T : IT} {n : Nat} {E : List Nat} {a : Nat} (hE : E.length ≤ a) :
    ixAllK T n (E.drop a) a = true := by
  rw [List.drop_eq_nil_of_le hE]
  rfl

theorem ixOK_of {S : List (Nat × Nat)} {E : List Nat}
    (hs : bAnd(sortedK S, bAnd(Nat.beq S.length E.length, Nat.ble S.length (nat_lit 65535))) = true)
    (hx : ixAllK (idxT S) E.length (E.drop 0) 0 = true) : ixOK S E = true := by
  rw [List.drop_zero] at hx
  unfold ixOK
  rw [hs]
  exact hx

end CFSG.KC.C690

end

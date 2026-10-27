module

public import CFSG.Quasithin.Background.RonanH154Chain
public import CFSG.Quasithin.Background.RonanH154Xor
public import CFSG.Certificates.Kernel.Common.Loop

public section

namespace CFSG.Quasithin.RonanH154.HypK

open CFSG.Quasithin.H.Mathieu CFSG.Quasithin.RonanH163 CFSG.KC.Loop

@[expose] def genTab : List (List ℕ) :=
  [[], [2, 4, 8, 16], [1, 4, 8, 16], [3, 4, 8, 16], [1, 2, 8, 16], [2, 5, 8, 16], [1, 6, 8, 16],
    [3, 5, 8, 16], [1, 2, 4, 16], [2, 4, 9, 16], [1, 4, 10, 16], [3, 4, 9, 16], [1, 2, 12, 16],
    [2, 5, 9, 16], [1, 6, 10, 16], [3, 5, 9, 16], [1, 2, 4, 8], [2, 4, 8, 17], [1, 4, 8, 18],
    [3, 4, 8, 17], [1, 2, 8, 20], [2, 5, 8, 17], [1, 6, 8, 18], [3, 5, 8, 17], [1, 2, 4, 24],
    [2, 4, 9, 17], [1, 4, 10, 18], [3, 4, 9, 17], [1, 2, 12, 20], [2, 5, 9, 17], [1, 6, 10, 18],
    [3, 5, 9, 17]]

@[expose] noncomputable def fixAll (G : List ℕ) (m : ℕ) : Bool :=
  List.rec (motive := fun _ => Bool) true
    (fun g _ ih => bAnd(Nat.beq (act10 (nq2Arr g) m) m, ih)) G

@[expose] noncomputable def memB (m : ℕ) (l : List ℕ) : Bool :=
  List.rec (motive := fun _ => Bool) false
    (fun x _ ih => Bool.rec (motive := fun _ => Bool) ih true (Nat.beq x m)) l

@[expose] noncomputable def fixGensB (L G : List ℕ) : Bool :=
  allBelow 1024 16 (fun m => bIf(fixAll G m, memB m (combos L), true))

theorem bAnd_tt {a b : Bool} (h : bAnd(a, b) = true) : a = true ∧ b = true := by
  cases a <;> cases b <;> simp_all

theorem bIf_tt {c t : Bool} (h : bIf(c, t, true) = true) (hc : c = true) : t = true := by
  subst hc
  exact h

theorem allBelow_tt {m hi : Nat} {f : Nat → Bool} (h : allBelow m hi f = true) :
    ∀ i < m, i < 64 * hi → f i = true := by
  have inner : ∀ (hh : Nat) (n : Nat), Nat.rec (motive := fun _ => Bool) true (fun l ih2 =>
      bAnd((fun i => bIf(Nat.blt i m, f i, true)) (Nat.add (Nat.shiftLeft hh 6) l), ih2)) n = true →
      ∀ l < n, Nat.add (Nat.shiftLeft hh 6) l < m → f (Nat.add (Nat.shiftLeft hh 6) l) = true := by
    intro hh n
    induction n with
    | zero => intro _ l hl; omega
    | succ n ih =>
      intro hn l hl hlm
      obtain ⟨h1, h2⟩ := bAnd_tt hn
      rcases Nat.lt_succ_iff_lt_or_eq.1 hl with hl | rfl
      · exact ih h2 l hl hlm
      · exact bIf_tt h1 (Nat.blt_eq.mpr hlm)
  have outer : ∀ n, Nat.rec (motive := fun _ => Bool) true (fun hh ih => bAnd(
      Nat.rec (motive := fun _ => Bool) true (fun l ih2 =>
        bAnd((fun i => bIf(Nat.blt i m, f i, true)) (Nat.add (Nat.shiftLeft hh 6) l), ih2)) 64,
        ih)) n = true → ∀ hh < n, ∀ l < 64, Nat.add (Nat.shiftLeft hh 6) l < m →
          f (Nat.add (Nat.shiftLeft hh 6) l) = true := by
    intro n
    induction n with
    | zero => intro _ hh hhh; omega
    | succ n ih =>
      intro hn hh hhh l hl hlm
      obtain ⟨h1, h2⟩ := bAnd_tt hn
      rcases Nat.lt_succ_iff_lt_or_eq.1 hhh with hhh | rfl
      · exact ih h2 hh hhh l hl hlm
      · exact inner _ 64 h1 l hl hlm
  intro i him hih
  have e : Nat.add (Nat.shiftLeft (i / 64) 6) (i % 64) = i := by
    change (i / 64) <<< 6 + i % 64 = i
    rw [Nat.shiftLeft_eq]
    omega
  have := outer hi h (i / 64) (by omega) (i % 64) (Nat.mod_lt _ (by norm_num)) (by rw [e]; exact him)
  rwa [e] at this

theorem fixAll_of {G : List ℕ} {m : ℕ} (h : ∀ g ∈ G, act10 (nq2Arr g) m = m) :
    fixAll G m = true := by
  induction G with
  | nil => rfl
  | cons g G ih =>
    have h1 : Nat.beq (act10 (nq2Arr g) m) m = true := by
      rw [Nat.beq_eq]
      exact h g (List.mem_cons_self ..)
    have h2 := ih (fun x hx => h x (List.mem_cons_of_mem _ hx))
    change Bool.rec (motive := fun _ => Bool) false (fixAll G m) (Nat.beq (act10 (nq2Arr g) m) m) = true
    rw [h1, h2]

theorem memB_sound {m : ℕ} {l : List ℕ} (h : memB m l = true) : m ∈ l := by
  induction l with
  | nil =>
    change false = true at h
    exact absurd h Bool.false_ne_true
  | cons x l ih =>
    change Bool.rec (motive := fun _ => Bool) (memB m l) true (Nat.beq x m) = true at h
    cases hx : Nat.beq x m
    · rw [hx] at h
      exact List.mem_cons_of_mem _ (ih h)
    · rw [Nat.eq_of_beq_eq_true hx]
      exact List.mem_cons_self ..

theorem fixed_of_gens {h : ℕ} {L G : List ℕ} (hG : ∀ g ∈ G, g < 32 ∧ dot5 h g = false)
    (hc : fixGensB L G = true) :
    ∀ m < 2 ^ 10, (∀ u < 32, dot5 h u = false → act10 (nq2Arr u) m = m) → m ∈ combos L := by
  intro m hm hfix
  have h1 := allBelow_tt hc m (by simpa using hm) (by simpa using hm)
  exact memB_sound (bIf_tt h1 (fixAll_of fun g hg => hfix g (hG g hg).1 (hG g hg).2))

theorem xor32_val (s t : Fin 32) : (RonanH143.xor32 s t).val = s.val ^^^ t.val := by
  have hs : s.val < 2 ^ 5 := s.isLt
  have ht : t.val < 2 ^ 5 := t.isLt
  have h : s.val ^^^ t.val < 2 ^ 5 := Nat.xor_lt_two_pow hs ht
  exact Nat.mod_eq_of_lt h

theorem xor32_self (s : Fin 32) : RonanH143.xor32 s s = 0 :=
  Fin.ext (by rw [xor32_val, Nat.xor_self]; rfl)

theorem xor32_zero (s : Fin 32) : RonanH143.xor32 s 0 = s :=
  Fin.ext (by rw [xor32_val, Fin.val_zero, Nat.xor_zero])

theorem zero_xor32 (s : Fin 32) : RonanH143.xor32 0 s = s :=
  Fin.ext (by rw [xor32_val, Fin.val_zero, Nat.zero_xor])

theorem xor32_comm (s t : Fin 32) : RonanH143.xor32 s t = RonanH143.xor32 t s :=
  Fin.ext (by rw [xor32_val, xor32_val, Nat.xor_comm])

theorem xor32_assoc (s t r : Fin 32) :
    RonanH143.xor32 (RonanH143.xor32 s t) r = RonanH143.xor32 s (RonanH143.xor32 t r) :=
  Fin.ext (by rw [xor32_val, xor32_val, xor32_val, xor32_val, Nat.xor_assoc])

theorem xor32_cancel_left (u v : Fin 32) : RonanH143.xor32 u (RonanH143.xor32 u v) = v := by
  rw [← xor32_assoc, xor32_self, zero_xor32]

theorem xor32_cancel_left' (u v : Fin 32) : RonanH143.xor32 v (RonanH143.xor32 u v) = u := by
  rw [xor32_comm u v, xor32_cancel_left]

theorem xor32_cancel_right (u v : Fin 32) : RonanH143.xor32 (RonanH143.xor32 u v) u = v := by
  rw [xor32_comm, xor32_cancel_left]

theorem xor32_cancel_right' (u v : Fin 32) : RonanH143.xor32 (RonanH143.xor32 u v) v = u := by
  rw [xor32_assoc, xor32_self, xor32_zero]

theorem xor32_closed4 (u v s t : Fin 32) (hs : s = 0 ∨ s = u ∨ s = v ∨ s = RonanH143.xor32 u v)
    (ht : t = 0 ∨ t = u ∨ t = v ∨ t = RonanH143.xor32 u v) :
    RonanH143.xor32 s t = 0 ∨ RonanH143.xor32 s t = u ∨ RonanH143.xor32 s t = v ∨
      RonanH143.xor32 s t = RonanH143.xor32 u v := by
  rcases hs with rfl | rfl | rfl | rfl <;> rcases ht with rfl | rfl | rfl | rfl
  all_goals simp only [xor32_self, xor32_zero, zero_xor32, xor32_cancel_left, xor32_cancel_left',
    xor32_cancel_right, xor32_cancel_right', xor32_comm, eq_self_iff_true, true_or, or_true]

end CFSG.Quasithin.RonanH154.HypK

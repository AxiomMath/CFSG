module

public import Certificates.Data.Kernel.LyS0.Check

public section

namespace CFSG.KD.LyS0

open CFSG.KC.Enum

@[expose] noncomputable def parseW (f : Nat → Nat) (n : Nat) (cs : List Char) :
    Nat → Nat → Bool → Bool :=
  List.rec (motive := fun _ => Nat → Nat → Bool → Bool)
    (fun k cur inN => bIf(inN, bAnd(Nat.beq cur (f k), Nat.beq (Nat.succ k) n), Nat.beq k n))
    (fun ch _ ih k cur inN => strictB (Char.toNat ch) (fun c =>
      bIf(bAnd(Nat.ble (nat_lit 48) c, Nat.ble c (nat_lit 57)),
        strictB (Nat.add (Nat.mul cur (nat_lit 10)) (Nat.sub c (nat_lit 48))) (fun cur' =>
          ih k cur' true),
        bIf(bIf(Nat.beq c (nat_lit 32), true, Nat.beq c (nat_lit 10)),
          bIf(inN, bAnd(Nat.beq cur (f k),
              strictB (Nat.succ k) (fun k' => ih k' (nat_lit 0) false)),
            ih k (nat_lit 0) false),
          false))))
    cs

theorem strictB_eq'' (y : Nat) (k : Nat → Bool) : strictB y k = k y := by
  cases y <;> rfl

theorem bAnd_iff' {a b : Bool} : bAnd(a, b) = true ↔ a = true ∧ b = true := by
  cases a <;> cases b <;> simp

theorem decL_snoc (l : List Char) (c : Char) : decL (l ++ [c]) = decL l * 10 + (c.toNat - 48) := by
  unfold decL
  rw [List.foldl_append]
  rfl

theorem char_eq_of_toNat' {a b : Char} (h : a.toNat = b.toNat) : a = b :=
  Char.ext (UInt32.toNat_inj.mp h)

theorem listT_cons (f : Nat → Nat) (x : Nat) (xs : List Nat) (k n : Nat) :
    listT f (x :: xs) k n = bAnd(Nat.beq x (f k), listT f xs (Nat.succ k) n) := rfl

theorem isDigit_iff (ch : Char) : ch.isDigit = true ↔ 48 ≤ ch.toNat ∧ ch.toNat ≤ 57 := by
  simp only [Char.isDigit, Bool.and_eq_true, decide_eq_true_eq, ge_iff_le, UInt32.le_iff_toNat_le]
  rfl

theorem char_of_toNat {ch : Char} {c : Char} (h : ch.toNat = c.toNat) : ch = c :=
  char_eq_of_toNat' h

theorem splitSp_cons_ne (x : Char) (xs acc : List Char) (hx : x ≠ ' ') :
    splitSp ' ' (x :: xs) acc = splitSp ' ' xs (x :: acc) := by
  simp [splitSp, hx]

theorem splitSp_cons_sp (xs acc : List Char) :
    splitSp ' ' (' ' :: xs) acc = acc.reverse :: splitSp ' ' xs [] := by
  simp [splitSp]

theorem parseW_sound (f : Nat → Nat) (n : Nat) :
    ∀ (cs : List Char) (k : Nat) (acc : List Char),
      parseW f n cs k (decL acc.reverse) (!acc.isEmpty) = true →
      textOK cs = true ∧
        listT f (((splitSp ' ' (cs.map nlSp) acc).filter fun l => !l.isEmpty).map decL) k n = true
  | [], k, acc, h => by
    refine ⟨rfl, ?_⟩
    rw [List.map_nil]
    cases acc with
    | nil => exact h
    | cons a acc' =>
      have h' : bAnd(Nat.beq (decL (a :: acc').reverse) (f k), Nat.beq (Nat.succ k) n) = true := h
      have hs : splitSp ' ' [] (a :: acc') = [(a :: acc').reverse] := rfl
      have hne : (!((a :: acc').reverse).isEmpty) = true := by simp
      rw [hs, List.filter_cons_of_pos (p := fun (l : List Char) => !l.isEmpty) hne, List.filter_nil,
        List.map_cons, List.map_nil, listT_cons]
      exact h'
  | ch :: cs, k, acc, h => by
    change strictB (Char.toNat ch) (fun c =>
      bIf(bAnd(Nat.ble (nat_lit 48) c, Nat.ble c (nat_lit 57)),
        strictB (Nat.add (Nat.mul (decL acc.reverse) (nat_lit 10)) (Nat.sub c (nat_lit 48)))
          (fun cur' => parseW f n cs k cur' true),
        bIf(bIf(Nat.beq c (nat_lit 32), true, Nat.beq c (nat_lit 10)),
          bIf((!acc.isEmpty), bAnd(Nat.beq (decL acc.reverse) (f k),
              strictB (Nat.succ k) (fun k' => parseW f n cs k' (nat_lit 0) false)),
            parseW f n cs k (nat_lit 0) false),
          false))) = true at h
    rw [strictB_eq''] at h
    simp only [strictB_eq''] at h
    by_cases hd : 48 ≤ ch.toNat ∧ ch.toNat ≤ 57
    · have e1 : Nat.ble 48 ch.toNat = true := Nat.ble_eq.mpr hd.1
      have e2 : Nat.ble ch.toNat 57 = true := Nat.ble_eq.mpr hd.2
      rw [e1, e2] at h
      have h' : parseW f n cs k (decL (ch :: acc).reverse) (!(ch :: acc).isEmpty) = true := by
        rw [List.reverse_cons, decL_snoc]
        exact h
      obtain ⟨ht, hl⟩ := parseW_sound f n cs k (ch :: acc) h'
      have hnl : ch ≠ '\n' := fun e => by rw [e] at hd; simp at hd
      have hsp : ch ≠ ' ' := fun e => by rw [e] at hd; simp at hd
      refine ⟨?_, ?_⟩
      · simp only [textOK, List.all_cons, (isDigit_iff ch).2 hd, Bool.true_or, Bool.true_and]
        exact ht
      · rw [List.map_cons, show nlSp ch = ch by simp [nlSp, hnl], splitSp_cons_ne _ _ _ hsp]
        exact hl
    · have e0 : bAnd(Nat.ble (nat_lit 48) ch.toNat, Nat.ble ch.toNat (nat_lit 57)) = false := by
        cases h1 : Nat.ble 48 ch.toNat <;> cases h2 : Nat.ble ch.toNat 57 <;> try rfl
        exact absurd ⟨Nat.ble_eq.mp h1, Nat.ble_eq.mp h2⟩ hd
      rw [e0] at h
      have hsep : ch.toNat = 32 ∨ ch.toNat = 10 := by
        cases h3 : Nat.beq ch.toNat 32
        · cases h4 : Nat.beq ch.toNat 10
          · rw [h3, h4] at h; exact Bool.noConfusion h
          · exact Or.inr (Nat.eq_of_beq_eq_true h4)
        · exact Or.inl (Nat.eq_of_beq_eq_true h3)
      have e3 : bIf(Nat.beq ch.toNat (nat_lit 32), true, Nat.beq ch.toNat (nat_lit 10)) = true := by
        rcases hsep with e | e <;> rw [e] <;> rfl
      rw [e3] at h
      have hnl : nlSp ch = ' ' := by
        rcases hsep with e | e
        · rw [char_of_toNat (c := ' ') e]; rfl
        · rw [char_of_toNat (c := '\n') e]; rfl
      have htx : (ch.isDigit || ch == ' ' || ch == '\n') = true := by
        rcases hsep with e | e
        · rw [char_of_toNat (c := ' ') e]; rfl
        · rw [char_of_toNat (c := '\n') e]; rfl
      rw [List.map_cons, hnl, splitSp_cons_sp]
      cases acc with
      | nil =>
        obtain ⟨ht, hl⟩ := parseW_sound f n cs k [] h
        refine ⟨?_, ?_⟩
        · simp only [textOK, List.all_cons, htx, Bool.true_and]; exact ht
        · rw [List.filter_cons_of_neg (p := fun (l : List Char) => !l.isEmpty) (by simp)]
          exact hl
      | cons a acc' =>
        have h' : bAnd(Nat.beq (decL (a :: acc').reverse) (f k),
            parseW f n cs (Nat.succ k) (decL ([] : List Char).reverse)
              (!([] : List Char).isEmpty)) = true := h
        obtain ⟨hb, hr⟩ := bAnd_iff'.1 h'
        obtain ⟨ht, hl⟩ := parseW_sound f n cs (Nat.succ k) [] hr
        refine ⟨?_, ?_⟩
        · simp only [textOK, List.all_cons, htx, Bool.true_and]; exact ht
        · rw [List.filter_cons_of_pos (p := fun (l : List Char) => !l.isEmpty) (by simp), List.map_cons,
            listT_cons]
          exact bAnd_iff'.2 ⟨hb, hl⟩

theorem parseOK_of_parseW {f : Nat → Nat} {cs : List Char} {n : Nat}
    (h : parseW f n cs (nat_lit 0) (nat_lit 0) false = true) : parseOK f cs n = true := by
  obtain ⟨ht, hl⟩ := parseW_sound f n cs 0 [] h
  unfold parseOK natsL
  rw [ht, hl]
  rfl

end CFSG.KD.LyS0

end

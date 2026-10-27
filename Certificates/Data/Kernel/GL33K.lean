module

public noncomputable section

namespace CFSG.KC.GL33K

@[expose] def mul9 (x0 x1 x2 x3 x4 x5 x6 x7 x8 y0 y1 y2 y3 y4 y5 y6 y7 y8 : Nat) : Nat :=
  (x0 * y0 + x1 * y3 + x2 * y6) % 3 + 3 * ((x0 * y1 + x1 * y4 + x2 * y7) % 3 +
  3 * ((x0 * y2 + x1 * y5 + x2 * y8) % 3 + 3 * ((x3 * y0 + x4 * y3 + x5 * y6) % 3 +
  3 * ((x3 * y1 + x4 * y4 + x5 * y7) % 3 + 3 * ((x3 * y2 + x4 * y5 + x5 * y8) % 3 +
  3 * ((x6 * y0 + x7 * y3 + x8 * y6) % 3 + 3 * ((x6 * y1 + x7 * y4 + x8 * y7) % 3 +
  3 * ((x6 * y2 + x7 * y5 + x8 * y8) % 3 + 3 * 0))))))))

@[expose] def mulK (a b : Nat) : Nat :=
  mul9 (a / 1 % 3) (a / 3 % 3) (a / 9 % 3) (a / 27 % 3) (a / 81 % 3) (a / 243 % 3)
    (a / 729 % 3) (a / 2187 % 3) (a / 6561 % 3)
    (b / 1 % 3) (b / 3 % 3) (b / 9 % 3) (b / 27 % 3) (b / 81 % 3) (b / 243 % 3)
    (b / 729 % 3) (b / 2187 % 3) (b / 6561 % 3)

@[expose] def oneK : Nat := 6643

@[expose] def conjK (n n' y : Nat) : Nat := mulK (mulK n y) n'

@[expose] def powK (a : Nat) (e : Nat) : Nat := Nat.rec oneK (fun _ acc => mulK acc a) e

@[expose] def bitK (M c : Nat) : Bool := Nat.testBit M c

@[expose] def allK {α : Type} (p : α → Bool) (L : List α) : Bool :=
  List.rec true (fun c _ ih => p c && ih) L

@[expose] def maskK (L : List Nat) : Nat := List.rec 0 (fun c _ ih => ih ||| 2 ^ c) L

@[expose] def genK (g₁ g₂ l : Nat) : Nat := if l == 0 then g₁ else g₂

@[expose] def treeK (g₁ g₂ M : Nat) (R : List (Nat × Nat × Nat)) : Nat → Bool :=
  List.rec (fun S => S == M)
    (fun r _ ih S => bitK S r.2.1 && !bitK S r.1 && r.1 == mulK r.2.1 (genK g₁ g₂ r.2.2) &&
      ih (S ||| 2 ^ r.1)) R

@[expose] def closK (g₁ g₂ M : Nat) (R : List (Nat × Nat × Nat)) : Bool :=
  bitK M (mulK oneK g₁) && bitK M (mulK oneK g₂) &&
    allK (fun r => bitK M (mulK r.1 g₁) && bitK M (mulK r.1 g₂)) R

@[expose] def memK (g₁ g₂ n M : Nat) (R : List (Nat × Nat × Nat)) : Bool :=
  R.length + 1 == n && treeK g₁ g₂ M R (2 ^ oneK) && closK g₁ g₂ M R

@[expose] def setK (M : Nat) (L : List Nat) : Nat → Bool :=
  List.rec (fun S => S == M) (fun c _ ih S => !bitK S c && ih (S ||| 2 ^ c)) L

@[expose] def cnjK (n₁ n₁' n₂ n₂' l p : Nat) : Nat :=
  if l == 0 then conjK n₁ n₁' p else conjK n₂ n₂' p

@[expose] def elemK (c : Nat) (L : List Nat) : Bool := List.rec false (fun d _ ih => c == d || ih) L

@[expose] def orbK (n₁ n₁' n₂ n₂' H : Nat) (X T : List Nat) (R : List (Nat × Nat × Nat)) :
    Nat → Bool :=
  List.rec (fun A => allK (fun t => bitK H t || bitK A t) T)
    (fun r _ ih A =>
      (r.2.2 == 2 && elemK r.1 X || bitK A r.2.1 && r.1 == cnjK n₁ n₁' n₂ n₂' r.2.2 r.2.1) &&
        ih (A ||| 2 ^ r.1)) R

@[expose] def keyK (v₁ v₂ v₃ g g' : Nat) : Nat :=
  2 ^ conjK g g' v₁ + 2 ^ conjK g g' v₂ + 2 ^ conjK g g' v₃

@[expose] def keysK (v₁ v₂ v₃ : Nat) (R : List (Nat × Nat)) : Nat → Bool :=
  List.rec (fun _ => true)
    (fun r _ ih k => mulK r.1 r.2 == oneK && decide (k < keyK v₁ v₂ v₃ r.1 r.2) &&
      ih (keyK v₁ v₂ v₃ r.1 r.2)) R

@[expose] def evalK (a b x : Nat) (w : List (Nat × Nat)) : Nat :=
  List.rec (fun acc => acc)
    (fun l _ ih acc => ih (mulK acc (powK (if l.1 == 0 then a else if l.1 == 1 then b else x) l.2)))
    w oneK

end CFSG.KC.GL33K

end

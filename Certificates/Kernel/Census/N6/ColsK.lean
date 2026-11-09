module

public import Certificates.Data.Kernel.N6ModClass

public section

namespace CFSG.KernelN6

open CFSG.CGT.T75JM

@[expose] noncomputable def bitK (v i c : Nat) : Nat := Nat.mul (Nat.land (Nat.shiftRight v i) 1) c

@[expose] noncomputable def applyK (c : Cols) (v : Nat) : Nat :=
  Nat.xor (Nat.xor (Nat.xor (bitK v 0 c.c0) (bitK v 1 c.c1)) (bitK v 2 c.c2)) (bitK v 3 c.c3)

@[expose] noncomputable def compK (c d : Cols) : Cols :=
  ⟨applyK c d.c0, applyK c d.c1, applyK c d.c2, applyK c d.c3⟩

@[expose] noncomputable def powK (c : Cols) (n : Nat) : Cols :=
  Nat.rec (motive := fun _ => Cols) idC (fun _ p => compK c p) n

@[expose] noncomputable def evalK (X Y : Cols) (w : List Nat) : Cols :=
  List.rec (motive := fun _ => Cols) idC (fun l _ ih => compK (Bool.rec Y X (Nat.beq l 0)) ih) w

@[expose] noncomputable def unpackK (m : Nat) : Cols :=
  ⟨Nat.land m 15, Nat.land (Nat.shiftRight m 4) 15, Nat.land (Nat.shiftRight m 8) 15,
    Nat.land (Nat.shiftRight m 12) 15⟩

theorem bitK_eq (v i c : Nat) : (if v.testBit i = true then c else 0) = bitK v i c := by
  unfold bitK
  have e : Nat.land (Nat.shiftRight v i) 1 = v >>> i % 2 := Nat.and_one_is_mod _
  rw [e]
  rcases Nat.mod_two_eq_zero_or_one (v >>> i) with h | h
  · have : v.testBit i = false := by
      rw [Nat.testBit_eq_decide_div_mod_eq, ← Nat.shiftRight_eq_div_pow, h]; rfl
    rw [this, h]; simp
  · have : v.testBit i = true := by
      rw [Nat.testBit_eq_decide_div_mod_eq, ← Nat.shiftRight_eq_div_pow, h]; rfl
    rw [this, h]; simp

theorem applyC_eq (c : Cols) (v : Nat) : applyC c v = applyK c v := by
  unfold applyC applyK
  rw [bitK_eq, bitK_eq, bitK_eq, bitK_eq]
  rfl

theorem compC_eq (c d : Cols) : compC c d = compK c d := by
  simp only [compC, compK, applyC_eq]

theorem powC_eq (c : Cols) (n : Nat) : powC c n = powK c n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [powC, compC_eq, ih]; rfl

theorem evalC_eq (X Y : Cols) (w : List Nat) : evalC X Y w = evalK X Y w := by
  induction w with
  | nil => rfl
  | cons l w ih =>
    rw [evalC, compC_eq, ih]
    by_cases h : l = 0
    · subst h; rfl
    · simp only [h, ↓reduceIte]
      have : Nat.beq l 0 = false := by cases l with | zero => exact absurd rfl h | succ _ => rfl
      show _ = compK (Bool.rec Y X (Nat.beq l 0)) _
      rw [this]
      rfl

theorem land15 (m : Nat) : Nat.land m 15 = m % 16 := Nat.and_two_pow_sub_one_eq_mod m 4

theorem unpackC_eq (m : Nat) : unpackC m = unpackK m := by
  unfold unpackC unpackK
  have s : ∀ a n : Nat, Nat.shiftRight a n = a / 2 ^ n := fun a n =>
    Nat.shiftRight_eq_div_pow a n
  rw [land15, land15, land15, land15, s, s, s] <;> rfl


@[expose] noncomputable def cjK (P Pi A : Cols) : Cols := compK (compK Pi A) P

@[expose] noncomputable def isInvK (m : ℕ) : Bool :=
  eqC (compK (unpackK m) (unpackK m)) idC && !eqC (unpackK m) idC

@[expose] noncomputable def relCBK (X Y : Cols) : Bool :=
  eqC (compK X X) idC && !eqC X idC && eqC (powK Y 4) idC && eqC (powK (compK X Y) 5) idC &&
    eqC (powK (compK X (compK Y Y)) 5) idC

@[expose] noncomputable def relBK (r n : ℕ) : Bool := relCBK (repC r) (unpackK n)

@[expose] noncomputable def equivBK (X Y Q Qi : Cols) : Bool :=
  smallB Q && smallB Qi && eqC (compK Qi Q) idC && eqC (compK Q Qi) idC &&
    eqC (compK X Q) (compK Q modelX) && eqC (compK Y Q) (compK Q modelY)

@[expose] noncomputable def invRecOKK (e : ℕ) : Bool :=
  eqC (compK (unpackK (e / 65536 ^ 2 % 65536)) (unpackK (e / 65536 % 65536))) idC &&
    eqC (compK (unpackK (e / 65536 % 65536)) (unpackK (e / 65536 ^ 2 % 65536))) idC &&
    eqC (cjK (unpackK (e / 65536 % 65536)) (unpackK (e / 65536 ^ 2 % 65536)) (unpackK (e % 65536)))
      (repC (e / 65536 ^ 3))

@[expose] noncomputable def relRecOKK (e : ℕ) : Bool :=
  equivBK modelX
    (if e / 65536 ^ 3 = 0 then unpackK (e % 65536)
      else evalK modelX (unpackK (e % 65536)) twistWord)
    (unpackK (e / 65536 % 65536)) (unpackK (e / 65536 ^ 2 % 65536))

@[expose] noncomputable def invAllK (L : List ℕ) : Bool :=
  eqNL ((List.range' 0 65536).filter isInvK) (L.map (· % 65536)) && L.all invRecOKK

@[expose] noncomputable def relAllK (r : ℕ) (L : List ℕ) : Bool :=
  eqNL ((List.range' 0 65536).filter (relBK r)) (L.map (· % 65536)) && L.all relRecOKK

theorem cjC_eq (P Pi A : Cols) : cjC P Pi A = cjK P Pi A := by
  simp only [cjC, cjK, compC_eq]

theorem isInvB_eq : isInvB = isInvK := funext fun m => by
  simp only [isInvB, isInvK, compC_eq, unpackC_eq]

theorem relB_eq (r : ℕ) : relB r = relBK r := funext fun n => by
  simp only [relB, relBK, relCB, relCBK, compC_eq, powC_eq, unpackC_eq]

theorem invRecOK_eq : invRecOK = invRecOKK := funext fun e => by
  simp only [invRecOK, invRecOKK, cjC_eq, compC_eq, unpackC_eq]

theorem relRecOK_eq : relRecOK = relRecOKK := funext fun e => by
  simp only [relRecOK, relRecOKK, equivB, equivBK, compC_eq, unpackC_eq, evalC_eq]

theorem invAll_eqK (L : List ℕ) : invAll L = invAllK L := by
  rw [invAll, invAllK, isInvB_eq, invRecOK_eq]

theorem relAll_eqK (r : ℕ) (L : List ℕ) : relAll r L = relAllK r L := by
  rw [relAll, relAllK, relB_eq, relRecOK_eq]

end CFSG.KernelN6

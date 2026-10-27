module

public import Certificates.Data.Kernel.LocalQT.Perm

public section

namespace CFSG.KD.YamakiS7

open CFSG.KC.LQT.P CFSG.KC.Ord

@[expose] noncomputable def ONE : Nat := 6614517792

@[expose] noncomputable def triK (s a b c : Nat) : Nat :=
  Nat.lor (Nat.lor (Nat.shiftLeft (nat_lit 1) (img s a)) (Nat.shiftLeft (nat_lit 1) (img s b)))
    (Nat.shiftLeft (nat_lit 1) (img s c))

@[expose] noncomputable def isLine (x : Nat) : Bool :=
  orB (Nat.beq x 11) (orB (Nat.beq x 22) (orB (Nat.beq x 44) (orB (Nat.beq x 88)
    (orB (Nat.beq x 49) (orB (Nat.beq x 98) (Nat.beq x 69))))))

@[expose] noncomputable def linesK (s : Nat) : Bool :=
  andB (isLine (triK s 0 1 3)) (andB (isLine (triK s 1 2 4)) (andB (isLine (triK s 2 3 5))
    (andB (isLine (triK s 3 4 6)) (andB (isLine (triK s 4 5 0)) (andB (isLine (triK s 5 6 1))
      (isLine (triK s 6 0 2)))))))

@[expose] noncomputable def l32K (s : Nat) : Bool := andB (linesK s) (linesK (inv 7 s))

@[expose] noncomputable def letterK (s a : Nat) : Nat :=
  Bool.rec (motive := fun _ => Nat) (Bool.rec (motive := fun _ => Nat)
    (Bool.rec (motive := fun _ => Nat) (Bool.rec (motive := fun _ => Nat) s 5509254208
      (Nat.beq a 3)) 5574329408 (Nat.beq a 2)) 1244793024 (Nat.beq a 1)) 1145148608 (Nat.beq a 0)

@[expose] noncomputable def evalK (s : Nat) (w : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat) ONE (fun a _ r => mul 7 (letterK s a) r) w

@[expose] noncomputable def ord5K (y : Nat) : Bool :=
  letB (mul 7 y y) fun y2 => letB (mul 7 y2 y2) fun y4 =>
    andB (Nat.beq (mul 7 y4 y) ONE) (notB (Nat.beq y ONE))

@[expose] noncomputable def wordsK (s : Nat) (W : List (List Nat)) : Bool :=
  List.rec (motive := fun _ => Bool) false (fun w _ r => orB (letB (evalK s w) ord5K) r) W

@[expose] noncomputable def s7KWords : List (List Nat) :=
  [[4, 4], [3, 4, 3, 4], [1, 4, 2, 4, 2], [0, 4, 1, 4], [1, 4, 1, 4, 2], [1, 4, 3, 2, 4],
   [0, 4, 3, 4, 3], [0, 4, 4, 4, 4], [0, 1, 4, 4], [0, 4, 2, 3, 4], [2, 4, 4, 3], [2, 3, 4, 3, 4],
   [1, 3, 4, 3, 4], [1, 4, 1, 4], [0, 2, 4, 2, 4], [0, 1, 4, 1, 4], [1, 4, 4], [0, 2, 4],
   [0, 4, 0, 4], [1, 4, 2, 4], [0, 4, 4, 3, 3], [0, 1, 4, 0, 4], [1, 4, 3, 4, 2], [0, 4, 2, 4]]

@[expose] noncomputable def s7FW (a1 b1 a2 b2 : Nat) (W : List (List Nat)) (s : Nat) : Bool :=
  orB (Nat.beq (img s 0) 0) (orB (l32K (mul 7 (mul 7 a1 s) b1))
    (orB (l32K (mul 7 (mul 7 a2 s) b2)) (wordsK s W)))

@[expose] noncomputable def s7F (s : Nat) : Bool :=
  s7FW 3427928096 5506271264 3426912288 5473765408 s7KWords s

@[expose] noncomputable def s7K : Bool := allP 7 s7F

end CFSG.KD.YamakiS7

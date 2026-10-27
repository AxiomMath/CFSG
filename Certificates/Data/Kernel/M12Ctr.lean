module

public section

namespace Certificates.KernelM12Ctr

@[expose] noncomputable def allB (n : Nat) (p : Nat → Bool) : Bool :=
  Nat.rec true (fun k acc => p k && acc) n

@[expose] def tabs : List (List Nat) :=
  [[0, 1, 2, 3, 6, 7, 8, 10, 9, 4, 11, 5], [1, 0, 2, 3, 4, 10, 7, 6, 8, 11, 5, 9],
   [2, 3, 0, 1, 4, 10, 6, 11, 8, 9, 5, 7], [4, 8, 5, 10, 0, 2, 7, 6, 1, 11, 3, 9]]

@[expose] def ap (k x : Nat) : Nat := (tabs.getD k []).getD x x

@[expose] def evalW (w : List Nat) (x : Nat) : Nat := w.foldr ap x

@[expose] def orbW : List (List Nat) :=
  [[], [1], [2], [2, 1], [3], [3, 2], [0, 3], [0, 3, 2], [3, 1], [0, 3, 1], [3, 2, 1],
   [0, 3, 2, 1]]

@[expose] def fq (q i : Nat) : Nat := evalW (orbW.getD i []) q

@[expose] noncomputable def commB (f : Nat → Nat) : Bool :=
  allB 4 fun k => allB 12 fun i => f (ap k i) == ap k (f i)

@[expose] def enc3 (a b c : Nat) : Nat := 144 * a + 12 * b + c

@[expose] def imgF (f : Nat → Nat) (n : Nat) : Nat :=
  enc3 (f (n / 144 % 12)) (f (n / 12 % 12)) (f (n % 12))

@[expose] def push (x : Nat) (st : Nat × List Nat) (k : Nat) : Nat × List Nat :=
  match st with
  | (V, S) =>
    let y := imgF (ap k) x
    if V.testBit y then (V, S) else (V ||| (1 <<< y), y :: S)

@[expose] def step (st : Nat × List Nat) : Nat × List Nat :=
  match st with
  | (V, []) => (V, [])
  | (V, x :: S) => [0, 1, 2, 3].foldl (push x) (V, S)

@[expose] noncomputable def orbMask (x n : Nat) : Nat :=
  (Nat.rec ((1 <<< x : Nat), [x]) (fun _ st => step st) n : Nat × List Nat).1

@[expose] noncomputable def orbChk (ws : List (List Nat)) : Bool :=
  allB 12 fun i => evalW (ws.getD i []) 0 == i

@[expose] noncomputable def orbOK : Bool := orbChk orbW

@[expose] noncomputable def centOK : Bool := allB 12 fun q => q == 0 || q == 1 || !commB (fq q)

@[expose] noncomputable def tupChk (V x : Nat) (f : Nat → Nat) : Bool :=
  allB 1728 (fun n => !V.testBit n || allB 4 fun k => V.testBit (imgF (ap k) n)) &&
    V.testBit x && !V.testBit (imgF f x)

@[expose] noncomputable def tupOK : Bool := tupChk (orbMask 54 192) 54 (fq 1)

end Certificates.KernelM12Ctr

end

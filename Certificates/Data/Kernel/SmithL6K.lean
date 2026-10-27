module

public import Certificates.Data.SmithL6Check

public section

namespace CFSG.SmithL6.K

open CFSG.SmithL6
open CFSG.SmithE (tri applyCols)

@[expose] def fldW (w T s : Nat) : Nat := (T >>> (w * s)) % 2 ^ w

@[expose] def codeOf (p : Nat × Nat) : Nat := 64 * p.1 + p.2

@[expose] def conjC (p q : Nat) : Nat :=
  64 * (if form (p % 64) (q / 64) then q / 64 ^^^ p / 64 else q / 64) +
    (if form (q % 64) (p / 64) then q % 64 ^^^ p % 64 else q % 64)

@[expose] def tvImgP (C I j a : Nat) : Nat := fldW 11 I (conjC (fldW 12 C j) (fldW 12 C a))

@[expose] def validP (n : Nat) : Bool := n / 64 != 0 && n % 64 != 0 && !form (n % 64) (n / 64)

@[expose] noncomputable def pinF (f : Nat → Nat) : Nat → List Nat → Bool :=
  fun a l => List.rec (motive := fun _ => Nat → Bool) (fun _ => true)
    (fun x _ ih a => (f a == x) && ih (a + 1)) l a

@[expose] def pinTv (l : List Nat) : Bool := tvList.toList.map codeOf == l

@[expose] def pinIdx (C I : Nat) : Bool :=
  (List.range 4096).all fun n => let k := fldW 11 I n
    (k == 1953 && !validP n) || (decide (k < 1953) && fldW 12 C k == n)

@[expose] def pinMapR {β α : Type} [BEq α] (f : β → α) (src : List β) (dst : List α) (a n : Nat) :
    Bool :=
  ((src.drop a).take n).map f == (dst.drop a).take n

@[expose] def wtC (c : Nat) : Nat := wedge3 (c % 64) (c / 64 % 64) (c / 4096)

@[expose] def maskC (c : Nat) : Nat := spanMask (c % 64) (c / 64 % 64) (c / 4096)

@[expose] def annC (c : Nat) : Nat := annMaskOf (c % 64) (c / 64 % 64) (c / 4096)

@[expose] def tvA (p : Nat × Nat) (x : Nat) : Nat := if form p.2 x then x ^^^ p.1 else x

@[expose] def colsL (p : Nat × Nat) : List Nat :=
  (List.range 20).map fun t =>
    let (a, b, c) := tri[t]!
    wedge3 (tvA p (2 ^ a)) (tvA p (2 ^ b)) (tvA p (2 ^ c))

@[expose] def rev20 (x : Nat) : Nat :=
  (List.range 20).foldl (fun acc t => if x.testBit t then acc ||| 2 ^ (19 - t) else acc) 0

@[expose] def Reach (n m : Nat) (isRoot : Nat → Bool) (edge : Nat → Nat → Nat → Bool) : Prop :=
  ∀ Q : Nat → Prop, (∀ v < n, isRoot v = true → Q v) →
    (∀ g < m, ∀ u < n, ∀ v < n, edge g u v = true → Q u → Q v) → ∀ v < n, Q v

@[expose] noncomputable def walkT (n m : Nat) (edge : Nat → Nat → Nat → Bool) :
    List (Nat × Nat × Nat) → Nat → Bool :=
  fun recs => List.rec (motive := fun _ => Nat → Bool) (fun S => S == 2 ^ n - 1)
    (fun r _ ih S => S.testBit r.2.1 && decide (r.2.2 < m) && decide (r.1 < n) &&
      edge r.2.2 r.2.1 r.1 && ih (S ||| 2 ^ r.1)) recs

@[expose] def maskOf (l : List Nat) : Nat := l.foldl (fun S r => S ||| 2 ^ r) 0

@[expose] noncomputable def treeK (n m : Nat) (isRoot : Nat → Bool) (edge : Nat → Nat → Nat → Bool)
    (roots : List Nat) (recs : List (Nat × Nat × Nat)) : Bool :=
  roots.all (fun r => decide (r < n) && isRoot r) && walkT n m edge recs (maskOf roots)

end CFSG.SmithL6.K

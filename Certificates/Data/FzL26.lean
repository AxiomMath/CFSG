module

public section

namespace Certificates.FzL26

@[expose] def tabulate {α : Type} (n : Nat) (f : Nat → α) : Array α :=
  Array.ofFn (n := n) fun i => f i.val

@[expose] def f4mul (a b : Nat) : Nat :=
  (a % 2 * (b % 2) + a / 2 * (b / 2)) % 2 +
    2 * ((a % 2 * (b / 2) + a / 2 * (b % 2) + a / 2 * (b / 2)) % 2)

@[expose] def pmul (i j : Nat) : Nat :=
  ((i % 4) ^^^ (j % 4)) + 4 * ((i / 4 % 4) ^^^ (j / 4 % 4)) +
    16 * ((i / 16) ^^^ (j / 16) ^^^ f4mul (i % 4) (j / 4 % 4))

@[expose] def pinv (i : Nat) : Nat := i % 16 + 16 * ((i / 16) ^^^ f4mul (i % 4) (i / 4 % 4))

structure PCtx where
  mul : Array Nat
  inv : Array Nat

@[expose] def pctx (_ : Unit := ()) : PCtx :=
  ⟨tabulate 4096 fun k => pmul (k / 64) (k % 64), tabulate 64 pinv⟩

namespace PCtx

variable (K : PCtx)

@[expose, inline] def m (i j : Nat) : Nat := K.mul[64 * i + j]!

@[expose, inline] def v (i : Nat) : Nat := K.inv[i]!

@[expose, inline] def c (i j : Nat) : Nat := K.m (K.m i j) (K.m (K.v i) (K.v j))

end PCtx

@[expose, inline] def bit (b g : Nat) : Nat := if b = 0 then 0 else g

@[expose] def PCtx.evTab (K : PCtx) (g1 g2 g3 g4 : Nat) : Array Nat :=
  let k3 := K.c g1 g3
  let k4 := K.c g1 g4
  tabulate 64 fun x =>
    let e := (x / 16) ^^^ f4mul (x % 4) (x / 4 % 4)
    K.m (K.m (K.m (K.m (K.m (bit (x % 2) g1) (bit (x / 2 % 2) g2)) (bit (x / 4 % 2) g3))
      (bit (x / 8 % 2) g4)) (bit (e % 2) k3)) (bit (e / 2) k4)

structure AutI where
  g1 : Nat
  g2 : Nat
  g3 : Nat
  g4 : Nat
  vals : Array Nat

@[expose] def PCtx.mkA (K : PCtx) (g1 g2 g3 g4 : Nat) : AutI :=
  ⟨g1, g2, g3, g4, K.evTab g1 g2 g3 g4⟩

@[expose, inline] def AutI.ap (a : AutI) (x : Nat) : Nat := a.vals[x]!

@[expose] def rho0 (x : Nat) : Nat :=
  f4mul 3 (x % 4) + 4 * f4mul 3 (x / 4 % 4) + 16 * f4mul 2 (x / 16)

@[expose, inline] def AutI.apb (a : AutI) (b q : Nat) : Nat := if b = 0 then q else a.ap q

@[expose] def actTab (t s l : AutI) : Array Nat :=
  tabulate 512 fun k => t.apb (k / 64 % 2) (s.apb (k / 128 % 2) (l.apb (k / 256) (k % 64)))

@[expose, inline] def PCtx.em (K : PCtx) (act : Array Nat) (x y : Nat) : Nat :=
  K.m (x % 64) act[64 * (x / 64) + y % 64]! + 64 * ((x / 64) ^^^ (y / 64))

end Certificates.FzL26

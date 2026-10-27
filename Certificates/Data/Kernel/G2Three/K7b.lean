module

public import Certificates.Data.Kernel.G2Three.Defs
public import Certificates.Data.G23K7b

public section

namespace CFSG.KD.G2Three

open CFSG.CGT.PushingUpLit.CGT6.EmbModule

@[expose] noncomputable def k7bGen (G : Nat → Nat) (k : Nat) : Nat := cond (Nat.blt k 8) (G k) ONE

@[expose] noncomputable def k7bWord (G : Nat → Nat) (w : List Nat) : Nat :=
  w.foldr (fun k acc => MUL (k7bGen G k) acc) ONE

@[expose] noncomputable def k7bHg (G : Nat → Nat) (i : Nat) : Nat :=
  if i < 3 then k7bWord G (k7bU ⟨i % 3, Nat.mod_lt _ (by decide)⟩)
  else MUL (k7bWord G k7bG0)
    (MUL (k7bWord G (k7bU ⟨i % 3, Nat.mod_lt _ (by decide)⟩)) (k7bWord G (invK7b k7bG0)))

@[expose] noncomputable def k7bSlpK (G : Nat → Nat) (l : List Nat) : Nat :=
  l.foldr (fun i acc => MUL (k7bHg G i) acc) ONE

@[expose] def nzK (A p : Nat) : Bool := Nat.testBit A p || Nat.testBit A (196 + p)

@[expose] noncomputable def k7bK (G : Nat → Nat) : Bool :=
  let W := k7bWord G
  let s1 := W (k7bS 0)
  let s2 := W (k7bS 1)
  let s3 := W (k7bS 2)
  let g0 := W k7bG0
  let g0i := W (invK7b k7bG0)
  let E := [ONE, s1, s2, s3, MUL s1 s2, MUL s1 s3, MUL s2 s3, MUL s1 (MUL s2 s3)]
  Nat.beq (MUL g0 g0i) ONE &&
    Nat.beq (MUL (W (k7bU 0)) (W (k7bU 0))) ONE &&
    Nat.beq (MUL (W (k7bU 1)) (W (k7bU 1))) ONE &&
    Nat.beq (MUL (W (k7bU 2)) (W (k7bU 2))) ONE &&
    Nat.beq (MUL s1 s1) ONE && Nat.beq (MUL s2 s2) ONE && Nat.beq (MUL s3 s3) ONE &&
    Nat.beq (W (k7bU 0)) (W (swapK7b (k7bU 0))) &&
    Nat.beq (W (k7bU 1)) (W (swapK7b (k7bU 1))) &&
    Nat.beq (W (k7bU 2)) (W (swapK7b (k7bU 2))) &&
    Nat.beq s1 (W (swapK7b (k7bS 0))) && Nat.beq s2 (W (swapK7b (k7bS 1))) &&
    Nat.beq s3 (W (swapK7b (k7bS 2))) &&
    nzK (W (k7bU 0)) 4 && nzK (W (k7bU 1)) 4 && nzK (W (k7bU 2)) 2 &&
    Nat.beq (MUL s1 s2) (MUL s2 s1) && Nat.beq (MUL s1 s3) (MUL s3 s1) &&
    Nat.beq (MUL s2 s3) (MUL s3 s2) &&
    nzK s1 12 && nzK s2 2 && nzK s3 8 && nzK (MUL s1 s2) 2 &&
    nzK (MUL s1 s3) 8 && nzK (MUL s2 s3) 2 && nzK (MUL s1 (MUL s2 s3)) 2 &&
    E.any (fun e => Nat.beq e (MUL g0 (MUL s1 g0i))) &&
    E.any (fun e => Nat.beq e (MUL g0 (MUL s2 g0i))) &&
    E.any (fun e => Nat.beq e (MUL g0 (MUL s3 g0i))) &&
    Nat.beq (k7bSlpK G (k7bSlp 0)) (k7bGen G (k7bRootLetter 0)) &&
    Nat.beq (k7bSlpK G (k7bSlp 1)) (k7bGen G (k7bRootLetter 1)) &&
    Nat.beq (k7bSlpK G (k7bSlp 2)) (k7bGen G (k7bRootLetter 2)) &&
    Nat.beq (k7bSlpK G (k7bSlp 3)) (k7bGen G (k7bRootLetter 3))

end CFSG.KD.G2Three

end

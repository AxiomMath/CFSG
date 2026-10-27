module

public import CFSG.Sporadic.Co2Smith.GlU62D1Inputs
public import Certificates.Kernel.Co2Smith.Elems

public section

namespace CertificateChecks.KernelCo2Smith

open CFSG.KC.Co2InvS CFSG.KC.Co2Smith CFSG.Sporadic.Co2Smith.Native

@[expose] noncomputable def d1hK (i : Nat) : Nat := wK SM hWords[i]!

@[expose] noncomputable def d1qK (e : Nat) : Nat :=
  let m := (List.range 8).foldr (fun i acc => if (e % 256).testBit i then mulV (d1hK i) acc else acc)
    IDP
  if e / 256 == 1 then mulV (SM 0) m else m

@[expose] noncomputable def d1SZ : Nat := Nat.xor zK IDP

@[expose] noncomputable def d1eK (j : Nat) : Nat := wK LP (d1EWords.getD j [])

@[expose] noncomputable def d1eiK (j : Nat) : Nat := wK LP (d1Inv (d1EWords.getD j []))

@[expose] noncomputable def d1gK (j : Nat) : Nat := if j < 3 then d1eK j else d1eiK (j - 3)

@[expose] noncomputable def d1giK (j : Nat) : Nat := if j < 3 then d1eiK j else d1eK (j - 3)

@[expose] noncomputable def d1stepK (ent : List Nat) (s : Nat × Nat × Nat) : List Nat :=
  if s.1 == 0 then ent ++ [mulV (mulV (d1gK s.2.2) (ent.getD s.2.1 IDP)) (d1giK s.2.2)]
  else ent ++ [mulV (ent.getD s.2.1 IDP) (ent.getD s.2.2 IDP)]

@[expose] noncomputable def d1runK (start : List Nat) (l : List (Nat × Nat × Nat)) : List Nat :=
  l.foldl d1stepK start

@[expose] noncomputable def d1QK : List Nat := (List.range 512).filter fun e => commK (d1qK e) x25K

@[expose] noncomputable def d1fK (e : Nat) : Nat := cjK d1K (d1qK e)

@[expose] noncomputable def d1X0K : List Nat := (List.range 4).map (rootK 0)

@[expose] noncomputable def d1B8K : List Nat := d1X0K ++ d1X0K.map (mulV x25K)

@[expose] noncomputable def d1TgtK : List Nat :=
  [rootK 0 1, rootK 0 2, rootK 4 1, rootK 4 2, rootK 5 1, rootK 5 2]

@[expose] noncomputable def d1In (l : List Nat) (x : Nat) : Bool := l.any fun y => eqK y x

@[expose] noncomputable def d1EltK : Bool :=
  !eqK (mulV x25K d1SZ) d1SZ && d1QK.length == 128 &&
  (List.range 3).all (fun j => (d1EWords.getD j []).all (glCzLet.contains ·) &&
    commK (d1eK j) x25K && eqK (mulV (d1eK j) (d1eiK j)) IDP) &&
  (List.range 5).all fun g => (d1MarkWords.getD g []).all (glC0Let.contains ·) &&
    commK (wK LP (d1MarkWords.getD g [])) zK && commK (wK LP (d1MarkWords.getD g [])) x25K

@[expose] noncomputable def d1Lam1K : Bool :=
  (List.range d1QK.length).all fun i =>
    d1In d1X0K (d1qK (d1QK.getD i 0)) || d1In (d1runK [d1qK (d1QK.getD i 0)] (d1Lam1.getD i [])) zK

@[expose] noncomputable def d1Lam2K : Bool :=
  (List.range d1QK.length).all fun i =>
    d1In d1B8K (d1fK (d1QK.getD i 0)) ||
      d1TgtK.all (d1In (d1runK [d1fK (d1QK.getD i 0), x25K] (d1Lam2.getD i [])))

@[expose] noncomputable def d1decK (c : Nat) : Nat :=
  mulV (mulV (mulV (if c / 64 == 1 then x25K else IDP) (rootK 0 (c / 16 % 4))) (rootK 4 (c / 4 % 4)))
    (rootK 5 (c % 4))

@[expose] noncomputable def d1DecK : Bool :=
  (List.range d1QK.length).all fun i => eqK (d1decK (d1Dec.getD i 0)) (d1fK (d1QK.getD i 0))

@[expose] noncomputable def d1pK (p : List Nat) : Nat := p.foldl (fun a j => mulV a (d1eK j)) IDP

@[expose] noncomputable def d1piK (p : List Nat) : Nat :=
  p.reverse.foldl (fun a j => mulV a (d1eiK j)) IDP

@[expose] noncomputable def d1q4K (j : Nat) : Nat := rootK (if j < 2 then 1 else 2) (j % 2 + 1)

@[expose] noncomputable def d1uK (p : List Nat) : List Nat :=
  (List.range 4).map fun j => mulV (mulV (d1pK p) (d1q4K j)) (d1piK p)

@[expose] noncomputable def d1UL : List (List Nat) := d1Tree.toList.map d1uK

@[expose] noncomputable def d1Sep (u v : List Nat) : Bool :=
  (List.range 4).any fun j => !d1In d1X0K (mulV (u.getD j IDP) (v.getD j IDP))

@[expose] noncomputable def d1TreeRow (i : Nat) : Bool :=
  (d1UL.take i).all (d1Sep (d1UL.getD i []))

@[expose] noncomputable def d1TreeBlk (b : Nat) : Bool :=
  (List.range 32).all fun r => d1TreeRow (32 * b + r)

@[expose] noncomputable def d1TreeK : Bool := d1Tree.size == 576

@[expose] noncomputable def d1oK (p : List Nat) : Nat := cK (mulV (mulV (wK LP p) x25K) (wK LP (d1Inv p)))

@[expose] def d1Nodup : List Nat → Bool
  | [] => true
  | x :: l => l.all (fun y => !Nat.beq y x) && d1Nodup l

@[expose] noncomputable def d1OrbK : Bool :=
  d1Orb.size == 1260 &&
  d1Orb.toList.all (fun p => p.all (glCzLet.contains ·) &&
    eqK (mulV (wK LP p) (wK LP (d1Inv p))) IDP) &&
  d1Nodup (d1Orb.toList.map d1oK)

@[expose] noncomputable def d1phiK (s q : Nat) : Nat :=
  [q, s, q, q, q, s, alK, s, q, s, q, q, q, alK, alK].foldl mulV IDP

@[expose] noncomputable def d1InXK (r R : Nat) : Bool := (List.range 4).any fun t => eqK R (rootK r t)

@[expose] noncomputable def d1PhiK : Bool :=
  d1QK.all (fun e => d1InXK 1 (d1phiK x34K (d1qK e)) && d1InXK 2 (d1phiK x43K (d1qK e)) &&
    d1InXK 4 (d1phiK x34K (d1fK e)) && d1InXK 5 (d1phiK x43K (d1fK e))) &&
  [1, 2, 3].all fun t => d1QK.any (fun e => eqK (d1phiK x34K (d1qK e)) (rootK 1 t)) &&
    d1QK.any (fun e => eqK (d1phiK x43K (d1qK e)) (rootK 2 t)) &&
    d1QK.any (fun e => eqK (d1phiK x34K (d1fK e)) (rootK 4 t)) &&
    d1QK.any (fun e => eqK (d1phiK x43K (d1fK e)) (rootK 5 t))

@[expose] noncomputable def d1RootK : Bool :=
  [0, 1, 2, 4, 5].all (fun r => (List.range 4).all fun s =>
    (List.range 4).all fun t => s == t || !eqK (rootK r s) (rootK r t)) &&
  (List.range 18).all fun r => [1, 2, 3].all fun t => glInChart r 0 || !commK (rootK r t) zK

@[expose] noncomputable def d1bgK (g : Nat) : Nat :=
  if g < 5 then wK LP (d1MarkWords.getD g []) else if g == 5 then alK
  else rootK (d1BRoot g) (d1BPar g)

@[expose] noncomputable def d1btK (ν : List Nat) (g : Nat) : Nat :=
  if g < 6 then d1bgK g else rootK (d1BRoot g) (f4mul (d1Nu ν (d1BRoot g)) (d1BPar g))

@[expose] noncomputable def d1wK (F : Nat → Nat) (w : List Nat) : Nat :=
  w.foldl (fun a g => mulV a (F g)) IDP

@[expose] noncomputable def d1BreakK : Bool :=
  [1, 2, 3].all fun a => [1, 2, 3].all fun b => [1, 2, 3].all fun c => [1, 2, 3].all fun d =>
    (a == 1 && b == 1 && c == 1 && d == 1) || d1Break.any fun e =>
      e.1 == [a, b, c, d] && eqK (d1wK d1bgK e.2.1) (d1wK d1bgK e.2.2) &&
        !eqK (d1wK (d1btK [a, b, c, d]) e.2.1) (d1wK (d1btK [a, b, c, d]) e.2.2)

end CertificateChecks.KernelCo2Smith

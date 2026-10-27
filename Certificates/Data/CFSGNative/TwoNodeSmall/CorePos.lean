module

public import Certificates.Data.CFSGNative.TwoNodeSmall.Core

public section

namespace CFSG.TwoNodeSmall

set_option compiler.extract_closed false

structure CWit where
  psi : Word
  j : Nat
  j' : Nat

structure SPt where
  pt : Pt
  s : Nat

inductive PWitness
  | fixed
  | self_
  | transv (t : TWit)
  | cycle (c : CWit)
  | order (o : OWit)
  | weyl (c : WWit)

@[expose] def Pt.lastRefl (P : Pt) : Refl := P.gens.getD P.nFrame ⟨[], []⟩

@[expose] def Pt.alphaK (P : Pt) (k : Nat) (v : Vec) : Nat := P.dotv (P.gens.getD k ⟨[], []⟩).f v

@[expose] def Pt.hK (P : Pt) (k : Nat) : Vec := (P.gens.getD k ⟨[], []⟩).h

@[expose] def allVecsP (p : Nat) : Nat → List Vec
  | 0 => [[]]
  | n + 1 => (allVecsP p n).flatMap fun v => (List.range p).map (· :: v)

@[expose] def cartanRowP (p N i : Nat) : Vec :=
  (List.range (N - 1)).map fun j => if i = j then 2 else if i + 1 = j ∨ j + 1 = i then p - 1 else 0

@[expose] def dotP (p : Nat) (a b : Vec) : Nat :=
  (((List.range (max a.length b.length)).map fun i => a.getD i 0 * b.getD i 0).foldl (· + ·) 0) % p

@[expose] def unitP (n k : Nat) : Vec := (List.range n).map fun j => if j = k then 1 else 0

@[expose] def posOpts (p N : Nat) : List (Nat × Nat × Nat) :=
  (List.range (N - 3)).map (fun c => (c, p - 1, p - 1)) ++
    [0, N - 4].flatMap fun c => [(c, p - 1, p - 2), (c, p - 2, p - 1)]

@[expose] def natFact : Nat → Nat
  | 0 => 1
  | n + 1 => (n + 1) * natFact n

@[expose] def posBound (p N : Nat) : Nat := p ^ N * (6 * (p - 1) * natFact N)

@[expose] def posBCell (p N : Nat) : List SPt :=
  [0, 1, 2].flatMap fun s =>
    (posOpts p N).flatMap fun o =>
      (allVecsP p 4).map fun fr =>
        let inJ := fun k => s ≤ k && k < s + (N - 3)
        let outs := (List.range (N - 1)).filter fun k => !(inJ k)
        let uv : Nat → Nat × Nat := fun k =>
          if inJ k then (if k - s = o.1 then (o.2.1, o.2.2) else (0, 0))
          else if outs.head? = some k then (fr.getD 0 0, fr.getD 1 0) else (fr.getD 2 0, fr.getD 3 0)
        ⟨{ p := p, D := N, nFrame := N - 1,
           gens := (List.range (N - 1)).map (fun k => (⟨cartanRowP p N k ++ [(uv k).1], unitP N k⟩ : Refl)) ++
             [⟨(List.range (N - 1)).map (fun k => (uv k).2) ++ [2], unitP N (N - 1)⟩],
           x := (List.range (N - 1)).map (· + 1) ++ [0], bound := posBound p N }, s⟩

@[expose] def posBPts (_ : Unit := ()) : List SPt := posBCell 5 5 ++ posBCell 3 6 ++ posBCell 7 7

@[expose] def exclCell (lift : Bool) (p N : Nat) : List SPt :=
  [0, 1, 2].flatMap fun s =>
    (posOpts p N).flatMap fun o =>
      let inJ := fun k => s ≤ k && k < s + (N - 3)
      let outs := (List.range (N - 1)).filter fun k => !(inJ k)
      let pinU := fun k => if k - s = o.1 then o.2.1 else 0
      ((allVecsP p (N - 1)).filter fun c =>
          (List.range (N - 1)).all fun j => !(inJ j) || dotP p (cartanRowP p N j) c == pinU j).flatMap fun c =>
        (allVecsP p 2).map fun fr =>
          let vv : Nat → Nat := fun k =>
            if inJ k then (if k - s = o.1 then o.2.2 else 0)
            else if outs.head? = some k then fr.getD 0 0 else fr.getD 1 0
          let D := if lift then N else N - 1
          let ext := fun (v : Vec) (e : Nat) => if lift then v ++ [e] else v
          ⟨{ p := p, D := D, nFrame := N - 1,
             gens := (List.range (N - 1)).map (fun k => (⟨ext (cartanRowP p N k) (if k = 0 then 1 else 0), unitP D k⟩ : Refl)) ++
               [⟨ext ((List.range (N - 1)).map vv) 0, ext c 0⟩],
             x := ext ((List.range (N - 1)).map (· + 1)) 0, bound := posBound p N }, s⟩

@[expose] def exclPts (_ : Unit := ()) : List SPt :=
  exclCell false 5 5 ++ exclCell false 7 7 ++ exclCell true 5 5 ++ exclCell true 7 7

end CFSG.TwoNodeSmall

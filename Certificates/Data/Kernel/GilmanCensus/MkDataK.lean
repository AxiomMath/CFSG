module

public import Certificates.Data.Kernel.GilmanCensus.Twin

public section

namespace Certificates.GilmanCensusK

@[expose] def gramK (B : List (List Int)) (r s : List Int) : Int :=
  (List.range' 0 r.length).foldl (fun t i => (List.range' 0 r.length).foldl
    (fun t j => t + r.getD i 0 * (B.getD i []).getD j 0 * s.getD j 0) t) 0

@[expose] def coordsInK (emb : List (List Nat)) (hv : List Nat) (n : Nat) : Option (List Nat) :=
  let aug := (List.range n).map fun i => emb.map (·.getD i 0) ++ [hv.getD i 0]
  let rp := rowRed3K aug (emb.length + 1)
  if rp.2 == List.range emb.length then some (rp.1.map fun r => r.getD (r.length - 1) 0) else none

@[expose] def adjK (g : Nat → Nat → Int) (N : Nat) : List Nat :=
  (List.range N).map fun i =>
    (List.range N).foldl (fun m j => if g i j != 0 then m ||| bitK j else m) 0

@[expose] def linesK (d : Nat) : List (List Nat) :=
  ((List.range (3 ^ d)).map fun k => (List.range d).map fun i => k / 3 ^ (d - 1 - i) % 3).filter
    fun v => firstNZK v == 1

@[expose] def idxIK (v : List Int) : List (List Int) → Nat → Option Nat
  | [], _ => none
  | r :: rs, k => if r == v then some k else idxIK v rs (k + 1)

@[expose] def reflZK (n : Nat) (r s : List Int) (q : Int) : List Int :=
  let z := (List.range n).map fun t => s.getD t 0 - q * r.getD t 0
  if (z.find? (· != 0)).getD 0 < 0 then z.map (- ·) else z

@[expose] def reflStepK (R : List (List Int)) (g : Nat → Nat → Int) (n i : Nat)
    (st : Bool × List Nat) (j : Nat) : Bool × List Nat :=
  let a := 2 * g j i
  let b := g i i
  let ok := if (a % b != 0) = true then false else st.1
  match idxIK (reflZK n (R.getD i []) (R.getD j []) (a / b)) R 0 with
  | some k => (ok, st.2 ++ [k])
  | none => (false, st.2 ++ [0])

@[expose] def reflRowK (R : List (List Int)) (g : Nat → Nat → Int) (n N i : Nat) (ok : Bool) :
    Bool × List Nat :=
  (List.range' 0 N).foldl (reflStepK R g n i) (ok, [])

@[expose] def reflK (R : List (List Int)) (g : Nat → Nat → Int) (n N : Nat) (ok : Bool) :
    Bool × List (List Nat) :=
  (List.range' 0 N).foldl (fun st i =>
    let r := reflRowK R g n N i st.1
    (r.1, st.2 ++ [r.2])) (ok, [])

@[expose] def imod3K (x : Int) : Nat := (x % 3).toNat

@[expose] def sumK (n : Nat) (f : Nat → Int) : Int := (List.range' 0 n).foldl (fun t i => t + f i) 0

@[expose] def dotIK (v w : List Int) : Int := sumK v.length fun i => v.getD i 0 * w.getD i 0

@[expose] def fhStepK (mode n : Nat) (A B : List (List Int)) (sc : List Int) (emb : List (List Nat))
    (st : Bool × List (List Nat) × List (List Nat)) (r : List Int) :
    Bool × List (List Nat) × List (List Nat) :=
  let norm := gramK B r r
  let h := (List.range n).map fun i => 2 * r.getD i 0 * sc.getD i 0 / norm
  let f := if (mode == 2 || mode == 3) = true then r
    else (List.range n).map fun j => sumK n fun i => r.getD i 0 * (A.getD i []).getD j 0
  let hv := if (mode == 2 || mode == 3) = true then
      (List.range n).map fun i => imod3K (sumK n fun j => (A.getD i []).getD j 0 * h.getD j 0)
    else h.map imod3K
  let F := st.2.1 ++ [emb.map fun v => imod3K (dotIK f (v.map fun (x : Nat) => (x : Int)))]
  match coordsInK emb hv n with
  | some c => (st.1, F, st.2.2 ++ [c])
  | none => (false, F, st.2.2)

@[expose] def idxsK {α : Type} [BEq α] (x : α) : List α → Nat → List Nat
  | [], _ => []
  | y :: l, k => if y == x then k :: idxsK x l (k + 1) else idxsK x l (k + 1)

@[expose] def fhOkK (F H : List (List Nat)) (g : Nat → Nat → Int) (N : Nat) (ok : Bool) : Bool :=
  (List.range' 0 N).foldl (fun ok i => (List.range' 0 N).foldl (fun ok j =>
    if ((dot3K (F.getD i []) (H.getD j []) : Int) != 2 * g i j / g j j % 3) = true then false else ok)
    ok) ok

@[expose] def dedupK {α : Type} [BEq α] (l : List α) : List α :=
  l.foldl (fun acc x => if acc.contains x then acc else acc ++ [x]) []

end Certificates.GilmanCensusK

end

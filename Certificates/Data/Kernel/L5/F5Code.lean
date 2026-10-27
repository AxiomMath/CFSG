module

public import Certificates.Data.Kernel.L5.EngRec

public section

namespace CFSG.GH74.GLS.C3.Layer2.L5.Fus

open Equiv Perm CFSG.GH74.GLS.C3.Prop121 CFSG.GH74.GLS.C3.Layer2 CFSG.GH74.GLS.C3.Layer2.Model

@[expose] def enc9 (a0 a1 a2 a3 a4 a5 a6 a7 a8 : Nat) : Nat :=
  a0 + 8 * (a1 + 8 * (a2 + 8 * (a3 + 8 * (a4 + 8 * (a5 + 8 * (a6 + 8 * (a7 + 8 * a8)))))))

@[expose] def codeP (p : Amb 5) : Nat :=
  enc9 (p.1 0).val (p.1 1).val (p.1 2).val (p.1 3).val (p.1 4).val (p.2 0).val (p.2 1).val
    (p.2 2).val (p.2 3).val

@[expose] def dg (c k : Nat) : Nat := c / 8 ^ k % 8

@[expose] def mulC (a b : Nat) : Nat :=
  enc9 (dg a (dg b 0)) (dg a (dg b 1)) (dg a (dg b 2)) (dg a (dg b 3)) (dg a (dg b 4))
    (dg a (5 + dg b 5)) (dg a (5 + dg b 6)) (dg a (5 + dg b 7)) (dg a (5 + dg b 8))

@[expose] def zN (k : Nat) : Nat :=
  if k = 0 then 1 else if k = 1 then 0 else if k = 2 then 3 else if k = 3 then 2 else k

@[expose] def zC (c : Nat) : Bool :=
  dg c 1 == zN (dg c 0) && dg c 0 == zN (dg c 1) && dg c 3 == zN (dg c 2) &&
    dg c 2 == zN (dg c 3) && dg c 4 == zN (dg c 4)

variable {n : Nat}

@[expose] def f5P (E : Nat → Idx n) (tC : List Nat) (fC : List (Nat × Nat)) :
    List (Idx n × Idx n) :=
  tC.flatMap fun tc => fC.filterMap fun gc =>
    if zC (mulC (mulC gc.1 tc) gc.2) then some (E tc, E (mulC (mulC gc.1 tc) gc.2)) else none

@[expose] def dedupGo : Nat → List (Idx n × Idx n) → List (Idx n × Idx n)
  | _, [] => []
  | b, p :: ps =>
    if b.testBit (p.1.v * n + p.2.v) then dedupGo b ps
    else p :: dedupGo (b ||| 2 ^ (p.1.v * n + p.2.v)) ps

@[expose] def dedupN (ps : List (Idx n × Idx n)) : List (Idx n × Idx n) := (dedupGo 0 ps).reverse

@[expose] def addNewN (vis : Nat) (new : List (Idx n)) : List (Idx n) → Nat × List (Idx n)
  | [] => (vis, new)
  | y :: ys => if vis.testBit y.v then addNewN vis new ys else addNewN (vis ||| 2 ^ y.v) (y :: new) ys

@[expose] def roundN (steps : Idx n → List (Idx n)) (vis : Nat) (new : List (Idx n)) :
    List (Idx n) → Nat × List (Idx n)
  | [] => (vis, new)
  | x :: xs => roundN steps (addNewN vis new (steps x)).1 (addNewN vis new (steps x)).2 xs

@[expose] def bfsGoN (steps : Idx n → List (Idx n)) :
    Nat → Nat → List (Idx n) → List (Idx n) → List (Idx n)
  | 0, _, _, acc => acc
  | fuel + 1, vis, frontier, acc =>
    match frontier with
    | [] => acc
    | _ =>
      let st := roundN steps vis [] frontier
      bfsGoN steps fuel st.1 st.2 (acc ++ st.2)

@[expose] def bfsN (steps : Idx n → List (Idx n)) (r : Idx n) : List (Idx n) :=
  bfsGoN steps n (2 ^ r.v) [r] [r]

@[expose] def repsGoN (steps : Idx n → List (Idx n)) :
    List (Idx n) → Array Bool → List (Idx n) → List (Idx n)
  | [], _, acc => acc.reverse
  | u :: us, cov, acc =>
    if cov.getD u.v false then repsGoN steps us cov acc
    else repsGoN steps us (markAll cov (bfsN steps u)) (u :: acc)

variable [Group (Idx n)]

@[expose] def fuseL (fp nb : List (Idx n × Idx n)) : List (Idx n × Idx n) :=
  dedupN ((fp ++ nb).filter fun p => isInv p.1 && isInv p.2)

@[expose] def fusChkL (fs : List (Idx n × Idx n)) (e0 : Idx n) (reps : List (Idx n))
    (ciA : Array Nat) (invs : List (Idx n)) (x : Idx n) : Bool :=
  let st := stepsOf fs
  let rs := repsGoN st ((elemsI n).filter isInv) (Array.replicate n false) []
  let ms := rs.map (bfsN st)
  decide ((elemsI n).filter isInv = invs) && decide (rs = reps) && decide (ciArrOf ms = ciA) &&
    decide (e0 = x) &&
    reps.all isInv &&
    (List.range reps.length).all (fun k => decide (ciA.getD (reps.getD k 1).v 0 = k)) &&
    invs.all (fun u => decide (ciA.getD u.v 0 < reps.length) &&
      (ms.getD (ciA.getD u.v 0) []).contains u) &&
    isInv x

end CFSG.GH74.GLS.C3.Layer2.L5.Fus

end

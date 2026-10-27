module

public import Certificates.Data.Kernel.PermCent.CV
public import CFSG.GH74.GLS.C3.Layer2.L5C0Inputs

public section

namespace CFSG.Certificates.Kernel.L5S

open CFSG.Certificates.Kernel.PkCV CFSG.GH74.GLS.C3.Layer2.L5

instance small16 : Small 16 := ⟨by decide⟩

@[expose] noncomputable def d8C : List (CV 16) := d8L.map cOf

@[expose] noncomputable def sh0C : List (CV 16) :=
  (List.finRange 16).flatMap fun v => d8C.map fun d => cOf (tr16 v) * d

@[expose] def fld (w P k : Nat) : Nat := (P >>> (w * k)) % 2 ^ w

@[expose] def pack (w : Nat) : List Nat → Nat
  | [] => 0
  | x :: l => x + 2 ^ w * pack w l

@[expose] noncomputable def dActP : Nat :=
  pack 4 ((List.range 8).flatMap fun i => (List.range 16).map fun v => img 16 (d8C.getD i 1).1 v)

@[expose] noncomputable def dMulP : Nat :=
  pack 3 ((List.range 8).flatMap fun i => (List.range 8).map fun j =>
    d8C.idxOf (d8C.getD i 1 * d8C.getD j 1))

@[expose] noncomputable def dInvP : Nat :=
  pack 3 ((List.range 8).map fun i => d8C.idxOf (d8C.getD i 1)⁻¹)

@[expose] noncomputable def mF (a b : Nat) : Nat :=
  8 * (a / 8 ^^^ fld 4 dActP (a % 8 * 16 + b / 8)) + fld 3 dMulP (a % 8 * 8 + b % 8)

@[expose] noncomputable def iF (a : Nat) : Nat :=
  8 * fld 4 dActP (fld 3 dInvP (a % 8) * 16 + a / 8) + fld 3 dInvP (a % 8)

@[expose] noncomputable def tF (n : Nat) : Nat := if n < 16384 then mF (n / 128) (n % 128) else 0

@[expose] noncomputable def iT (n : Nat) : Nat := if n < 128 then iF n else 0

@[expose] noncomputable def sh0Chk : Bool :=
  (List.range 128).all fun a =>
    decide (iF a < 128) && decide ((sh0C.getD a 1)⁻¹ = sh0C.getD (iF a) 1) &&
      (List.range 128).all fun b =>
        decide (mF a b < 128) && decide (sh0C.getD a 1 * sh0C.getD b 1 = sh0C.getD (mF a b) 1)

@[expose] def evFromT (t : Nat → Nat) (x : List Nat) (a : Nat) (w : List Nat) : Nat :=
  w.foldl (fun a k => t (a * 128 + x.getD k 0)) a

@[expose] def conjIT (t iv : Nat → Nat) (h a : Nat) : Nat := t (t (h * 128 + a) * 128 + iv h)

@[expose] def bfsWordsGoT (t : Nat → Nat) (gs : List Nat) :
    Nat → Array (Option (List Nat)) → List Nat → Array (Option (List Nat))
  | 0, W, _ => W
  | fuel + 1, W, frontier =>
    let st := frontier.foldl (fun (st : Array (Option (List Nat)) × List Nat) g =>
      (List.range gs.length).foldl (fun (st : Array (Option (List Nat)) × List Nat) k =>
        let p := t (g * 128 + gs.getD k 0)
        match st.1.getD p none with
        | some _ => st
        | none => (st.1.set! p (some ((st.1.getD g none).getD [] ++ [k])), st.2 ++ [p])) st) (W, [])
    bfsWordsGoT t gs fuel st.1 st.2

@[expose] def WdT (t : Nat → Nat) (gs : List Nat) : Array (List Nat) :=
  (bfsWordsGoT t gs 128 ((Array.replicate 128 none).set! 0 (some [])) [0]).map fun o => o.getD []

@[expose] def relsUT (t : Nat → Nat) (gs : List Nat) (W : Nat → List Nat) :
    List (List Nat × List Nat) :=
  (List.range 128).flatMap fun g => (List.range 3).filterMap fun k =>
    let p := t (g * 128 + gs.getD k 0)
    let w1 := W g ++ [k]
    let w2 := W p
    if w1 == w2 then none else some (w1, w2)

@[expose] def invLT (t : Nat → Nat) : List Nat :=
  (List.range 128).filter fun i => decide (t (i * 128 + i) = 0)

@[expose] noncomputable def RIdxC : List Nat :=
  (List.range 128).filter fun i =>
    decide (sh0C.getD i 1 ∈ (List.finRange 16).map fun v => cOf (tr16 v))

@[expose] def autPairOKT (t iv : Nat → Nat) (gs : List Nat) (W : Nat → List Nat) (x : List Nat)
    (u : Nat) : Bool :=
  decide (evFromT t x 0 (W u) = u) &&
    (List.range 3).all fun k =>
      decide (evFromT t x 0 (W (x.getD k 0)) = conjIT t iv u (gs.getD k 0))

@[expose] def twistOKT (t iv : Nat → Nat) (W : Nat → List Nat) (xs : List (List Nat))
    (ss : List Nat) (x : List Nat) (u : Nat) : Bool :=
  (List.range 4).any fun m => (List.range 128).any fun h0 =>
    (List.range 3).all (fun k => decide (conjIT t iv h0 (x.getD k 0) = (xs.getD m []).getD k 0)) &&
      decide (t (t (h0 * 128 + evFromT t x 0 (W h0)) * 128 + u) = ss.getD m 0)

@[expose] def classifyRowT (t iv : Nat → Nat) (gs : List Nat) (W : Nat → List Nat)
    (rels : List (List Nat × List Nat)) (ridx invl : List Nat) (z : Nat) (xs : List (List Nat))
    (ss : List Nat) (x0 : Nat) : Bool :=
  invl.all fun x1 => invl.all fun x2 =>
    decide (evFromT t [x0, x1, x2] 0 (W z) = 0) ||
    !(rels.all fun r => decide (evFromT t [x0, x1, x2] 0 r.1 = evFromT t [x0, x1, x2] 0 r.2)) ||
    !(ridx.any fun r => !decide (evFromT t [x0, x1, x2] 0 (W r) ∈ ridx)) ||
    (List.range 128).all fun u =>
      !(autPairOKT t iv gs W [x0, x1, x2] u) || twistOKT t iv W xs ss [x0, x1, x2] u

@[expose] def classifyT (t iv : Nat → Nat) (gs : List Nat) (W : Nat → List Nat)
    (rels : List (List Nat × List Nat)) (ridx invl : List Nat) (z : Nat) (xs : List (List Nat))
    (ss : List Nat) : Bool :=
  invl.all (classifyRowT t iv gs W rels ridx invl z xs ss)

@[expose] def gsK : List Nat := [1, 4, 24]

@[expose] def xsK : List (List Nat) := [[1, 16, 7], [1, 16, 7], [1, 48, 39], [1, 48, 39]]

@[expose] def ssK : List Nat := [0, 32, 0, 32]

@[expose] noncomputable def wdK : List (List Nat) := (WdT tF gsK).toList

@[expose] noncomputable def relsK : List (List Nat × List Nat) :=
  relsUT tF gsK fun i => wdK.getD i []

@[expose] def relK : List Nat × List Nat := ([1, 2, 0, 1, 2, 1], [0, 2, 0, 2, 1, 0])

@[expose] noncomputable def classifyK (c : Nat) : Bool :=
  (invLT tF).all fun x0 => !(x0 / 11 == c) ||
    classifyRowT tF iT gsK (fun i => wdK.getD i []) (relK :: relsK) RIdxC (invLT tF) 32 xsK ssK x0

end CFSG.Certificates.Kernel.L5S

end

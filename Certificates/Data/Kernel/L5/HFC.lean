
module

public import Certificates.Data.Kernel.L5.Sh0T
public import CFSG.GH74.GLS.C3.Layer2.L5C9Inputs

public section

namespace CFSG.Certificates.Kernel.L5H

open Equiv Perm CFSG.Certificates.Kernel.PkCV CFSG.Certificates.Kernel.L5S
  CFSG.GH74.GLS.C3.Layer2.L5 CFSG.GH74.GLS.C3.Layer2.L5.HF CFSG.GH74.GLS.C3.Layer2.Model

@[expose] noncomputable def yC : CV 16 := cOf yHat

@[expose] noncomputable def wC : CV 16 := cOf wHat

@[expose] noncomputable def cHC : CV 16 := cOf cHat

@[expose] noncomputable def twC : CV 16 := cOf twPerm

@[expose] noncomputable def n24C : List (CV 16) := n24L.map cOf

@[expose] noncomputable def G72gC : List (CV 16) := [yC, wC, n24C.getD 6 1, cHC]

@[expose] noncomputable def G72C : List (CV 16) := closureList G72gC 8

@[expose] noncomputable def G72Chk : Bool :=
  invClosedChkP G72C && n24C.all (fun a => decide (a ∈ G72C)) && decide (yC ∈ G72C) &&
    decide (wC ∈ G72C) && decide (cHC ∈ G72C) && decide (twC⁻¹ * yC * twC = yC) &&
    decide (twC⁻¹ * wC * twC = wC)

@[expose] def pN (V : Finset (Fin 16)) : Nat :=
  (List.finRange 16).foldl (fun acc i => acc ||| if i ∈ V then 2 ^ i.val else 0) 0

@[expose] noncomputable def imgN (g : CV 16) (M : Nat) : Nat :=
  (List.range 16).foldl (fun acc i => acc ||| (M >>> i) % 2 * 2 ^ img 16 g.1 i) 0

@[expose] def permN (f : Fin 16 → Fin 16) : Bool :=
  (List.finRange 16).foldl (fun acc i => acc ||| 2 ^ (f i).val) 0 == 65535

@[expose] noncomputable def orbStepN (gs : List (CV 16)) (l : List Nat) : List Nat :=
  ((l ++ l.flatMap fun M => gs.map fun g => imgN g M).dedup).take 5

@[expose] noncomputable def orbListN (gs : List (CV 16)) (k : Nat) : List Nat :=
  (orbStepN gs)^[k] [pN Qpl]

@[expose] def fam0L : List (Finset (Fin 16)) := [{0, 5, 11, 14}, {0, 7, 10, 13}, {0, 1, 2, 3}, {0, 6, 9, 15}]

@[expose] def fam1L : List (Finset (Fin 16)) := [{0, 6, 11, 13}, {0, 7, 9, 14}, {0, 5, 10, 15}, {0, 1, 2, 3}]

@[expose] noncomputable def linChkN (c : CV 16) : Bool :=
  (List.finRange 16).all fun i => (List.finRange 16).all fun j =>
    img 16 c.1 (i.val ^^^ j.val) == (img 16 c.1 i.val ^^^ img 16 c.1 j.val)

@[expose] noncomputable def fam0ChkN (c : CV 16) : Bool :=
  fam0L.all fun V => decide (imgN c (pN V) ∈ fam0L.map pN)

@[expose] noncomputable def G72LinChk : Bool := G72C.all fun c => linChkN c && fam0ChkN c

@[expose] noncomputable def allQ2C (g : Fin 16 → Fin 16 → Bool) (c : CV 16 → Bool) : Bool :=
  (List.finRange 16).all fun a => (List.finRange 16).all fun b => !(g a b) ||
    (List.finRange 16).all fun c' => (List.finRange 16).all fun d =>
      !(permN (linFun (a, b, c', d))) || c (cOf (mkPerm (linFun (a, b, c', d))))

@[expose] noncomputable def allQ2RowC (g : Fin 16 → Fin 16 → Bool) (c : CV 16 → Bool) (k : Nat) :
    Bool :=
  (List.finRange 16).all fun a => !(a.val / 4 == k) || (List.finRange 16).all fun b => !(g a b) ||
    (List.finRange 16).all fun c' => (List.finRange 16).all fun d =>
      !(permN (linFun (a, b, c', d))) || c (cOf (mkPerm (linFun (a, b, c', d))))

@[expose] noncomputable def n24PreC (x : CV 16) : Bool :=
  let A := imgN x (pN Qpl)
  !(A == pN Qpl) && (A &&& pN Qpl == 1) && (A &&& pN Ppl == 1)

@[expose] noncomputable def n24CovC (C : List (CV 16)) (tw : Bool) : Bool :=
  n24C.all fun a => decide ((if tw then twC * a * twC⁻¹ else a) ∈ C)

@[expose] def stepG (n : Nat) (mul : Nat → Nat → Nat) (gs : List Nat) (M : Nat) : Nat :=
  (List.range n).foldl (fun acc a =>
    acc ||| if M.testBit a then gs.foldl (fun acc' s => acc' ||| 2 ^ mul a s) 0 else 0) M

@[expose] def closG (n : Nat) (mul : Nat → Nat → Nat) (i1 : Nat) (gs : List Nat) (k : Nat) : Nat :=
  (stepG n mul gs)^[k] (2 ^ i1)

@[expose] noncomputable def mulGP : Nat :=
  pack 7 ((List.range 72).flatMap fun a => (List.range 72).map fun b =>
    G72C.idxOf (G72C.getD a 1 * G72C.getD b 1))

@[expose] noncomputable def mG (a b : Nat) : Nat := fld 7 mulGP (a * 72 + b)

@[expose] noncomputable def G72TabChk : Bool :=
  decide (G72C.length = 72) && decide G72C.Nodup && decide ((1 : CV 16) ∈ G72C) &&
    (List.range 72).all fun a => (List.range 72).all fun b =>
      decide (mG a b < 72) && decide (G72C.getD a 1 * G72C.getD b 1 = G72C.getD (mG a b) 1)

@[expose] noncomputable def idx72 (x : CV 16) : Nat := G72C.idxOf x

@[expose] noncomputable def covIdx (i : Nat) : Bool :=
  let M := closG 72 mG (idx72 1) [idx72 yC, idx72 wC, i] 8
  n24C.all fun a => M.testBit (idx72 a)

@[expose] noncomputable def covC (x : CV 16) : Bool :=
  if x ∈ G72C then covIdx (idx72 x) else n24CovC (closureList [yC, wC, x] 8) false

@[expose] noncomputable def n24TailC (x : CV 16) (o : List Nat) : Bool :=
  (imgN x (pN Ppl) == pN Ppl) &&
    (((fam0L.all fun F => decide (pN F ∈ o)) && covC x) ||
       ((fam1L.all fun F => decide (pN F ∈ o)) && covC (twC⁻¹ * x * twC)))

@[expose] noncomputable def n24ChkC (x : CV 16) : Bool :=
  decide ((orbListN [yC, wC, x] 3).length = 5) ||
    (let o := orbListN [yC, wC, x] 6
     decide (5 ≤ o.dedup.length) || n24TailC x o)

@[expose] noncomputable def n24EntryC (x : CV 16) : Bool := !(n24PreC x) || n24ChkC x

@[expose] noncomputable def cHatC (x : CV 16) : Bool :=
  if x ∈ G72C then
    (closG 72 mG (idx72 1) [idx72 wC, idx72 (n24C.getD 6 1), idx72 x] 8).testBit (idx72 cHC)
  else decide (cHC ∈ closureList [wC, n24C.getD 6 1, x] 8)

@[expose] noncomputable def famEntryC (x : CV 16) : Bool :=
  let f0 := fam0ChkL (ev x)
  let f1 := fam1ChkL (ev x)
  (!(f0 || f1) || (imgN x (pN Ppl) == pN Ppl)) && (!f0 || decide (x ∈ G72C)) &&
    (!f0 || decide (x ∈ n24C) || cHatC x)

@[expose] noncomputable def n24RowK (k : Nat) : Bool := allQ2RowC gN n24EntryC k

@[expose] noncomputable def famRowK (k : Nat) : Bool := allQ2RowC gFam famEntryC k

@[expose] noncomputable def mulTP : Nat :=
  pack 5 ((List.range 24).flatMap fun a => (List.range 24).map fun b =>
    n24C.idxOf (n24C.getD a 1 * n24C.getD b 1))

@[expose] noncomputable def invTP : Nat := pack 5 ((List.range 24).map fun a => n24C.idxOf (n24C.getD a 1)⁻¹)

@[expose] noncomputable def mI (a b : Nat) : Nat := fld 5 mulTP (a * 24 + b)

@[expose] noncomputable def iI (a : Nat) : Nat := fld 5 invTP a

@[expose] noncomputable def n24TabChk : Bool :=
  decide (n24C.length = 24) && decide n24C.Nodup && decide (n24C.getD 0 1 = 1) &&
    decide (n24C.getD 3 1 = yC) &&
    (List.range 24).all fun a => decide (iI a < 24) && decide ((n24C.getD a 1)⁻¹ = n24C.getD (iI a) 1) &&
      (List.range 24).all fun b =>
        decide (mI a b < 24) && decide (n24C.getD a 1 * n24C.getD b 1 = n24C.getD (mI a b) 1)

@[expose] noncomputable def d8ChkI (i j : Nat) : Bool :=
  let gs := [3, i, j]
  let M := closG 24 mI 0 gs 8
  ((List.range 24).all fun a => !(M.testBit a) || gs.all fun s =>
      M.testBit (mI a s) && M.testBit (mI a (iI s))) &&
    (let L := ((List.range 24).filter fun a => M.testBit a).map fun a => n24C.getD a 1
     !decide (L.length = 8) || (L.all (fun x => decide (x ∈ d8C)) && d8C.all fun x => decide (x ∈ L)))

@[expose] noncomputable def d8ChkAll : Bool :=
  (List.range 24).all fun i => (List.range 24).all fun j => d8ChkI i j

end CFSG.Certificates.Kernel.L5H

end

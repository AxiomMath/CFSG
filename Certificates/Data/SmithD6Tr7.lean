module

public import Certificates.Data.SmithD6Model

public noncomputable section

namespace CFSG.SmithD6

@[expose] def tr7XorSel : List Nat → Nat → Nat
  | [], _ => 0
  | b :: bs, m => (if m % 2 == 1 then b else 0) ^^^ tr7XorSel bs (m / 2)

@[expose] def tr7IndepOK (bs : List Nat) : Bool :=
  (List.range (2 ^ bs.length)).all fun m => (List.range (2 ^ bs.length)).all fun m' =>
    m == m' || tr7XorSel bs m != tr7XorSel bs m'

@[expose] def tr7Red (E : List (Nat × Nat)) (x : Nat) : Nat :=
  E.foldl (fun x e => if x.testBit e.1 then x ^^^ e.2 else x) x

@[expose] def tr7Ech (vs : List Nat) : List (Nat × Nat) :=
  vs.foldl (fun E v => let r := tr7Red E v; if r == 0 then E else E ++ [(r.log2, r)]) []

@[expose] def tr7Bs (vs : List Nat) : List Nat := (tr7Ech vs).map (·.2)

@[expose] def tr7RepLines (j : Nat) : List (Nat × Nat) :=
  if j == 0 then [(eV 0, eV 1)]
  else if j == 1 then [(eV 0, eV 1), (eV 2, eV 3)]
  else if j == 2 then [(eV 0, eV 1), (eV 2, eV 3), (eV 4, eV 5)]
  else if j == 3 then [(eV 0, eV 1), (eV 2, eV 3), (eV 4, fV 5)]
  else if j == 4 then [(eV 0, eV 1), (eV 0, fV 1)]
  else if j == 5 then [(eV 0, eV 1), (eV 0, fV 1), (eV 2, eV 3), (eV 2, fV 3)]
  else [(eV 0, eV 1), (eV 0, fV 1), (eV 2, eV 3), (eV 2, fV 3), (eV 4, eV 5), (eV 4, fV 5)]

@[expose] def tr7RepIdx (j : Nat) : List Nat := (tr7RepLines j).map fun p => lineOf p.1 p.2

@[expose] def tr7Comp (A B : Array Nat) : Array Nat := Array.ofFn (n := 32) fun c => applyCols A B[c]!

@[expose] def tr7IdCols : Array Nat := Array.ofFn (n := 32) fun c => 2 ^ c.val

@[expose] def tr7RepCols (j : Nat) : Array Nat :=
  (tr7RepIdx j).foldr (fun k acc => tr7Comp (tvCols k) acc) tr7IdCols

@[expose] def tr7RepImg (j k : Nat) : Nat := (tr7RepIdx j).foldr (fun r acc => tvImg r acc) k

@[expose] def tr7Rep12 (j x : Nat) : Nat := (tr7RepLines j).foldr (fun p acc => sgl p.1 p.2 acc) x

@[expose] def tr7Dim12 (j : Nat) : Nat :=
  if j == 0 then 2 else if j == 1 then 4 else if j == 2 then 6 else if j == 3 then 6
  else if j == 4 then 2 else if j == 5 then 4 else 6

@[expose] def tr7Cols12 (j : Nat) : List Nat :=
  (List.range 12).map fun i => tr7Rep12 j (2 ^ i) ^^^ 2 ^ i

@[expose] def tr7Bs12 (j : Nat) : List Nat := tr7Bs (tr7Cols12 j)

@[expose] def tr7Chk12 (j : Nat) : Bool :=
  (tr7RepLines j).all (fun p => decide (0 < p.1) && decide (p.1 < 4096) && decide (0 < p.2) &&
    decide (p.2 < 4096) && decide (p.1 ≠ p.2) && !qf p.1 && !qf p.2 && !bf p.1 p.2) &&
  decide ((tr7Bs12 j).length = tr7Dim12 j) && (tr7Bs12 j).all (· < 4096) &&
  tr7IndepOK (tr7Bs12 j) &&
  (List.range 4096).all (fun x => tr7Red (tr7Ech (tr7Cols12 j)) (tr7Rep12 j x ^^^ x) == 0) &&
  (List.range 4096).all (fun x => tr7Rep12 j (tr7Rep12 j x) == x) &&
  (if j < 4 then (List.range (2 ^ (tr7Bs12 j).length)).all fun m => !qf (tr7XorSel (tr7Bs12 j) m)
   else (tr7Bs12 j).any qf)

@[expose] def tr7BsInt : List Nat := tr7Bs (tr7Bs12 2 ++ tr7Bs12 3)

@[expose] def tr7ChkInt : Bool :=
  decide (tr7BsInt.length = 7) && tr7BsInt.all (· < 4096) && tr7IndepOK tr7BsInt &&
  (tr7Bs12 2 ++ tr7Bs12 3).all fun v => tr7Red (tr7Ech (tr7Bs12 2 ++ tr7Bs12 3)) v == 0

@[expose] def tr7ChkClass : Bool := (List.range 7).all tr7Chk12 && tr7ChkInt

@[expose] def tr7Cols32 (j : Nat) : List Nat :=
  (List.range 32).map fun c => (tr7RepCols j)[c]! ^^^ 2 ^ c

@[expose] def tr7Bs32 (j : Nat) : List Nat := tr7Bs (tr7Cols32 j)

@[expose] def tr7ChkDim (j : Nat) : Bool :=
  tr7IndepOK ((tr7Bs32 j).take 8) && ((tr7Bs32 j).take 8).all (· < 2 ^ 32) &&
  decide (8 ≤ (tr7Bs32 j).length) &&
  (if j == 2 || j == 6 then
    (List.range 75735).any fun i => fB (wt i) (applyCols (tr7RepCols j) (wt i))
   else true)

@[expose] def tr7ChkDims : Bool := (List.range 7).all tr7ChkDim

@[expose] def tr7GenPairs (j : Nat) : List (Nat × Nat) :=
  if j == 0 then [(3614, 3133), (1024, 513), (2580, 515), (2868, 2835)]
  else if j == 1 then [(3130, 1061), (918, 13), (192, 3), (456, 451), (2802, 2805), (1070, 45)]
  else if j == 3 then [(2990, 29), (2482, 25), (2060, 1794), (368, 362), (2, 2069), (768, 12)]
  else if j == 4 then [(1036, 3242), (3876, 3746), (398, 1341), (954, 533)]
  else if j == 5 then [(1028, 3723), (2620, 3609), (4, 682), (2702, 3609), (1596, 2714)]
  else []

@[expose] def tr7Gens (j : Nat) : List Nat := (tr7GenPairs j).map fun p => lineOf p.1 p.2

@[expose] def tr7Target (j : Nat) : Nat :=
  if j == 0 then 524288 else if j == 1 then 2147483776 else if j == 3 then 49280
  else if j == 4 then 67174400 else if j == 5 then 132 else 0

end CFSG.SmithD6

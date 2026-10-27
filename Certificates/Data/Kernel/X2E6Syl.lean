module

public import Init

public section

namespace CFSG.KC.X2E6Syl

@[expose] def mkV {α : Type} (f : Nat → α) : List α := [f 0, f 1, f 2, f 3, f 4, f 5]

@[expose] def mk6 (f : Nat → Nat → Nat) : List (List Nat) := mkV fun i => mkV (f i)

@[expose] def ent (A : List (List Nat)) (i j : Nat) : Nat := (A.getD i []).getD j 0

@[expose] def mulL (A B : List (List Nat)) : List (List Nat) :=
  mk6 fun i j => (ent A i 0 * ent B 0 j + ent A i 1 * ent B 1 j + ent A i 2 * ent B 2 j +
    ent A i 3 * ent B 3 j + ent A i 4 * ent B 4 j + ent A i 5 * ent B 5 j) % 3

@[expose] def addL (A B : List (List Nat)) : List (List Nat) := mk6 fun i j => (ent A i j + ent B i j) % 3

@[expose] def subL (A B : List (List Nat)) : List (List Nat) :=
  mk6 fun i j => (ent A i j + 2 * ent B i j) % 3

@[expose] def idL : List (List Nat) := mk6 fun i j => if i = j then 1 else 0

@[expose] def zeroL : List (List Nat) := mk6 fun _ _ => 0

@[expose] def czL : List (List Int) :=
  [[2, 0, -1, 0, 0, 0], [0, 2, 0, -1, 0, 0], [-1, 0, 2, -1, 0, 0],
   [0, -1, -1, 2, -1, 0], [0, 0, 0, -1, 2, -1], [0, 0, 0, 0, -1, 2]]

@[expose] def cz (i j : Nat) : Int := (czL.getD i []).getD j 0

@[expose] def reflL (i : Nat) : List (List Nat) :=
  mk6 fun j k => (((if j = k then 1 else 0) - (if k = i then cz j i else 0)) % 3).toNat

@[expose] def wordL (w : List Nat) : List (List Nat) := w.foldr (fun i A => mulL (reflL i) A) idL

@[expose] def pwL (A : List (List Nat)) : Nat → List (List Nat)
  | 0 => idL
  | e + 1 => mulL (pwL A e) A

@[expose] def qEls (gw : List (List Nat)) : List (List (List Nat)) :=
  let g := fun k => wordL (gw.getD k [])
  (List.range 3).flatMap fun a => (List.range 3).flatMap fun b => (List.range 3).flatMap fun c =>
    (List.range 3).map fun d =>
      mulL (mulL (mulL (pwL (g 0) a) (pwL (g 1) b)) (pwL (g 2) c)) (pwL (g 3) d)

@[expose] def qOK (gw : List (List Nat)) : Bool :=
  let Q := qEls gw
  gw.length == 4 && gw.all (fun w => w.all fun i => decide (i < 6)) &&
    gw.all (fun w => pwL (wordL w) 3 == idL) && Q.length == 81 && decide Q.Nodup &&
    Q.all fun A => gw.all fun w => Q.contains (mulL A (wordL w))

@[expose] def tEls (Q : List (List (List Nat))) : List (List (List Nat)) :=
  Q.filter fun A => A != idL && mulL A (mulL A A) == idL

@[expose] def famM (Q : List (List (List Nat))) (m : List Nat) : List (List (List Nat)) :=
  m.map fun i => Q.getD i idL

@[expose] def extL (H : List (List (List Nat))) (x : List (List Nat)) : List (List (List Nat)) :=
  H ++ H.map (fun h => mulL h x) ++ H.map fun h => mulL h (mulL x x)

@[expose] def sameSet (H K : List (List (List Nat))) : Bool := H.all K.contains && K.all H.contains

@[expose] def famOK (gw : List (List Nat)) (mel : List (List Nat)) : Bool :=
  let Q := qEls gw
  let F := mel.map (famM Q)
  let T := tEls Q
  F.head? == some [idL] && F.all (fun H => decide H.Nodup) &&
    F.all fun H => T.all fun x =>
      H.contains x || !(H.all fun h => mulL x h == mulL h x) ||
        F.any fun K => K.length == 3 * H.length && sameSet K (extL H x)

@[expose] def mvL (A : List (List Nat)) (v : List Nat) : List Nat :=
  mkV fun i => (ent A i 0 * v.getD 0 0 + ent A i 1 * v.getD 1 0 + ent A i 2 * v.getD 2 0 +
    ent A i 3 * v.getD 3 0 + ent A i 4 * v.getD 4 0 + ent A i 5 * v.getD 5 0) % 3

@[expose] def sum6 (g : Nat → Int) : Int := g 0 + g 1 + g 2 + g 3 + g 4 + g 5

@[expose] def rootReflL (i : Nat) (a : List Int) : List Int :=
  mkV fun j => if j = i then a.getD i 0 - sum6 (fun k => a.getD k 0 * cz k i) else a.getD j 0

@[expose] def rootW (j : Nat) (w : List Nat) : List Int :=
  w.foldr rootReflL (mkV fun t => if t = j then 1 else 0)

@[expose] def pairI (a : List Int) (f : List Nat) : Int := sum6 fun i => a.getD i 0 * (f.getD i 0 : Int)

@[expose] def cformL (a b : List Int) : Int :=
  sum6 fun i => a.getD i 0 * sum6 fun j => cz i j * b.getD j 0

@[expose] def det3L (x y z : List Int) (c₁ c₂ c₃ : Nat) : Int :=
  x.getD c₁ 0 * (y.getD c₂ 0 * z.getD c₃ 0 - y.getD c₃ 0 * z.getD c₂ 0) -
    x.getD c₂ 0 * (y.getD c₁ 0 * z.getD c₃ 0 - y.getD c₃ 0 * z.getD c₁ 0) +
    x.getD c₃ 0 * (y.getD c₁ 0 * z.getD c₂ 0 - y.getD c₂ 0 * z.getD c₁ 0)

@[expose] def wfV (v : List Nat) : Bool := v.length == 6 && v.all fun a => decide (a < 3)

@[expose] def addV (a b : List Nat) : List Nat := mkV fun i => (a.getD i 0 + b.getD i 0) % 3

@[expose] def negV (a : List Nat) : List Nat := mkV fun i => (2 * a.getD i 0) % 3

@[expose] def fsOK (fs : List (List Nat)) : Bool :=
  fs.length == 9 && decide fs.Nodup && fs.all wfV && fs.contains (mkV fun _ => 0) &&
    fs.all (fun a => fs.all fun b => fs.contains (addV a b)) && fs.all fun a => fs.contains (negV a)

@[expose] def rootOK (fs : List (List Nat)) (r : Nat × List Nat) : Bool :=
  decide (r.1 < 6) && r.2.all (fun i => decide (i < 6)) &&
    fs.all fun f => pairI (rootW r.1 r.2) f % 3 == 0

abbrev Wit : Type := Nat × (List (List Nat) × (List (Nat × List Nat) × List Nat))

@[expose] def witOK1 (w : Wit) : Bool :=
  match w.2.2.1, w.2.2.2 with
  | [r₀, r₂, r₃], [c₁, c₂, c₃] =>
    let a := rootW r₀.1 r₀.2
    let b := rootW r₂.1 r₂.2
    let c := rootW r₃.1 r₃.2
    fsOK w.2.1 && rootOK w.2.1 r₀ && rootOK w.2.1 r₂ && rootOK w.2.1 r₃ &&
      (b == a || cformL a b != 0) && (c == a || cformL a c != 0) &&
      decide (c₁ < 6) && decide (c₂ < 6) && decide (c₃ < 6) && det3L a b c c₁ c₂ c₃ != 0
  | _, _ => false

@[expose] def boundOK (s k : Nat) : Bool :=
  decide (s ≤ 27) && (s != 9 || decide (k ≤ 2)) && (s != 27 || decide (k ≤ 1)) &&
    (s != 3 || decide (k ≤ 4))

@[expose] def colsZero (E : List (List Nat)) (S : List Nat) : Bool :=
  (List.range 6).all fun i => (List.range 6).all fun j => S.contains j || ent E i j == 0

@[expose] def fixOK (gw : List (List Nat)) (mel : List (List Nat)) (fixS : List (List Nat))
    (fixE : List (List (List Nat))) (fixY : List (List (Nat × List (List Nat)))) (wit : List Wit) :
    Bool :=
  let Q := qEls gw
  mel.length == fixS.length && mel.length == fixE.length && mel.length == fixY.length &&
  (List.range mel.length).all fun m =>
    let H := famM Q (mel.getD m [])
    let S := fixS.getD m []
    let E := fixE.getD m []
    let Ys := fixY.getD m []
    Ys.all (fun p => H.contains (Q.getD p.1 idL)) &&
      subL idL E == Ys.foldr (fun p acc => addL (mulL p.2 (subL (Q.getD p.1 idL) idL)) acc) zeroL &&
      S.all (fun j => decide (j < 6)) && colsZero E S && boundOK H.length S.length &&
      (!(H.length == 3 && S.length == 4) ||
        wit.any fun w => w.1 == m && witOK1 w && H.all fun A => w.2.1.all fun f => mvL A f == f)

end CFSG.KC.X2E6Syl

end

module

public import Certificates.Data.H9Four

public section

namespace CFSG.Quasithin.H13.H9Four

@[expose] def u0Codes : List (Nat × Nat × Bool) :=
  [(33827, 33827, false), (33829, 33829, false), (33833, 33833, false), (33889, 33889, false),
    (33953, 33953, false), (35873, 35873, false)]

@[expose] def s0Code : Nat × Nat × Bool := (4680, 4680, true)

@[expose] def j0Codes : List (Nat × Nat × Bool) :=
  [(33829, 33829, false), (33833, 33833, false), (33889, 33889, false), (33953, 33953, false)]

@[expose] def y1Code : Nat × Nat × Bool := (33842, 33811, false)

@[expose] def y2Code : Nat × Nat × Bool := (51233, 19489, false)

@[expose] def lineCodes : List ((Nat × Nat × Bool) × (Nat × Nat × Bool)) :=
  [((33842, 33811, false), (4680, 4680, true)), ((51233, 19489, false), (4680, 4680, true)),
    ((51250, 19475, false), (35873, 35873, false)), ((19506, 51219, false), (35873, 35873, false))]

@[expose] def u0Gens : List Elt := u0Codes.map Elt.ofCodes

@[expose] def s0Elt : Elt := Elt.ofCodes s0Code

@[expose] def s0Gens : List Elt := u0Gens ++ [s0Elt]

@[expose] def s0List : List Elt := elems u0Gens ++ (elems u0Gens).map (fun u => u.mul s0Elt)

@[expose] def j0Gens : List Elt := j0Codes.map Elt.ofCodes

@[expose] def j0List : List Elt := elems j0Gens

@[expose] def y1Elt : Elt := Elt.ofCodes y1Code

@[expose] def y2Elt : Elt := Elt.ofCodes y2Code

@[expose] def x0Gens : List Elt := j0Gens ++ [y1Elt, y2Elt]

@[expose] def pow3 (y : Elt) : List Elt := [Elt.one, y, y.mul y]

@[expose] def x0List : List Elt :=
  j0List.flatMap fun j => (pow3 y1Elt).flatMap fun a => (pow3 y2Elt).map fun b => (j.mul a).mul b

@[expose] def e9Gens : List Elt := [y1Elt, y2Elt]

@[expose] def e9List : List Elt := (pow3 y1Elt).flatMap fun a => (pow3 y2Elt).map fun b => a.mul b

@[expose] def lines : List (Elt × Elt) :=
  lineCodes.map fun p => (Elt.ofCodes p.1, Elt.ofCodes p.2)

@[expose] def lineList (y : Elt) : List Elt :=
  j0List ++ j0List.map (fun j => j.mul y) ++ j0List.map (fun j => j.mul (y.mul y))

@[expose] def lineLists : List (List Elt) := lines.map fun p => lineList p.1

@[expose] def conjE (s x : Elt) : Elt := (s.mul x).mul s.inv

@[expose] def closedRCheck (E Γ : List Elt) : Bool :=
  E.all fun e => Γ.all fun g => E.contains (e.mul g) && E.contains (e.mul g.inv)

@[expose] def s0Check : Bool :=
  s0Gens.all Elt.valid && closedRCheck s0List s0Gens && decide s0List.Nodup &&
    s0List.length == 128

@[expose] def j0Check : Bool :=
  j0Gens.all (fun g => g.valid && g.mul g == Elt.one && g != Elt.one && !g.b) &&
    j0Gens.all (fun g => j0Gens.all (commutes g)) && decide j0List.Nodup &&
    j0Gens.all (s0List.contains ·)

@[expose] def x0Check : Bool :=
  x0Gens.all (fun x => x.valid && !x.b) && x0List.contains Elt.one &&
    closedRCheck x0List x0Gens && decide x0List.Nodup && x0List.length == 144 &&
    x0Gens.all (fun x => j0Gens.all fun j => j0List.contains (conjE x j)) &&
    s0Gens.all (fun s => x0Gens.all fun x => x0List.contains (conjE s x)) &&
    x0List.all (fun x => j0List.contains (x.mul (x.mul x))) &&
    x0Gens.all (fun x => x0List.all fun y => j0List.contains ((conjE x y).mul y.inv))

@[expose] def oddGenCheck : Bool :=
  x0List.all fun x => x0List.any fun a =>
    a.mul (a.mul a) == Elt.one && (a.inv.mul x).mul ((a.inv.mul x).mul (a.inv.mul x)) == Elt.one

@[expose] def lineCheck : Bool :=
  lines.all (fun p => x0List.contains p.1 && s0List.contains p.2 &&
      p.1.mul (p.1.mul p.1) == Elt.one && decide (lineList p.1).Nodup &&
      !(lineList p.1).contains (conjE p.2 p.1)) &&
    x0List.all fun x => j0List.contains x || lineLists.any fun l => l.contains x

@[expose] def fixCheck : Bool := (fixPts x0Gens).length == 1

@[expose] def kerCheck : Bool :=
  s0List.all fun t => j0List.contains t ||
    x0Gens.any fun x => !j0List.contains ((conjE t x).mul x.inv)

@[expose] def e9Check : Bool :=
  e9List.contains Elt.one && closedRCheck e9List e9Gens && decide e9List.Nodup &&
    e9List.length == 9 && (fixPts e9Gens).length == 1 &&
    (fixPts j0Gens).any fun w => y1Elt.act w != w

@[expose] def ffRepCheck : Bool :=
  reps.all fun gs => gs.isEmpty || decide ((elems gs).length * (fixPts gs).length < 256) ||
    gs.length == 4

@[expose] def u0Check : Bool :=
  s0List.all fun e => e.b || e.mul e != Elt.one || e == Elt.one || j0List.contains e ||
    decide ((s0List.filter fun g => !g.b && g.mul g == Elt.one && commutes g e).length ≤ 12)

@[expose] def b0Elt : Elt := Elt.ofCodes (33827, 33827, false)

@[expose] def d8Elt : Elt :=
  (conjE (s0Elt.mul b0Elt) y1Elt).mul (conjE (b0Elt.mul s0Elt) y1Elt).inv

@[expose] def d8Check : Bool := !j0List.contains d8Elt

end CFSG.Quasithin.H13.H9Four

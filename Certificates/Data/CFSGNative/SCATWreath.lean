module

public import Certificates.Data.CFSGNative.SCATWreathSearch

public section

namespace CFSG.SCATWreath

@[expose] def ext2 (X : Array Bool) (δ : Bool) (c : Nat) : Bool := X[c / 2]! != (δ && c % 2 == 1)

@[expose] def pReps (D : GD) (invs : List Nat) : List Nat :=
  D.reps.toList.filter fun r =>
    r != 0 && D.mul r r == 0 && D.csz[D.lab[r]!]! == D.n / 256 && cntC D.mul invs r == 87

@[expose] def charsOf (D : GD) (par gi order : Array Nat) : List (Array Bool) :=
  (List.range 16).filterMap fun m =>
    let v := #[m.testBit 0, m.testBit 1, m.testBit 2, m.testBit 3]
    let X := charOf D.n par gi order v
    if charOK D.n D.mul D.gens v X then some X else none

@[expose] def level1OK (W : GD) (t0 : Nat) (chars : List (Array Bool)) : Bool :=
  let invs := invols W.n W.mul
  W.csz[W.lab[t0]!]! == W.n / 128 &&
    chars.any fun X => X[t0]! &&
      (W.reps.toList.filter fun r => r != 0 && W.mul r r == 0).all fun r =>
        if X[r]! then W.lab[r]! == W.lab[t0]! else
          W.csz[W.lab[r]!]! ≤ W.n / 256 &&
            (W.csz[W.lab[r]!]! != W.n / 256 || cntC W.mul invs r != 87)

@[expose] def t3GD (T : GD) (G3 F3 : Array Nat) (g : Nat) : GD :=
  mkGD (2 * T.n) (extMul T.mul F3 g) #[2 * G3[0]!, 2 * G3[1]!, 2 * G3[2]!, 2 * G3[3]!, 1] false

@[expose] def level3Facts (T : GD) (G3 F3 : Array Nat) (t g : Nat)
    (chars2 : List (Array Bool × Bool)) : Bool :=
  let U := t3GD T G3 F3 g
  if cntC U.mul (List.range U.n) (2 * t) != 256 then true else
  U.ok false && (pReps U U.dom).all (fun r => U.lab[r]! == U.lab[2 * t]!) &&
    chars2.any fun χ =>
      (List.range 4).all (fun i => ext2 χ.1 χ.2 F3[G3[i]!]! == ext2 χ.1 χ.2 G3[i]!) &&
        !ext2 χ.1 χ.2 g

@[expose] def tuple3OK (T : GD) (G3 par gi order : Array Nat) (t : Nat)
    (chars2 : List (Array Bool × Bool)) (u : Nat × Nat × Nat) : Bool :=
  let imgs := #[t, u.1, u.2.1, u.2.2]
  let F3 := buildF T.n T.mul par gi order imgs
  recOK T.n T.mul par gi imgs F3 && (!edgeOK T.n T.mul G3 imgs F3 ||
    ((List.range T.n).filter (gOK T G3 F3)).all fun g => level3Facts T G3 F3 t g chars2)

@[expose] def chooseG3 (T : GD) (x0 : Nat) :
    Option (Array Nat × (Array Nat × Array Nat × Array Nat × Array Nat)) :=
  let k := T.gens.size
  let triples := (List.range k).flatMap fun i => (List.range k).flatMap fun j =>
    (List.range k).filterMap fun l =>
      if i < j && j < l then some (T.gens[i]!, T.gens[j]!, T.gens[l]!) else none
  triples.findSome? fun abc =>
    let G := #[x0, abc.1, abc.2.1, abc.2.2]
    let tr := bfsTree T.n T.mul G
    if tr.2.2.2.size == T.n then some (G, tr) else none

@[expose] def level3OK (T : GD) (t x0 : Nat) (chars2 : List (Array Bool × Bool)) : Bool :=
  match chooseG3 T x0 with
  | none => false
  | some (G3, tr) =>
    treeOK T.n T.mul G3 tr.1 tr.2.1 tr.2.2.1 &&
      (search T tr.1 tr.2.1 G3 t (centList T t) (centList T x0) (zList T G3)
        (spotList T.n)).all (tuple3OK T G3 tr.1 tr.2.1 tr.2.2.2 t chars2)

@[expose] def t2GD (W : GD) (F : Array Nat) (g : Nat) : GD :=
  mkGD (2 * W.n) (extMul W.mul F g)
    #[2 * W.gens[0]!, 2 * W.gens[1]!, 2 * W.gens[2]!, 2 * W.gens[3]!, 1] true

@[expose] def x0Of (T : GD) (Pr : List Nat) (t : Nat) : Nat :=
  (Pr.find? fun r => T.lab[r]! != T.lab[t]!).getD t

@[expose] def chars2Of (W : GD) (charsW : List (Array Bool)) (t0 : Nat) (F : Array Nat)
    (g : Nat) : List (Array Bool × Bool) :=
  (charsW.filter fun X => X[t0]! &&
      (List.range 4).all (fun i => X[F[W.gens[i]!]!]! == X[W.gens[i]!]!) && !X[g]!).flatMap
    fun X => [(X, false), (X, true)]

@[expose] def level2OK (W : GD) (t0 : Nat) (charsW : List (Array Bool)) (F : Array Nat)
    (g : Nat) : Bool :=
  let T := t2GD W F g
  if !(cntC T.mul (List.range T.n) (2 * t0) == 256 &&
      cntC T.mul (invols T.n T.mul) (2 * t0) == 87) then true
  else
  let Pr := pReps T (invols T.n T.mul)
  let x0 := x0Of T Pr (2 * t0)
  let chars2 := chars2Of W charsW t0 F g
  T.ok true && Pr.all (fun r => T.lab[r]! == T.lab[2 * t0]! || T.lab[r]! == T.lab[x0]!) &&
    chars2.any (fun χ => Pr.all fun r => ext2 χ.1 χ.2 r) &&
    (T.lab[x0]! == T.lab[2 * t0]! || level3OK T (2 * t0) x0 chars2)

@[expose] def tuple2OK (W : GD) (par gi order : Array Nat) (H : List Nat) (t0 : Nat)
    (charsW : List (Array Bool)) (u : Nat × Nat × Nat) : Bool :=
  let imgs := #[t0, u.1, u.2.1, u.2.2]
  let F := buildF W.n W.mul par gi order imgs
  recOK W.n W.mul par gi imgs F && (!edgeOK W.n W.mul W.gens imgs F ||
    (H.filter (gOK W W.gens F)).all fun g => level2OK W t0 charsW F g)

@[expose] def wGD (L : List Nat) : GD :=
  mkGD 8192 (wMul (smulTab L) (actTab L)) #[64, 256, 320, 32] true

@[expose] def towerCheck (L : List Nat) (_ : Unit := ()) : Bool :=
  let W := wGD L
  let tr := bfsTree W.n W.mul W.gens
  let chars := charsOf W tr.1 tr.2.1 tr.2.2.2
  let H := centList W 64
  treeOK W.n W.mul W.gens tr.1 tr.2.1 tr.2.2.1 && W.ok true && level1OK W 64 chars &&
    (search W tr.1 tr.2.1 W.gens 64 H H (zList W W.gens) (spotList W.n)).all
      (tuple2OK W tr.1 tr.2.1 tr.2.2.2 H 64 chars)

end CFSG.SCATWreath

module

public import Init

public section

namespace CFSG.KC.P0Orb

@[expose] noncomputable def pAct (w m n p x : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat) (fun _ _ => 0)
    (fun _ ih p x => bif Nat.beq x 0 then 0 else
      Nat.xor (bif Nat.beq (Nat.land x 1) 1 then Nat.land p m else 0)
        (ih (Nat.shiftRight p w) (Nat.shiftRight x 1))) n p x

@[expose] def fld (r o m : Nat) : Nat := Nat.land (Nat.shiftRight r o) m

@[expose] def m144 : Nat := 22300745198530623141535718272648361505980415

@[expose] def m256 : Nat :=
  115792089237316195423570985008687907853269984665640564039457584007913129639935

@[expose] def m96 : Nat := 79228162514264337593543950335

@[expose] noncomputable def bet (BC x y : Nat) : Nat := pAct 9 511 16 (pAct 144 m144 16 BC y) x

@[expose] noncomputable def qf (BU x : Nat) : Nat := pAct 9 511 16 (pAct 144 m144 16 BU x) x

@[expose] noncomputable def aAct (AT lam x : Nat) : Nat := pAct 16 65535 16 (fld AT (256 * lam) m256) x

@[expose] def slot (RT r : Nat) : Nat := fld RT (96 * r) m96

@[expose] def sbasis (s : Nat) : List Nat :=
  (List.range (Nat.shiftRight s 80)).map fun k => fld s (16 * k) 65535

@[expose] noncomputable def lAct (cs : List Nat) (x : Nat) : Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun _ => 0)
    (fun c _ ih x => Nat.xor (bif Nat.beq (Nat.land x 1) 1 then c else 0) (ih (Nat.shiftRight x 1)))
    cs x

@[expose] def redZ (bs : List Nat) (y : Nat) : Bool :=
  Nat.beq (bs.foldl (fun y b => Nat.min y (Nat.xor y b)) y) 0

@[expose] noncomputable def fv (BC : Nat) (bs : List Nat) (x : Nat) : Nat :=
  List.rec (motive := fun _ => Nat) 0 (fun b _ ih => Nat.lor (bet BC b x) (Nat.shiftLeft ih 9)) bs

@[expose] noncomputable def tsOK (BC BU : Nat) : List Nat → Bool
  | [] => true
  | b :: bs => Nat.beq (qf BU b) 0 && bs.all (fun b' => Nat.beq (bet BC b b') 0) && tsOK BC BU bs

@[expose] def triOK : List Nat → List Nat → Bool
  | [], [] => true
  | f :: fs, p :: ps => f.testBit p && fs.all (fun g => !g.testBit p) && triOK fs ps
  | _, _ => false

@[expose] noncomputable def qOK (P Q : List Nat) : Bool :=
  Nat.beq P.length 16 && Nat.beq Q.length 16 &&
    (List.range 16).all fun j => Nat.beq (lAct P (Q.getD j 0)) (2 ^ j)

@[expose] noncomputable def recOK (AT RT d : Nat) (bs : List Nat) (σ : Nat) (r : Nat × Nat) :
    Bool :=
  Nat.blt r.1 1024 &&
    (let s := slot RT r.2
     Nat.beq (Nat.shiftRight s 80) (d + 1) &&
      (let B := sbasis s
       redZ B (aAct AT r.1 σ) && bs.all fun b => redZ B (aAct AT r.1 b)))

@[expose] noncomputable def leaf (AT RT d : Nat) (bs : List Nat) (σ q : Nat)
    (recs : List (Nat × Nat)) : Option (List (Nat × Nat)) :=
  bif !Nat.beq σ 0 && Nat.beq q 0 then
    List.rec (motive := fun _ => Option (List (Nat × Nat))) none
      (fun r rest _ => bif recOK AT RT d bs σ r then some rest else none) recs
  else some recs

@[expose] noncomputable def gwalk (AT RT d : Nat) (bs : List Nat) :
    List (Nat × Nat × Nat × Nat) → Nat → Nat → Nat → List (Nat × Nat) →
      Option (List (Nat × Nat)) :=
  List.rec (motive := fun _ => Nat → Nat → Nat → List (Nat × Nat) → Option (List (Nat × Nat)))
    (fun σ q _ recs => leaf AT RT d bs σ q recs)
    (fun c _ ih σ q v recs =>
      Option.rec (motive := fun _ => Option (List (Nat × Nat))) none
        (fun recs' => ih (Nat.xor σ c.1) (Nat.xor (Nat.xor q c.2.1) (fld v c.2.2.2 511))
          (Nat.xor v c.2.2.1) recs')
        (ih σ q v recs))

@[expose] noncomputable def gRow (BC : Nat) (c : List Nat) (x : Nat) : Nat :=
  List.rec (motive := fun _ => Nat) 0 (fun y _ ih => Nat.lor (bet BC x y) (Nat.shiftLeft ih 9)) c

@[expose] noncomputable def cEntries (BC BU : Nat) (c : List Nat) : List (Nat × Nat × Nat × Nat) :=
  (List.range c.length).map fun j =>
    let x := c.getD j 0
    (x, qf BU x, gRow BC c x, 9 * j)

abbrev Row := List Nat × List Nat × List Nat × List Nat × List (Nat × Nat)

@[expose] noncomputable def repOK (AT RT BC BU r : Nat) (row : Row) : Bool :=
  let s := slot RT r
  let d := Nat.shiftRight s 80
  let bs := sbasis s
  let c := row.1
  let w := row.2.1
  tsOK BC BU bs && Nat.beq (d + c.length + w.length) 16 && qOK (bs ++ c ++ w) row.2.2.1 &&
    c.all (fun x => Nat.beq (fv BC bs x) 0) && triOK (w.map (fv BC bs)) row.2.2.2.1 &&
    Option.rec (motive := fun _ => Bool) false (fun l => l.isEmpty)
      (gwalk AT RT d bs (cEntries BC BU c) 0 0 0 row.2.2.2.2)

@[expose] noncomputable def repsOK (AT RT BC BU : Nat) : Nat → List Row → Bool
  | _, [] => true
  | r, row :: rows => repOK AT RT BC BU r row && repsOK AT RT BC BU (r + 1) rows

@[expose] noncomputable def grpOK (AT RT BC BU lo g : Nat) (rows : List Row) (i : Nat) : Bool :=
  repsOK AT RT BC BU (lo + g * i) ((rows.drop (g * i)).take g)

@[expose] noncomputable def rowOf (p : Nat) (xs : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat) 0
    (fun x _ ih => Nat.lor (pAct 16 65535 16 p x) (Nat.shiftLeft ih 16)) xs

@[expose] noncomputable def atOK (AT : Nat) (aCols : List (List Nat)) (t : Nat) : Bool :=
  (List.range (2 ^ t)).all fun κ =>
    Nat.beq (fld AT (256 * (κ + 2 ^ t)) m256) (rowOf (fld AT (256 * κ) m256) (aCols.getD t []))

@[expose] noncomputable def at0OK (AT : Nat) (aCols : List (List Nat)) : Bool :=
  Nat.beq (fld AT 0 m256) ((List.range 16).foldl (fun a j => a ||| 2 ^ (17 * j)) 0) &&
    Nat.beq aCols.length 10 && aCols.all (fun cs => Nat.beq cs.length 16) &&
    Nat.blt AT (2 ^ 262144)

@[expose] noncomputable def bcOK (BC BU : Nat) (beta : List (List Nat)) : Bool :=
  Nat.beq beta.length 16 && beta.all (fun r => Nat.beq r.length 16) &&
    (List.range 16).all (fun i => (List.range 16).all fun j =>
      Nat.beq ((beta.getD i []).getD j 0) ((beta.getD j []).getD i 0) &&
      Nat.blt ((beta.getD i []).getD j 0) 512 &&
      Nat.beq (fld BC (144 * j + 9 * i) 511) ((beta.getD i []).getD j 0) &&
      Nat.beq (fld BU (144 * j + 9 * i) 511) (bif Nat.blt i j then (beta.getD j []).getD i 0 else 0)) &&
    (List.range 16).all (fun i => Nat.beq ((beta.getD i []).getD i 0) 0) &&
    Nat.blt BC (2 ^ 2304) && Nat.blt BU (2 ^ 2304)

@[expose] def rtOK (RT N : Nat) : Bool := Nat.beq (slot RT 0) 0 && Nat.blt RT (2 ^ (96 * N))

end CFSG.KC.P0Orb

end

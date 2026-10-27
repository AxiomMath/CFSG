module

public import CFSG.Quasithin.Vol2.Ch12Sec6S8Data

public section

namespace CFSG.Quasithin.H13.S8F

open S8E

@[expose] def Vec (u : List Nat) : Prop :=
  (∀ i ∈ id8, ap u i < 2) ∧
    (ap u 0 + ap u 1 + ap u 2 + ap u 3 + ap u 4 + ap u 5 + ap u 6 + ap u 7) % 2 = 0

instance (u : List Nat) : Decidable (Vec u) := by
  unfold Vec
  infer_instance

@[expose] def FixL (f u : List Nat) : Prop :=
  (∀ i ∈ id8, ap u (ap f i) = ap u i) ∨ ∀ i ∈ id8, ap u (ap f i) ≠ ap u i

instance (f u : List Nat) : Decidable (FixL f u) := by
  unfold FixL
  infer_instance

@[expose] def SepW (bs g : List (List Nat)) (u : List Nat) : Prop :=
  Vec u ∧ (∀ b ∈ bs, FixL b u) ∧ ∃ a ∈ g, ¬ FixL a u

instance (bs g : List (List Nat)) (u : List Nat) : Decidable (SepW bs g u) := by
  unfold SepW
  infer_instance

@[expose] def Ok1 (g : List (List Nat)) (w : List Nat × List Nat) : Prop :=
  w.1 ∈ g ∧ w.1 ≠ id8 ∧ SepW [w.1] g w.2

instance (g : List (List Nat)) (w : List Nat × List Nat) : Decidable (Ok1 g w) := by
  unfold Ok1
  infer_instance

@[expose] def Ok2 (g : List (List Nat)) (w : List Nat × List Nat × List Nat) : Prop :=
  w.1 ∈ g ∧ w.2.1 ∈ g ∧ w.1 ≠ id8 ∧ w.2.1 ≠ id8 ∧ w.1 ≠ w.2.1 ∧ SepW [w.1, w.2.1] g w.2.2

instance (g : List (List Nat)) (w : List Nat × List Nat × List Nat) : Decidable (Ok2 g w) := by
  unfold Ok2
  infer_instance

@[expose] def Ok3 (g : List (List Nat)) (w : List Nat × List Nat × List Nat × List Nat) : Prop :=
  w.1 ∈ g ∧ w.2.1 ∈ g ∧ w.2.2.1 ∈ g ∧ w.1 ≠ id8 ∧ w.2.1 ≠ id8 ∧ w.1 ≠ w.2.1 ∧
    w.2.2.1 ∉ [id8, w.1, w.2.1, S8E.cmp w.1 w.2.1] ∧ SepW [w.1, w.2.1, w.2.2.1] g w.2.2.2

instance (g : List (List Nat)) (w : List Nat × List Nat × List Nat × List Nat) :
    Decidable (Ok3 g w) := by
  unfold Ok3
  infer_instance

@[expose] def OkE3 (g : List (List Nat))
    (w : (List Nat × List Nat) × (List Nat × List Nat) × (List Nat × List Nat)) : Prop :=
  w.1.1 ≠ w.2.1.1 ∧ w.1.1 ≠ w.2.2.1 ∧ w.2.1.1 ≠ w.2.2.1 ∧ Ok1 g w.1 ∧ Ok1 g w.2.1 ∧ Ok1 g w.2.2

instance (g : List (List Nat))
    (w : (List Nat × List Nat) × (List Nat × List Nat) × (List Nat × List Nat)) :
    Decidable (OkE3 g w) := by
  unfold OkE3
  infer_instance

@[expose] def OkE4 (g : List (List Nat))
    (w : List Nat × (List Nat × List Nat) × (List Nat × List Nat) × (List Nat × List Nat)) :
    Prop :=
  w.1 ∈ g ∧ w.1 ≠ id8 ∧ w.2.1.1 ∈ g ∧ w.2.2.1.1 ∈ g ∧ w.2.2.2.1 ∈ g ∧
    w.2.1.1 ∉ [id8, w.1] ∧ w.2.2.1.1 ∉ [id8, w.1, w.2.1.1, S8E.cmp w.1 w.2.1.1] ∧
    w.2.2.2.1 ∉ [id8, w.1, w.2.1.1, S8E.cmp w.1 w.2.1.1] ∧
    w.2.2.2.1 ∉ [id8, w.1, w.2.2.1.1, S8E.cmp w.1 w.2.2.1.1] ∧
    SepW [w.1, w.2.1.1] g w.2.1.2 ∧ SepW [w.1, w.2.2.1.1] g w.2.2.1.2 ∧
    SepW [w.1, w.2.2.2.1] g w.2.2.2.2

instance (g : List (List Nat))
    (w : List Nat × (List Nat × List Nat) × (List Nat × List Nat) × (List Nat × List Nat)) :
    Decidable (OkE4 g w) := by
  unfold OkE4
  infer_instance

@[expose] def VECS : List (List Nat) :=
  ((List.range 256).map fun n => (List.range 8).map fun i => n / 2 ^ i % 2).filter
    fun u => u.sum % 2 == 0

@[expose] def fixMask (f : List Nat) : Nat :=
  (List.range 128).foldl
    (fun m k => if decide (FixL f (VECS.getD k [])) then m ||| 2 ^ k else m) 0

@[expose] def FM : List Nat := INV.map fixMask

@[expose] def maskOf (f : List Nat) : Nat := FM.getD (INV.findIdx (· == f)) (2 ^ 128 - 1)

@[expose] def gMask (g : List (List Nat)) : Nat := g.foldl (fun m a => m &&& maskOf a) (2 ^ 128 - 1)

@[expose] def lowVec (m : Nat) : List Nat :=
  VECS.getD (((List.range 128).find? fun k => m.testBit k).getD 0) []

@[expose] def sepv (m F : Nat) : Option (List Nat) :=
  if m == F then none else some (lowVec (m ^^^ F))

@[expose] def s1 (g : List (List Nat)) : Option (List Nat × List Nat) :=
  let F := gMask g
  g.findSome? fun b => if b == id8 then none else (sepv (maskOf b) F).map fun u => (b, u)

@[expose] def s2 (g : List (List Nat)) : Option (List Nat × List Nat × List Nat) :=
  let F := gMask g
  g.findSome? fun b => if b == id8 then none else
    g.findSome? fun c => if c == id8 || c == b then none else
      (sepv (maskOf b &&& maskOf c) F).map fun u => (b, c, u)

@[expose] def s3 (g : List (List Nat)) : Option (List Nat × List Nat × List Nat × List Nat) :=
  let F := gMask g
  g.findSome? fun b => if b == id8 then none else
    g.findSome? fun c => if c == id8 || c == b then none else
      g.findSome? fun d => if [id8, b, c, S8E.cmp b c].contains d then none else
        (sepv (maskOf b &&& maskOf c &&& maskOf d) F).map fun u => (b, c, d, u)

@[expose] def sE3 (g : List (List Nat)) :
    Option ((List Nat × List Nat) × (List Nat × List Nat) × (List Nat × List Nat)) :=
  let F := gMask g
  match g.filterMap fun e => if e == id8 then none else (sepv (maskOf e) F).map fun u => (e, u)
  with
  | p₁ :: p₂ :: p₃ :: _ => some (p₁, p₂, p₃)
  | _ => none

@[expose] def pick (d : List Nat) (md F : Nat) :
    List (List Nat) → List (List Nat × List Nat) → List (List Nat × List Nat)
  | [], acc => acc
  | e :: es, acc =>
    if e == id8 || e == d || acc.any (fun p => e == p.1 || e == S8E.cmp d p.1) then
      pick d md F es acc
    else match sepv (md &&& maskOf e) F with
      | some u => pick d md F es (acc ++ [(e, u)])
      | none => pick d md F es acc

@[expose] def sE4 (g : List (List Nat)) :
    Option (List Nat × (List Nat × List Nat) × (List Nat × List Nat) × (List Nat × List Nat)) :=
  let F := gMask g
  g.findSome? fun d => if d == id8 then none else
    match pick d (maskOf d) F g [] with
    | p₁ :: p₂ :: p₃ :: _ => some (d, p₁, p₂, p₃)
    | _ => none

@[expose] def grp2 (x y : List Nat) : List (List Nat) := [id8, x, y, cmp x y]

@[expose] def R2 (g : List (List Nat)) : Prop := ∃ w ∈ (s1 g).toList, Ok1 g w

instance (g : List (List Nat)) : Decidable (R2 g) := by
  unfold R2
  infer_instance

@[expose] def R3 (g : List (List Nat)) : Prop :=
  (∃ w ∈ (s1 g).toList, Ok1 g w) ∧
    ((∃ w ∈ (s2 g).toList, Ok2 g w) ∨ ∃ w ∈ (sE3 g).toList, OkE3 g w)

instance (g : List (List Nat)) : Decidable (R3 g) := by
  unfold R3
  infer_instance

@[expose] def R4 (g : List (List Nat)) : Prop :=
  (∃ w ∈ (s2 g).toList, Ok2 g w) ∧
    ((∃ w ∈ (s3 g).toList, Ok3 g w) ∨ ∃ w ∈ (sE4 g).toList, OkE4 g w)

instance (g : List (List Nat)) : Decidable (R4 g) := by
  unfold R4
  infer_instance

@[expose] def Max4 (g : List (List Nat)) (x y z w : List Nat) : Prop :=
  ∀ n ∈ List.range 43, CommL (iv n) x → CommL (iv n) y → CommL (iv n) z → CommL (iv n) w →
    iv n ∈ g

instance (g : List (List Nat)) (x y z w : List Nat) : Decidable (Max4 g x y z w) := by
  unfold Max4
  infer_instance

@[expose] def C2 : Prop :=
  ∀ i ∈ List.range 43, ∀ j ∈ List.range 43, i < j → CommL (iv i) (iv j) →
    R2 (grp2 (iv i) (iv j))

@[expose] def C3 : Prop :=
  ∀ i ∈ List.range 43, ∀ j ∈ List.range 43, i < j → CommL (iv i) (iv j) →
    ∀ k ∈ List.range 43, j < k → CommL (iv i) (iv k) → CommL (iv j) (iv k) →
    iv k ∉ [id8, iv i, iv j, cmp (iv i) (iv j)] → R3 (grp3 (iv i) (iv j) (iv k))

@[expose] def T4 (i j k : Nat) : Prop :=
  ∀ l ∈ List.range 43, k < l → CommL (iv i) (iv l) → CommL (iv j) (iv l) →
    CommL (iv k) (iv l) → iv l ∉ grp3 (iv i) (iv j) (iv k) →
    R4 (grp4 (grp3 (iv i) (iv j) (iv k)) (iv l)) ∧
      Max4 (grp4 (grp3 (iv i) (iv j) (iv k)) (iv l)) (iv i) (iv j) (iv k) (iv l)

instance (i j k : Nat) : Decidable (T4 i j k) := by
  unfold T4
  infer_instance

@[expose] def C4 : Prop :=
  ∀ i ∈ List.range 43, ∀ j ∈ List.range 43, i < j → CommL (iv i) (iv j) →
    ∀ k ∈ List.range 43, j < k → CommL (iv i) (iv k) → CommL (iv j) (iv k) →
    iv k ∉ [id8, iv i, iv j, cmp (iv i) (iv j)] → T4 i j k

instance : Decidable C2 := by
  unfold C2
  infer_instance

instance : Decidable C3 := by
  unfold C3
  infer_instance

instance : Decidable C4 := by
  unfold C4
  infer_instance

@[expose] def s8Check28 : Bool := decide K0 && decide C2 && decide C3 && decide C4

end CFSG.Quasithin.H13.S8F


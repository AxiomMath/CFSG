module

public import CFSG.LocalAnalysis.StandardType.GGKacK0

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

private local instance (priority := high) k0tabDecidableEqLargeEvenLabel : DecidableEq LargeEvenLabel :=
  fun a b =>
    match a, b with
    | ⟨ta, ra, na⟩, ⟨tb, rb, nb⟩ =>
      if h1 : ta = tb then
        if h2 : ra = rb then
          if h3 : na = nb then isTrue (by cases h1; cases h2; cases h3; rfl)
          else isFalse (by intro h; injection h with _ _ h3'; exact h3 h3')
        else isFalse (by intro h; injection h with _ h2' _; exact h2 h2')
      else isFalse (by intro h; injection h with h1' _ _; exact h1 h1')

private local instance (priority := high) k0tabDecidableEqGGKacOrbit : DecidableEq GGKacOrbit :=
  fun a b =>
    match a, b with
    | ⟨la, qa⟩, ⟨lb, qb⟩ =>
      if h1 : la = lb then
        if h2 : qa = qb then isTrue (by cases h1; cases h2; rfl)
        else isFalse (by intro h; injection h with _ h2'; exact h2 h2')
      else isFalse (by intro h; injection h with h1' _; exact h1 h1')

private local instance (priority := high) k0tabDecidableEqGGKacDatum : DecidableEq GGKacDatum :=
  fun a b =>
    match a, b with
    | ⟨oa, za, sa⟩, ⟨ob, zb, sb⟩ =>
      if h1 : oa = ob then
        if h2 : za = zb then
          if h3 : sa = sb then isTrue (by cases h1; cases h2; cases h3; rfl)
          else isFalse (by intro h; injection h with _ _ h3'; exact h3 h3')
        else isFalse (by intro h; injection h with _ h2' _; exact h2 h2')
      else isFalse (by intro h; injection h with h1' _ _; exact h1 h1')

inductive GGKacType | E6 | E7 | E8 | F4
  deriving DecidableEq

@[expose] def k0pId (n : ℕ) : List ℕ := List.range n

@[expose] def k0pMul (a b : List ℕ) : List ℕ := b.map (fun i => a.getD i 0)

@[expose] def k0pInv (a : List ℕ) : List ℕ :=
  let rec go (i : ℕ) (l : List ℕ) (acc : List ℕ) : List ℕ :=
    match l with
    | [] => acc
    | x :: xs => go (i + 1) xs (acc.set x i)
  go 0 a (List.replicate a.length 0)

@[expose] def k0pAct (a s : List ℕ) : List ℕ :=
  let rec go (i : ℕ) (l : List ℕ) (acc : List ℕ) : List ℕ :=
    match l with
    | [] => acc
    | x :: xs => go (i + 1) xs (acc.set x (s.getD i 0))
  go 0 a (List.replicate s.length 0)

@[expose] def k0pPow (a : List ℕ) (k : ℕ) : List ℕ :=
  let rec go (f : ℕ) (acc : List ℕ) : List ℕ :=
    match f with
    | 0 => acc
    | f + 1 => go f (k0pMul a acc)
  go k (k0pId a.length)

structure K0Diag where
  marks : List ℕ
  edges : List (ℕ × ℕ × ℕ)
  long : List ℕ
  omega : List (List ℕ)
  tau : List ℕ
  tau0 : List ℕ

@[expose] def K0Diag.adj (D : K0Diag) (i j : ℕ) : ℕ :=
  match D.edges.find? (fun e => (e.1 = i ∧ e.2.1 = j) ∨ (e.1 = j ∧ e.2.1 = i)) with
  | some e => e.2.2
  | none => 0

@[expose] def k0E6Diag : K0Diag where
  marks := [1, 1, 2, 2, 3, 2, 1]
  edges := [(1, 3, 1), (3, 4, 1), (4, 5, 1), (5, 6, 1), (2, 4, 1), (0, 2, 1)]
  long := []
  omega := [k0pId 7, [1, 6, 3, 5, 4, 2, 0], k0pMul [1, 6, 3, 5, 4, 2, 0] [1, 6, 3, 5, 4, 2, 0]]
  tau := [0, 6, 2, 5, 4, 3, 1]
  tau0 := [0, 6, 2, 5, 4, 3, 1]

@[expose] def k0E7Diag : K0Diag where
  marks := [1, 2, 2, 3, 4, 3, 2, 1]
  edges := [(0, 1, 1), (1, 3, 1), (3, 4, 1), (4, 5, 1), (5, 6, 1), (6, 7, 1), (2, 4, 1)]
  long := []
  omega := [k0pId 8, [7, 6, 2, 5, 4, 3, 1, 0]]
  tau := k0pId 8
  tau0 := k0pId 8

@[expose] def k0E8Diag : K0Diag where
  marks := [1, 2, 3, 4, 6, 5, 4, 3, 2]
  edges := [(1, 3, 1), (3, 4, 1), (4, 5, 1), (5, 6, 1), (6, 7, 1), (7, 8, 1), (2, 4, 1), (8, 0, 1)]
  long := []
  omega := [k0pId 9]
  tau := k0pId 9
  tau0 := k0pId 9

@[expose] def k0F4Diag : K0Diag where
  marks := [1, 2, 3, 4, 2]
  edges := [(0, 1, 1), (1, 2, 1), (2, 3, 2), (3, 4, 1)]
  long := [0, 1, 2]
  omega := [k0pId 5]
  tau := k0pId 5
  tau0 := k0pId 5

@[expose] def k0DiagOf : GGKacType → K0Diag
  | .E6 => k0E6Diag
  | .E7 => k0E7Diag
  | .E8 => k0E8Diag
  | .F4 => k0F4Diag

@[expose] def k0InsertBy {α : Type} (le : α → α → Bool) (a : α) : List α → List α
  | [] => [a]
  | b :: bs => if le a b then a :: b :: bs else b :: k0InsertBy le a bs

@[expose] def k0SortBy {α : Type} (le : α → α → Bool) : List α → List α
  | [] => []
  | a :: as => k0InsertBy le a (k0SortBy le as)

@[expose] def k0SortNat (l : List ℕ) : List ℕ := k0SortBy (fun a b => decide (a ≤ b)) l

@[expose] def k0LexLtNat : List ℕ → List ℕ → Bool
  | [], [] => false
  | [], _ :: _ => true
  | _ :: _, [] => false
  | x :: xs, y :: ys =>
      if x < y then true else if y < x then false else k0LexLtNat xs ys

@[expose] def k0LexLtKey : List (List ℕ) → List (List ℕ) → Bool
  | [], [] => false
  | [], _ :: _ => true
  | _ :: _, [] => false
  | x :: xs, y :: ys =>
      if k0LexLtNat x y then true
      else if k0LexLtNat y x then false
      else k0LexLtKey xs ys

@[expose] def k0VecsAux : List ℕ → ℕ → List (List ℕ)
  | [], p => if p = 0 then [[]] else []
  | m :: ms, p =>
      (List.range (p / m + 1)).foldr
        (fun v acc => (k0VecsAux ms (p - v * m)).map (fun rest => v :: rest) ++ acc) []

@[expose] def k0ReachAux (D : K0Diag) (nodes : List ℕ) (single : Bool) (start forbid : ℕ) :
    ℕ → List ℕ → List ℕ → List ℕ
  | 0, seen, _ => seen
  | _ + 1, seen, [] => seen
  | fuel + 1, seen, x :: rest =>
      let newNodes := nodes.filter (fun y =>
        decide (y ∉ seen ∧
          (if single then D.adj x y = 1 ∧ ¬ (x = start ∧ y = forbid) else D.adj x y > 0)))
      k0ReachAux D nodes single start forbid fuel (seen ++ newNodes) (rest ++ newNodes)

@[expose] def k0Reach (D : K0Diag) (nodes : List ℕ) (single : Bool) (start forbid : ℕ) : List ℕ :=
  k0ReachAux D nodes single start forbid (nodes.length + 1) [start] [start]

@[expose] def k0Side (D : K0Diag) (nodes : List ℕ) (start forbid : ℕ) : ℕ :=
  (k0Reach D nodes true start forbid).length

@[expose] def k0ArmSize (D : K0Diag) (nodes : List ℕ) (c nb : ℕ) : ℕ :=
  (k0ReachAux D nodes false nb 0 (nodes.length + 1) [c, nb] [nb]).length - 1

@[expose] def k0CompsAux (D : K0Diag) (zero : List ℕ) (seen : List ℕ) : List (List ℕ) :=
  match zero with
  | [] => []
  | i :: rest =>
      if i ∈ seen then k0CompsAux D rest seen
      else
        let comp := k0SortNat (k0Reach D zero false i 0)
        comp :: k0CompsAux D rest (seen ++ comp)

@[expose] def k0Comps (D : K0Diag) (zero : List ℕ) : List (List ℕ) := k0CompsAux D zero []

@[expose] def k0CompType (D : K0Diag) (nodes : List ℕ) : LargeEvenLieTag × ℕ :=
  let nodes := k0SortNat nodes
  let r := nodes.length
  let deg (i : ℕ) : ℕ := (nodes.filter (fun j => decide (j ≠ i ∧ D.adj i j > 0))).length
  let dbl := nodes.foldl (fun acc i =>
    acc ++ (nodes.filter (fun j => decide (i < j ∧ D.adj i j ≥ 2))).map (fun j => (i, j))) []
  match dbl with
  | [] =>
      let branch := nodes.filter (fun i => decide (deg i ≥ 3))
      match branch with
      | [] => (LargeEvenLieTag.A, r)
      | c :: _ =>
          let arms := k0SortNat ((nodes.filter (fun nb => decide (nb ≠ c ∧ D.adj c nb > 0))).map
            (fun nb => k0ArmSize D nodes c nb))
          if arms.take 2 = [1, 1] then (LargeEvenLieTag.D, r)
          else if arms = [1, 2, 2] then (LargeEvenLieTag.E6, 6)
          else if arms = [1, 2, 3] then (LargeEvenLieTag.E7, 7)
          else if arms = [1, 2, 4] then (LargeEvenLieTag.E8, 8)
          else (LargeEvenLieTag.A, r)
  | (i, j) :: _ =>
      if D.adj i j = 3 then (LargeEvenLieTag.G2, 2)
      else
        let u := if i ∈ D.long then i else j
        let v := if i ∈ D.long then j else i
        let a := k0Side D nodes u v
        let b := k0Side D nodes v u
        if r = 2 then (LargeEvenLieTag.C, 2)
        else if a ≥ 2 ∧ b ≥ 2 then (LargeEvenLieTag.F4, 4)
        else (LargeEvenLieTag.C, r)

@[expose] def k0AutOrder (c rk : List ℕ) : ℕ :=
  let rec go (o : ℕ) (cur : List ℕ) (fuel : ℕ) : ℕ :=
    match fuel with
    | 0 => o
    | fuel + 1 =>
        if c.all (fun i => decide (cur.getD i 0 = i)) then o
        else go (o + 1) (k0pMul rk cur) fuel
  go 1 rk (c.length + 1)

@[expose] def k0Tau0Of (fam : LargeEvenLieTag) (r : ℕ) : Bool :=
  match fam with
  | .A => decide (r ≥ 2)
  | .D => decide (r % 2 = 1)
  | .E6 => true
  | _ => false

@[expose] def k0LabelOf (fam : LargeEvenLieTag) (r tw nEff : ℕ) : GGKacOrbit :=
  let mk (tag : LargeEvenLieTag) (rk nn : ℕ) (qs : Bool) : GGKacOrbit := ⟨⟨tag, rk, nn⟩, qs⟩
  match fam with
  | .A =>
      if tw = 1 then mk .A r nEff (decide (¬ (r = 1 ∧ nEff = 1)))
      else mk .twA r nEff (decide (¬ (r = 2 ∧ nEff = 1)))
  | .C =>
      if r = 2 ∧ nEff = 1 then mk .B2der 0 1 true else mk .C r nEff true
  | .D =>
      if tw = 1 then mk .D r nEff true
      else if tw = 2 then mk .twD r nEff true
      else mk .triD4 0 nEff true
  | .E6 => if tw = 1 then mk .E6 0 nEff true else mk .twE6 0 nEff true
  | .E7 => mk .E7 0 nEff true
  | .E8 => mk .E8 0 nEff true
  | .F4 => mk .F4 0 nEff true
  | _ => mk fam 0 nEff true

@[expose] def k0TagIdx : LargeEvenLieTag → ℕ
  | .A => 0 | .twA => 1 | .B => 2 | .C => 3 | .D => 4 | .twD => 5
  | .E6 => 6 | .E7 => 7 | .E8 => 8 | .F4 => 9 | .twE6 => 10 | .triD4 => 11
  | .G2 => 12 | .twB2 => 13 | .twF4 => 14 | .B2der => 15 | .G2der => 16 | .twF4der => 17

@[expose] def k0OrbitKey (o : GGKacOrbit) : List ℕ :=
  [k0TagIdx o.lab.tag, o.lab.rank, o.lab.n, if o.qs then 1 else 0]

@[expose] def k0DatumKey (D : GGKacDatum) : List (List ℕ) := D.orbits.map k0OrbitKey

structure K0Keyed where
  keys : List (List ℕ)
  rZ : ℕ
  stabΩ : ℕ
  datum : GGKacDatum

@[expose] def k0KeyedLe (a b : K0Keyed) : Bool :=
  if k0LexLtKey a.keys b.keys then true
  else if k0LexLtKey b.keys a.keys then false
  else if a.rZ < b.rZ then true
  else if b.rZ < a.rZ then false
  else decide (a.stabΩ ≤ b.stabΩ)

@[expose] def k0SortDatums (raw : List GGKacDatum) : List GGKacDatum :=
  (k0SortBy k0KeyedLe
    (raw.map (fun D => ⟨k0DatumKey D, D.rZ, D.stabΩ, D⟩))).map (fun k => k.datum)

@[expose] def k0NodeOrbit (rho : List ℕ) (i : ℕ) : List ℕ :=
  let rec go (f : ℕ) (cur : ℕ) (acc : List ℕ) : List ℕ :=
    match f with
    | 0 => acc
    | f + 1 =>
        if cur = i then acc else go f (rho.getD cur 0) (acc ++ [cur])
  go (rho.length + 1) (rho.getD i 0) [i]

@[expose] def k0NumRhoOrbits (rho : List ℕ) (removed : List ℕ) : ℕ :=
  let rec go (nodes seen : List ℕ) (count : ℕ) : ℕ :=
    match nodes with
    | [] => count
    | i :: rest =>
        if i ∈ seen then go rest seen count
        else go rest (seen ++ k0NodeOrbit rho i) (count + 1)
  go removed [] 0

@[expose] def k0CompOrbit (img : List ℕ → List ℕ) (fuel : ℕ) (c : List ℕ) : List (List ℕ) :=
  let rec go (f : ℕ) (cur : List ℕ) (acc : List (List ℕ)) : List (List ℕ) :=
    match f with
    | 0 => acc
    | f + 1 =>
        if cur = c then acc else go f (img cur) (acc ++ [cur])
  go fuel (img c) [c]

@[expose] def k0CompOrbits (img : List ℕ → List ℕ) (fuel : ℕ) (cs seen : List (List ℕ)) :
    List (List (List ℕ)) :=
  match cs with
  | [] => []
  | c :: rest =>
      if c ∈ seen then k0CompOrbits img fuel rest seen
      else
        let orb := k0CompOrbit img fuel c
        orb :: k0CompOrbits img fuel rest (seen ++ orb)

@[expose] def k0Datum (D : K0Diag) (s rho : List ℕ) (d n stabΩ : ℕ) : GGKacDatum :=
  let nNodes := D.marks.length
  let zero := (List.range nNodes).filter (fun i => decide (s.getD i 0 = 0))
  let comps := k0Comps D zero
  let img : List ℕ → List ℕ := fun c => k0SortNat (c.map (fun i => rho.getD i 0))
  let orbits := (k0CompOrbits img (nNodes + 1) comps []).map (fun orb =>
    let k := orb.length
    let c := orb.headD []
    let p := k0CompType D c
    let rk := k0pPow rho k
    let o := k0AutOrder c rk
    let tw := if d = 2 ∧ k % 2 = 1 ∧ k0Tau0Of p.1 p.2 then
                (if o = 1 then 2 else if o = 2 then 1 else o) else o
    k0LabelOf p.1 p.2 tw (k * n))
  let orbitsSorted := k0SortBy (fun a b => k0LexLtNat (k0OrbitKey a) (k0OrbitKey b)) orbits
  let removed := (List.range nNodes).filter (fun i => decide (s.getD i 0 > 0))
  ⟨orbitsSorted, k0NumRhoOrbits rho removed - 1, stabΩ⟩

@[expose] def k0Rho0 (D : K0Diag) (tw : Bool) (d : ℕ) : List ℕ :=
  let tau := if tw then D.tau else k0pId D.marks.length
  if d = 1 then tau else k0pMul D.tau0 tau

@[expose] def k0BaseAux (rho0 s : List ℕ) : List (List ℕ) → Option (List ℕ)
  | [] => none
  | a0 :: rest =>
      let r := k0pMul a0 rho0
      if k0pAct r s = s then some r else k0BaseAux rho0 s rest

@[expose] def k0KacBase (D : K0Diag) (rho0 s : List ℕ) : Option (List ℕ) :=
  k0BaseAux rho0 s D.omega

@[expose] def k0RepsAux (stab : List (List ℕ)) (base : List ℕ) (fuel : ℕ)
    (as seenF acc : List (List ℕ)) :
    List (List ℕ) :=
  match fuel with
  | 0 => acc
  | fuel + 1 =>
      match as with
      | [] => acc
      | a :: rest =>
          let rho := k0pMul a base
          if rho ∈ seenF then k0RepsAux stab base fuel rest seenF acc
          else
            let conj := stab.map (fun b => k0pMul b (k0pMul rho (k0pInv b)))
            k0RepsAux stab base fuel rest (seenF ++ conj) (acc ++ [rho])

@[expose] def k0Reps (stab : List (List ℕ)) (base : List ℕ) : List (List ℕ) :=
  k0RepsAux stab base (stab.length + 1) stab [] []

@[expose] def k0OrbMin (D : K0Diag) (s : List ℕ) : List ℕ :=
  (k0SortBy k0LexLtNat (D.omega.map (fun a => k0pAct a s))).headD []

@[expose] def k0DatumsOf (D : K0Diag) (rho0 s : List ℕ) (d n : ℕ) : List GGKacDatum :=
  match k0KacBase D rho0 s with
  | none => []
  | some base =>
      let stab := D.omega.filter (fun a => decide (k0pAct a s = s))
      (k0Reps stab base).map (fun rho => k0Datum D s rho d n stab.length)

@[expose] def k0RawDatums (D : K0Diag) (tw : Bool) (p n d : ℕ) : List GGKacDatum :=
  let rho0 := k0Rho0 D tw d
  ((k0VecsAux D.marks p).filter (fun s => decide (k0OrbMin D s = s))).foldr
    (fun s acc => k0DatumsOf D rho0 s d n ++ acc) []

@[expose] def ggKacTable (T : GGKacType) (tw : Bool) (p n : ℕ) : List GGKacDatum :=
  let D := k0DiagOf T
  let q := 2 ^ n
  if p ∣ q - 1 then k0SortDatums (k0RawDatums D tw p n 1)
  else if p ∣ q + 1 then k0SortDatums (k0RawDatums D tw p n 2)
  else []

@[expose] def ggKacTypeOfLabel : LargeEvenLabel → Option (GGKacType × Bool) := fun lab =>
  match lab.tag with
  | .E6 => some (.E6, false)
  | .twE6 => some (.E6, true)
  | .E7 => some (.E7, false)
  | .E8 => some (.E8, false)
  | .F4 => some (.F4, false)
  | _ => none

@[expose] def GGKacValid (lab : LargeEvenLabel) (p : ℕ) (D : GGKacDatum) : Prop :=
  ∃ T tw, ggKacTypeOfLabel lab = some (T, tw) ∧ D ∈ ggKacTable T tw p lab.n

@[expose] def GGTCJKacExc : Prop := GGTCJKac GGKacGeneric GGKacValid

theorem GGTCJKacExc.toTCJGeneric (h : GGTCJKacExc) : GGTCJKnownGeneric :=
  GGK0Main.toTCJGeneric h.1

example : ggKacTable .F4 false 3 1 =
  [⟨[⟨⟨.twA, 2, 1⟩, false⟩, ⟨⟨.twA, 2, 1⟩, false⟩], 0, 1⟩,
  ⟨[⟨⟨.C, 3, 1⟩, true⟩], 1, 1⟩,
  ⟨[⟨⟨.C, 3, 1⟩, true⟩], 1, 1⟩,
  ⟨[⟨⟨.F4, 0, 1⟩, true⟩], 0, 1⟩] := by decide

example : ggKacTable .F4 false 5 2 =
  [⟨[⟨⟨.A, 1, 2⟩, true⟩, ⟨⟨.twA, 2, 2⟩, true⟩], 1, 1⟩,
  ⟨[⟨⟨.A, 1, 2⟩, true⟩, ⟨⟨.twA, 2, 2⟩, true⟩], 1, 1⟩,
  ⟨[⟨⟨.A, 1, 2⟩, true⟩, ⟨⟨.twA, 2, 2⟩, true⟩], 1, 1⟩,
  ⟨[⟨⟨.A, 1, 2⟩, true⟩, ⟨⟨.twA, 2, 2⟩, true⟩], 1, 1⟩,
  ⟨[⟨⟨.C, 2, 2⟩, true⟩], 2, 1⟩,
  ⟨[⟨⟨.C, 3, 2⟩, true⟩], 1, 1⟩,
  ⟨[⟨⟨.C, 3, 2⟩, true⟩], 1, 1⟩,
  ⟨[⟨⟨.C, 3, 2⟩, true⟩], 1, 1⟩,
  ⟨[⟨⟨.C, 3, 2⟩, true⟩], 1, 1⟩,
  ⟨[⟨⟨.F4, 0, 2⟩, true⟩], 0, 1⟩] := by decide

example : ggKacTable .E6 false 3 1 =
  [⟨[⟨⟨.A, 2, 2⟩, true⟩, ⟨⟨.twA, 2, 1⟩, false⟩], 0, 3⟩,
  ⟨[⟨⟨.A, 5, 1⟩, true⟩], 1, 1⟩,
  ⟨[⟨⟨.twD, 4, 1⟩, true⟩], 1, 3⟩,
  ⟨[⟨⟨.E6, 0, 1⟩, true⟩], 0, 1⟩] := by decide

example : ggKacTable .E6 true 3 1 =
  [⟨[⟨⟨.A, 1, 1⟩, false⟩, ⟨⟨.twA, 4, 1⟩, true⟩], 1, 1⟩,
  ⟨[⟨⟨.A, 1, 1⟩, false⟩, ⟨⟨.twA, 4, 1⟩, true⟩], 1, 1⟩,
  ⟨[⟨⟨.twA, 2, 1⟩, false⟩, ⟨⟨.twA, 2, 1⟩, false⟩, ⟨⟨.twA, 2, 1⟩, false⟩], 0, 3⟩,
  ⟨[⟨⟨.twA, 2, 3⟩, true⟩], 0, 3⟩,
  ⟨[⟨⟨.twA, 2, 3⟩, true⟩], 0, 3⟩,
  ⟨[⟨⟨.twA, 5, 1⟩, true⟩], 1, 1⟩,
  ⟨[⟨⟨.D, 4, 1⟩, true⟩], 2, 3⟩,
  ⟨[⟨⟨.twD, 5, 1⟩, true⟩], 1, 1⟩,
  ⟨[⟨⟨.twD, 5, 1⟩, true⟩], 1, 1⟩,
  ⟨[⟨⟨.twE6, 0, 1⟩, true⟩], 0, 1⟩,
  ⟨[⟨⟨.triD4, 0, 1⟩, true⟩], 0, 3⟩,
  ⟨[⟨⟨.triD4, 0, 1⟩, true⟩], 0, 3⟩] := by decide

example : ggKacTable .E7 false 3 1 =
  [⟨[⟨⟨.A, 1, 1⟩, false⟩, ⟨⟨.twD, 5, 1⟩, true⟩], 1, 1⟩,
  ⟨[⟨⟨.twA, 2, 1⟩, false⟩, ⟨⟨.twA, 5, 1⟩, true⟩], 0, 1⟩,
  ⟨[⟨⟨.twA, 6, 1⟩, true⟩], 1, 1⟩,
  ⟨[⟨⟨.D, 6, 1⟩, true⟩], 1, 1⟩,
  ⟨[⟨⟨.E7, 0, 1⟩, true⟩], 0, 1⟩,
  ⟨[⟨⟨.twE6, 0, 1⟩, true⟩], 1, 1⟩] := by decide

example : ggKacTable .E7 false 5 2 =
  [⟨[⟨⟨.A, 1, 2⟩, true⟩, ⟨⟨.twA, 2, 2⟩, true⟩, ⟨⟨.twA, 3, 2⟩, true⟩], 1, 1⟩,
  ⟨[⟨⟨.A, 1, 2⟩, true⟩, ⟨⟨.twA, 2, 2⟩, true⟩, ⟨⟨.twA, 3, 2⟩, true⟩], 1, 1⟩,
  ⟨[⟨⟨.A, 1, 2⟩, true⟩, ⟨⟨.twA, 4, 2⟩, true⟩], 2, 1⟩,
  ⟨[⟨⟨.A, 1, 2⟩, true⟩, ⟨⟨.twA, 4, 2⟩, true⟩], 2, 1⟩,
  ⟨[⟨⟨.A, 1, 2⟩, true⟩, ⟨⟨.twA, 5, 2⟩, true⟩], 1, 1⟩,
  ⟨[⟨⟨.A, 1, 2⟩, true⟩, ⟨⟨.twA, 5, 2⟩, true⟩], 1, 1⟩,
  ⟨[⟨⟨.A, 1, 2⟩, true⟩, ⟨⟨.D, 4, 2⟩, true⟩], 2, 1⟩,
  ⟨[⟨⟨.A, 1, 2⟩, true⟩, ⟨⟨.twD, 5, 2⟩, true⟩], 1, 1⟩,
  ⟨[⟨⟨.A, 1, 2⟩, true⟩, ⟨⟨.twD, 5, 2⟩, true⟩], 1, 1⟩,
  ⟨[⟨⟨.twA, 2, 2⟩, true⟩, ⟨⟨.twA, 4, 2⟩, true⟩], 1, 1⟩,
  ⟨[⟨⟨.twA, 2, 2⟩, true⟩, ⟨⟨.twA, 4, 2⟩, true⟩], 1, 1⟩,
  ⟨[⟨⟨.twA, 5, 2⟩, true⟩], 2, 1⟩,
  ⟨[⟨⟨.twA, 5, 2⟩, true⟩], 2, 1⟩,
  ⟨[⟨⟨.twA, 6, 2⟩, true⟩], 1, 1⟩,
  ⟨[⟨⟨.twA, 6, 2⟩, true⟩], 1, 1⟩,
  ⟨[⟨⟨.D, 6, 2⟩, true⟩], 1, 1⟩,
  ⟨[⟨⟨.D, 6, 2⟩, true⟩], 1, 1⟩,
  ⟨[⟨⟨.twD, 5, 2⟩, true⟩], 2, 1⟩,
  ⟨[⟨⟨.twD, 5, 2⟩, true⟩], 2, 1⟩,
  ⟨[⟨⟨.E7, 0, 2⟩, true⟩], 0, 1⟩,
  ⟨[⟨⟨.twE6, 0, 2⟩, true⟩], 1, 1⟩,
  ⟨[⟨⟨.twE6, 0, 2⟩, true⟩], 1, 1⟩] := by decide

example : ggKacTable .E8 false 3 1 =
  [⟨[⟨⟨.twA, 2, 1⟩, false⟩, ⟨⟨.twE6, 0, 1⟩, true⟩], 0, 1⟩,
  ⟨[⟨⟨.twA, 8, 1⟩, true⟩], 0, 1⟩,
  ⟨[⟨⟨.twD, 7, 1⟩, true⟩], 1, 1⟩,
  ⟨[⟨⟨.E7, 0, 1⟩, true⟩], 1, 1⟩,
  ⟨[⟨⟨.E8, 0, 1⟩, true⟩], 0, 1⟩] := by decide

example : (ggKacTable .E6 false 7 3).length = 77 := by decide
example : ggKacTypeOfLabel ⟨.twE6, 0, 1⟩ = some (.E6, true) := by decide

@[expose] def ggKacShapeLabel (n : ℕ) (lab : LargeEvenLabel) : LargeEvenLieTag × ℕ × ℕ :=
  match lab.tag with
  | .B2der => (.C, 2, lab.n / n)
  | t => (t, lab.rank, lab.n / n)

@[expose] def GGKacDatum.shape (n : ℕ) (D : GGKacDatum) :
    Multiset (LargeEvenLieTag × ℕ × ℕ) × ℕ × ℕ :=
  (↑(D.orbits.map fun o => ggKacShapeLabel n o.lab), D.rZ, D.stabΩ)

private def k0shapeTagRank (fam : LargeEvenLieTag) (r tw : ℕ) : LargeEvenLieTag × ℕ :=
  match fam with
  | .A => if tw = 1 then (.A, r) else (.twA, r)
  | .C => (.C, r)
  | .D => if tw = 1 then (.D, r) else if tw = 2 then (.twD, r) else (.triD4, 0)
  | .E6 => if tw = 1 then (.E6, 0) else (.twE6, 0)
  | .E7 => (.E7, 0)
  | .E8 => (.E8, 0)
  | .F4 => (.F4, 0)
  | .B2der => (.C, 2)
  | _ => (fam, 0)

private lemma k0shape_insertBy_perm {α : Type} (le : α → α → Bool) (a : α) (l : List α) :
    (k0InsertBy le a l).Perm (a :: l) := by
  induction l with
  | nil => simp [k0InsertBy]
  | cons b bs ih =>
      unfold k0InsertBy
      split
      · exact List.Perm.refl _
      · exact (List.Perm.cons b ih).trans (List.Perm.swap a b bs)

private lemma k0shape_sortBy_perm {α : Type} (le : α → α → Bool) (l : List α) :
    (k0SortBy le l).Perm l := by
  induction l with
  | nil => simp [k0SortBy]
  | cons a as ih =>
      unfold k0SortBy
      exact (k0shape_insertBy_perm le a (k0SortBy le as)).trans (List.Perm.cons a ih)

lemma k0shape_sortDatums_perm (raw : List GGKacDatum) :
    (k0SortDatums raw).Perm raw := by
  have h : (raw.map (fun D => (⟨k0DatumKey D, D.rZ, D.stabΩ, D⟩ : K0Keyed))).map
      (fun k => k.datum) = raw := by
    have hfun : ((fun k : K0Keyed => k.datum) ∘
        fun D => (⟨k0DatumKey D, D.rZ, D.stabΩ, D⟩ : K0Keyed)) = id := by
      funext D; rfl
    rw [List.map_map, hfun, List.map_id]
  exact ((k0shape_sortBy_perm k0KeyedLe _).map (fun k => k.datum)).trans (List.Perm.of_eq h)

private lemma k0shape_sorted_map_eq {β : Type} (raw : List GGKacDatum) (sh : GGKacDatum → β) :
    (↑((k0SortDatums raw).map sh) : Multiset β) = ↑(raw.map sh) :=
  Multiset.coe_eq_coe.mpr ((k0shape_sortDatums_perm raw).map sh)

private lemma k0shape_mul_eq_one {k n : ℕ} (hn : 1 ≤ n) (h : k * n = 1) :
    k = 1 ∧ n = 1 := by
  have hn1 : n = 1 := Nat.dvd_one.mp ⟨k, by rw [mul_comm]; exact h.symm⟩
  subst hn1
  exact ⟨by simpa using h, rfl⟩

private lemma k0shape_mul_ne_one {k n : ℕ} (hn : 2 ≤ n) : k * n ≠ 1 := by
  intro h
  have hn1 : n = 1 := Nat.dvd_one.mp ⟨k, by rw [mul_comm]; exact h.symm⟩
  omega

private lemma k0shape_label_shape_eq (n : ℕ) (hn : 1 ≤ n) (fam : LargeEvenLieTag)
    (r tw k : ℕ) :
    ggKacShapeLabel n (k0LabelOf fam r tw (k * n)).lab =
      ((k0shapeTagRank fam r tw).1, (k0shapeTagRank fam r tw).2, k) := by
  have hdiv : k * n / n = k := Nat.mul_div_left k (Nat.lt_of_lt_of_le Nat.zero_lt_one hn)
  cases fam
  case A =>
    simp only [k0LabelOf, k0shapeTagRank]
    by_cases htw : tw = 1
    · simp only [if_pos htw, ggKacShapeLabel]; rw [hdiv]
    · simp only [if_neg htw, ggKacShapeLabel]; rw [hdiv]
  case C =>
    simp only [k0LabelOf, k0shapeTagRank]
    by_cases hc : r = 2 ∧ k * n = 1
    · simp only [if_pos hc]
      obtain ⟨hr, hkn⟩ := hc
      obtain ⟨hk, hn1⟩ := k0shape_mul_eq_one hn hkn
      subst hr; subst hk; subst hn1
      simp only [ggKacShapeLabel]
    · simp only [if_neg hc, ggKacShapeLabel]; rw [hdiv]
  case D =>
    simp only [k0LabelOf, k0shapeTagRank]
    by_cases h1 : tw = 1
    · simp only [if_pos h1, ggKacShapeLabel]; rw [hdiv]
    · simp only [if_neg h1]
      by_cases h2 : tw = 2
      · simp only [if_pos h2, ggKacShapeLabel]; rw [hdiv]
      · simp only [if_neg h2, ggKacShapeLabel]; rw [hdiv]
  case E6 =>
    simp only [k0LabelOf, k0shapeTagRank]
    by_cases h1 : tw = 1
    · simp only [if_pos h1, ggKacShapeLabel]; rw [hdiv]
    · simp only [if_neg h1, ggKacShapeLabel]; rw [hdiv]
  case E7 => simp only [k0LabelOf, k0shapeTagRank, ggKacShapeLabel]; rw [hdiv]
  case E8 => simp only [k0LabelOf, k0shapeTagRank, ggKacShapeLabel]; rw [hdiv]
  case F4 => simp only [k0LabelOf, k0shapeTagRank, ggKacShapeLabel]; rw [hdiv]
  case B2der => simp only [k0LabelOf, k0shapeTagRank, ggKacShapeLabel]; rw [hdiv]
  all_goals
    simp only [k0LabelOf, k0shapeTagRank, ggKacShapeLabel]
    rw [hdiv]

private lemma k0shape_label_shape_eq_one (n : ℕ) (hn : 1 ≤ n) (fam : LargeEvenLieTag)
    (r tw k : ℕ) :
    ggKacShapeLabel n (k0LabelOf fam r tw (k * n)).lab =
      ggKacShapeLabel 1 (k0LabelOf fam r tw (k * 1)).lab := by
  rw [k0shape_label_shape_eq n hn fam r tw k,
    k0shape_label_shape_eq 1 le_rfl fam r tw k]

private def k0shapeOrbLabel (D : K0Diag) (rho : List ℕ) (d n : ℕ) (orb : List (List ℕ)) :
    GGKacOrbit :=
  let k := orb.length
  let c := orb.headD []
  let p := k0CompType D c
  let rk := k0pPow rho k
  let o := k0AutOrder c rk
  let tw := if d = 2 ∧ k % 2 = 1 ∧ k0Tau0Of p.1 p.2 then
              (if o = 1 then 2 else if o = 2 then 1 else o) else o
  k0LabelOf p.1 p.2 tw (k * n)

private def k0shapeOrbitsRaw (D : K0Diag) (s rho : List ℕ) (d n : ℕ) : List GGKacOrbit :=
  let nNodes := D.marks.length
  let zero := (List.range nNodes).filter (fun i => decide (s.getD i 0 = 0))
  let comps := k0Comps D zero
  let img : List ℕ → List ℕ := fun c => k0SortNat (c.map (fun i => rho.getD i 0))
  (k0CompOrbits img (nNodes + 1) comps []).map (k0shapeOrbLabel D rho d n)

private lemma k0shapeOrbLabel_shape (D : K0Diag) (rho : List ℕ) (d n : ℕ) (orb : List (List ℕ))
    (hn : 1 ≤ n) :
    ggKacShapeLabel n (k0shapeOrbLabel D rho d n orb).lab =
      ggKacShapeLabel 1 (k0shapeOrbLabel D rho d 1 orb).lab := by
  simp only [k0shapeOrbLabel]
  exact k0shape_label_shape_eq_one n hn _ _ _ _

private lemma k0shape_datum_orbits (D : K0Diag) (s rho : List ℕ) (d n st : ℕ) :
    (k0Datum D s rho d n st).orbits =
      k0SortBy (fun a b => k0LexLtNat (k0OrbitKey a) (k0OrbitKey b))
        (k0shapeOrbitsRaw D s rho d n) := by
  unfold k0Datum k0shapeOrbitsRaw k0shapeOrbLabel
  rfl

private lemma k0shape_datum_shape (D : K0Diag) (s rho : List ℕ) (d st n : ℕ) (hn : 1 ≤ n) :
    GGKacDatum.shape n (k0Datum D s rho d n st) =
      GGKacDatum.shape 1 (k0Datum D s rho d 1 st) := by
  have hmap : (k0shapeOrbitsRaw D s rho d n).map (fun o => ggKacShapeLabel n o.lab) =
      (k0shapeOrbitsRaw D s rho d 1).map (fun o => ggKacShapeLabel 1 o.lab) := by
    simp only [k0shapeOrbitsRaw, List.map_map]
    apply List.map_congr_left
    intro orb _
    exact k0shapeOrbLabel_shape D rho d n orb hn
  simp only [GGKacDatum.shape]
  refine Prod.ext ?_ (Prod.ext rfl rfl)
  rw [k0shape_datum_orbits D s rho d n st, k0shape_datum_orbits D s rho d 1 st]
  apply Multiset.coe_eq_coe.mpr
  exact ((k0shape_sortBy_perm _ (k0shapeOrbitsRaw D s rho d n)).map
        (fun o => ggKacShapeLabel n o.lab)).trans
      ((List.Perm.of_eq hmap).trans
        ((k0shape_sortBy_perm _ (k0shapeOrbitsRaw D s rho d 1)).map
          (fun o => ggKacShapeLabel 1 o.lab)).symm)

private lemma k0shape_datumsOf_shape (D : K0Diag) (rho0 s : List ℕ) (d n : ℕ) (hn : 1 ≤ n) :
    (↑((k0DatumsOf D rho0 s d n).map (GGKacDatum.shape n)) :
        Multiset (Multiset (LargeEvenLieTag × ℕ × ℕ) × ℕ × ℕ)) =
      (↑((k0DatumsOf D rho0 s d 1).map (GGKacDatum.shape 1)) :
        Multiset (Multiset (LargeEvenLieTag × ℕ × ℕ) × ℕ × ℕ)) := by
  unfold k0DatumsOf
  split
  · rfl
  · simp only [List.map_map]
    apply Multiset.coe_eq_coe.mpr
    exact List.Perm.of_eq
      (List.map_congr_left (fun rho _ => k0shape_datum_shape D s rho d _ n hn))

private lemma k0shape_foldr_one (D : K0Diag) (rho0 : List ℕ) (d n : ℕ) (l : List (List ℕ))
    (hn : 1 ≤ n) :
    (↑((l.foldr (fun s acc => k0DatumsOf D rho0 s d n ++ acc) []).map
        (GGKacDatum.shape n)) :
        Multiset (Multiset (LargeEvenLieTag × ℕ × ℕ) × ℕ × ℕ)) =
      (↑((l.foldr (fun s acc => k0DatumsOf D rho0 s d 1 ++ acc) []).map
        (GGKacDatum.shape 1)) :
        Multiset (Multiset (LargeEvenLieTag × ℕ × ℕ) × ℕ × ℕ)) := by
  induction l with
  | nil => rfl
  | cons s rest ih =>
      simp only [List.foldr_cons, List.map_append, ← Multiset.coe_add]
      rw [k0shape_datumsOf_shape D rho0 s d n hn, ih]

private lemma k0shape_rawFoldr (D : K0Diag) (rho0 : List ℕ) (d n n' : ℕ) (l : List (List ℕ))
    (hn : 1 ≤ n) (hn' : 1 ≤ n') :
    (↑((l.foldr (fun s acc => k0DatumsOf D rho0 s d n ++ acc) []).map
        (GGKacDatum.shape n)) :
        Multiset (Multiset (LargeEvenLieTag × ℕ × ℕ) × ℕ × ℕ)) =
      (↑((l.foldr (fun s acc => k0DatumsOf D rho0 s d n' ++ acc) []).map
        (GGKacDatum.shape n')) :
        Multiset (Multiset (LargeEvenLieTag × ℕ × ℕ) × ℕ × ℕ)) := by
  rw [k0shape_foldr_one D rho0 d n l hn, k0shape_foldr_one D rho0 d n' l hn']

private lemma k0shape_rawDatums_shape (D : K0Diag) (tw : Bool) (p d n n' : ℕ)
    (hn : 1 ≤ n) (hn' : 1 ≤ n') :
    (↑((k0RawDatums D tw p n d).map (GGKacDatum.shape n)) :
        Multiset (Multiset (LargeEvenLieTag × ℕ × ℕ) × ℕ × ℕ)) =
      (↑((k0RawDatums D tw p n' d).map (GGKacDatum.shape n')) :
        Multiset (Multiset (LargeEvenLieTag × ℕ × ℕ) × ℕ × ℕ)) :=
  k0shape_rawFoldr D (k0Rho0 D tw d) d n n'
    ((k0VecsAux D.marks p).filter (fun s => decide (k0OrbMin D s = s))) hn hn'

lemma k0shape_table_branch1 (T : GGKacType) (tw : Bool) (p n : ℕ)
    (h : p ∣ 2 ^ n - 1) :
    ggKacTable T tw p n = k0SortDatums (k0RawDatums (k0DiagOf T) tw p n 1) := by
  unfold ggKacTable
  rw [if_pos h]

lemma k0shape_table_branch2 (T : GGKacType) (tw : Bool) (p n : ℕ)
    (h1 : ¬ p ∣ 2 ^ n - 1) (h2 : p ∣ 2 ^ n + 1) :
    ggKacTable T tw p n = k0SortDatums (k0RawDatums (k0DiagOf T) tw p n 2) := by
  unfold ggKacTable
  rw [if_neg h1, if_pos h2]

lemma k0shape_table_branch0 (T : GGKacType) (tw : Bool) (p n : ℕ)
    (h1 : ¬ p ∣ 2 ^ n - 1) (h2 : ¬ p ∣ 2 ^ n + 1) :
    ggKacTable T tw p n = [] := by
  unfold ggKacTable
  rw [if_neg h1, if_neg h2]

private lemma k0shape_dvd_pos_imp_not_dvd_neg {p n : ℕ} (hp : p.Prime) (hn : 1 ≤ n) :
    p ∣ 2 ^ n + 1 → ¬ p ∣ 2 ^ n - 1 := by
  intro h2 h1
  have hp2 : p ∣ 2 := by
    have hsub : p ∣ (2 ^ n + 1) - (2 ^ n - 1) := Nat.dvd_sub h2 h1
    have heq : (2 ^ n + 1) - (2 ^ n - 1) = 2 := by
      have hp1 : 1 ≤ 2 ^ n := Nat.one_le_two_pow
      omega
    rwa [heq] at hsub
  have hp_eq : p = 2 := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp hp2
  subst hp_eq
  exact (Odd.not_two_dvd_nat ((Even.pow_of_ne_zero even_two (by omega : n ≠ 0)).add_one)) h2

theorem ggKacTable_shape (T : GGKacType) (tw : Bool) {p n n' : ℕ} (hp : p.Prime)
    (hn : 1 ≤ n) (hn' : 1 ≤ n')
    (hd : (p ∣ 2 ^ n - 1 ∧ p ∣ 2 ^ n' - 1) ∨ (p ∣ 2 ^ n + 1 ∧ p ∣ 2 ^ n' + 1)) :
    (↑((ggKacTable T tw p n).map (GGKacDatum.shape n)) :
        Multiset (Multiset (LargeEvenLieTag × ℕ × ℕ) × ℕ × ℕ)) =
      ↑((ggKacTable T tw p n').map (GGKacDatum.shape n')) := by
  rcases hd with ⟨h1n, h1n'⟩ | ⟨h2n, h2n'⟩
  · rw [k0shape_table_branch1 T tw p n h1n, k0shape_table_branch1 T tw p n' h1n']
    rw [k0shape_sorted_map_eq (k0RawDatums (k0DiagOf T) tw p n 1) (GGKacDatum.shape n),
      k0shape_sorted_map_eq (k0RawDatums (k0DiagOf T) tw p n' 1) (GGKacDatum.shape n')]
    exact k0shape_rawDatums_shape (k0DiagOf T) tw p 1 n n' hn hn'
  · have h1n : ¬ p ∣ 2 ^ n - 1 := k0shape_dvd_pos_imp_not_dvd_neg hp hn h2n
    have h1n' : ¬ p ∣ 2 ^ n' - 1 := k0shape_dvd_pos_imp_not_dvd_neg hp hn' h2n'
    rw [k0shape_table_branch2 T tw p n h1n h2n, k0shape_table_branch2 T tw p n' h1n' h2n']
    rw [k0shape_sorted_map_eq (k0RawDatums (k0DiagOf T) tw p n 2) (GGKacDatum.shape n),
      k0shape_sorted_map_eq (k0RawDatums (k0DiagOf T) tw p n' 2) (GGKacDatum.shape n')]
    exact k0shape_rawDatums_shape (k0DiagOf T) tw p 2 n n' hn hn'

private lemma k0shape_label_qs (fam : LargeEvenLieTag) (r tw k n : ℕ) (hn : 2 ≤ n) :
    (k0LabelOf fam r tw (k * n)).qs = true := by
  have hne : k * n ≠ 1 := k0shape_mul_ne_one hn
  cases fam <;> simp only [k0LabelOf] <;>
    first
      | (split_ifs <;> simp_all [hne])
      | rfl

private lemma k0shapeOrbLabel_qs (D : K0Diag) (rho : List ℕ) (d n : ℕ) (orb : List (List ℕ))
    (hn : 2 ≤ n) : (k0shapeOrbLabel D rho d n orb).qs = true := by
  simp only [k0shapeOrbLabel]
  exact k0shape_label_qs _ _ _ _ n hn

private lemma k0shapeOrbitsRaw_qs (D : K0Diag) (s rho : List ℕ) (d n : ℕ) (hn : 2 ≤ n) :
    ∀ o ∈ k0shapeOrbitsRaw D s rho d n, o.qs = true := by
  intro o ho
  simp only [k0shapeOrbitsRaw, List.mem_map] at ho
  obtain ⟨orb, _, rfl⟩ := ho
  exact k0shapeOrbLabel_qs D rho d n orb hn

private lemma k0shape_datum_qs (D : K0Diag) (s rho : List ℕ) (d n st : ℕ) (hn : 2 ≤ n) :
    ∀ o ∈ (k0Datum D s rho d n st).orbits, o.qs = true := by
  intro o ho
  rw [k0shape_datum_orbits D s rho d n st] at ho
  have hperm : (k0SortBy (fun a b => k0LexLtNat (k0OrbitKey a) (k0OrbitKey b))
      (k0shapeOrbitsRaw D s rho d n)).Perm (k0shapeOrbitsRaw D s rho d n) :=
    k0shape_sortBy_perm _ _
  exact k0shapeOrbitsRaw_qs D s rho d n hn o (hperm.mem_iff.mp ho)

private lemma k0shape_datumsOf_qs (D : K0Diag) (rho0 s : List ℕ) (d n : ℕ) (hn : 2 ≤ n) :
    ∀ D' ∈ k0DatumsOf D rho0 s d n, ∀ o ∈ D'.orbits, o.qs = true := by
  intro D' hD' o ho
  unfold k0DatumsOf at hD'
  split at hD'
  · simp at hD'
  · simp only [List.mem_map] at hD'
    obtain ⟨rho, _, rfl⟩ := hD'
    exact k0shape_datum_qs D s rho d n _ hn o ho

lemma k0shape_mem_foldr_append {α β : Type} (l : List α) (F : α → List β) (x : β) :
    x ∈ l.foldr (fun s acc => F s ++ acc) [] ↔ ∃ s ∈ l, x ∈ F s := by
  induction l with
  | nil => simp
  | cons s rest ih =>
      simp only [List.foldr_cons, List.mem_append, List.mem_cons, ih]
      constructor
      · rintro (h | ⟨t, ht, hx⟩)
        · exact ⟨s, Or.inl rfl, h⟩
        · exact ⟨t, Or.inr ht, hx⟩
      · rintro ⟨t, hts, hx⟩
        rcases hts with rfl | ht
        · exact Or.inl hx
        · exact Or.inr ⟨t, ht, hx⟩

private lemma k0shape_rawDatums_qs (D : K0Diag) (tw : Bool) (p d n : ℕ) (hn : 2 ≤ n) :
    ∀ D' ∈ k0RawDatums D tw p n d, ∀ o ∈ D'.orbits, o.qs = true := by
  intro D' hD' o ho
  unfold k0RawDatums at hD'
  simp only [k0shape_mem_foldr_append] at hD'
  obtain ⟨s, _, hs⟩ := hD'
  exact k0shape_datumsOf_qs D (k0Rho0 D tw d) s d n hn D' hs o ho

theorem ggKacTable_qs_of_two_le (T : GGKacType) (tw : Bool) (p : ℕ) {n : ℕ} (hn : 2 ≤ n) :
    ∀ D ∈ ggKacTable T tw p n, ∀ o ∈ D.orbits, o.qs = true := by
  intro D hD o ho
  by_cases h1 : p ∣ 2 ^ n - 1
  · rw [k0shape_table_branch1 T tw p n h1] at hD
    exact k0shape_rawDatums_qs (k0DiagOf T) tw p 1 n hn D
      ((k0shape_sortDatums_perm _).mem_iff.mp hD) o ho
  · by_cases h2 : p ∣ 2 ^ n + 1
    · rw [k0shape_table_branch2 T tw p n h1 h2] at hD
      exact k0shape_rawDatums_qs (k0DiagOf T) tw p 2 n hn D
        ((k0shape_sortDatums_perm _).mem_iff.mp hD) o ho
    · rw [k0shape_table_branch0 T tw p n h1 h2] at hD
      simp at hD

example : (↑((ggKacTable .E6 false 3 2).map (GGKacDatum.shape 2)) :
    Multiset (Multiset (LargeEvenLieTag × ℕ × ℕ) × ℕ × ℕ)) =
    ↑((ggKacTable .E6 false 3 4).map (GGKacDatum.shape 4)) := by decide

example : (↑((ggKacTable .E6 false 3 1).map (GGKacDatum.shape 1)) :
    Multiset (Multiset (LargeEvenLieTag × ℕ × ℕ) × ℕ × ℕ)) =
    ↑((ggKacTable .E6 false 3 3).map (GGKacDatum.shape 3)) := by decide

end CFSG.StandardType

end

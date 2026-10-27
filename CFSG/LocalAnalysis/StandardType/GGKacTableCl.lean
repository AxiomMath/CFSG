module

public import CFSG.LocalAnalysis.StandardType.GGKacK0

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

private local instance (priority := high) k1tabDecidableEqLargeEvenLabel : DecidableEq LargeEvenLabel :=
  fun a b =>
    match a, b with
    | ⟨ta, ra, na⟩, ⟨tb, rb, nb⟩ =>
      if h1 : ta = tb then
        if h2 : ra = rb then
          if h3 : na = nb then isTrue (by cases h1; cases h2; cases h3; rfl)
          else isFalse (by intro h; injection h with _ _ h3'; exact h3 h3')
        else isFalse (by intro h; injection h with _ h2' _; exact h2 h2')
      else isFalse (by intro h; injection h with h1' _ _; exact h1 h1')

private local instance (priority := high) k1tabDecidableEqGGKacOrbit : DecidableEq GGKacOrbit :=
  fun a b =>
    match a, b with
    | ⟨la, qa⟩, ⟨lb, qb⟩ =>
      if h1 : la = lb then
        if h2 : qa = qb then isTrue (by cases h1; cases h2; rfl)
        else isFalse (by intro h; injection h with _ h2'; exact h2 h2')
      else isFalse (by intro h; injection h with h1' _; exact h1 h1')

private local instance (priority := high) k1tabDecidableEqGGKacDatum : DecidableEq GGKacDatum :=
  fun a b =>
    match a, b with
    | ⟨oa, za, sa⟩, ⟨ob, zb, sb⟩ =>
      if h1 : oa = ob then
        if h2 : za = zb then
          if h3 : sa = sb then isTrue (by cases h1; cases h2; cases h3; rfl)
          else isFalse (by intro h; injection h with _ _ h3'; exact h3 h3')
        else isFalse (by intro h; injection h with _ h2' _; exact h2 h2')
      else isFalse (by intro h; injection h with h1' _ _; exact h1 h1')

inductive GGKacTypeCl | A (l : ℕ) | C (l : ℕ) | D (l : ℕ)
  deriving DecidableEq

@[expose] def k1pId (n : ℕ) : List ℕ := List.range n

@[expose] def k1pMul (a b : List ℕ) : List ℕ := b.map (fun i => a.getD i 0)

@[expose] def k1pInv (a : List ℕ) : List ℕ :=
  let rec go (i : ℕ) (l : List ℕ) (acc : List ℕ) : List ℕ :=
    match l with
    | [] => acc
    | x :: xs => go (i + 1) xs (acc.set x i)
  go 0 a (List.replicate a.length 0)

@[expose] def k1pAct (a s : List ℕ) : List ℕ :=
  let rec go (i : ℕ) (l : List ℕ) (acc : List ℕ) : List ℕ :=
    match l with
    | [] => acc
    | x :: xs => go (i + 1) xs (acc.set x (s.getD i 0))
  go 0 a (List.replicate s.length 0)

@[expose] def k1pPow (a : List ℕ) (k : ℕ) : List ℕ :=
  let rec go (f : ℕ) (acc : List ℕ) : List ℕ :=
    match f with
    | 0 => acc
    | f + 1 => go f (k1pMul a acc)
  go k (k1pId a.length)

structure K1Diag where
  marks : List ℕ
  edges : List (ℕ × ℕ × ℕ)
  long : List ℕ
  omega : List (List ℕ)
  tau : List ℕ
  tau0 : List ℕ

@[expose] def K1Diag.adj (D : K1Diag) (i j : ℕ) : ℕ :=
  match D.edges.find? (fun e => (e.1 = i ∧ e.2.1 = j) ∨ (e.1 = j ∧ e.2.1 = i)) with
  | some e => e.2.2
  | none => 0

@[expose] def k1ADiag (l : ℕ) : K1Diag :=
  let nn := l + 1
  let tau := (List.range nn).map (fun i => (nn - i) % nn)
  { marks := List.replicate nn 1
    edges := if 2 ≤ l then (List.range nn).map (fun i => (i, (i + 1) % nn, 1))
      else [(0, 1, 2)]
    long := []
    omega := (List.range nn).map (fun k => (List.range nn).map (fun i => (i + k) % nn))
    tau := tau
    tau0 := if 2 ≤ l then tau else k1pId nn }

@[expose] def k1CDiag (l : ℕ) : K1Diag :=
  let nn := l + 1
  { marks := [1] ++ List.replicate (l - 1) 2 ++ [1]
    edges := (List.range l).map (fun i => (i, i + 1, if i = 0 ∨ i = l - 1 then 2 else 1))
    long := [0, l]
    omega := [k1pId nn, (List.range nn).map (fun i => l - i)]
    tau := k1pId nn
    tau0 := k1pId nn }

@[expose] def k1Dmk (l : ℕ) (ass : List (ℕ × ℕ)) (rev : Bool) : List ℕ :=
  let nn := l + 1
  let base := ass.foldl (fun (p : List ℕ) (ab : ℕ × ℕ) => p.set ab.1 ab.2) (k1pId nn)
  if rev then
    (List.range nn).map (fun i => if 2 ≤ i ∧ i < l - 1 then l - i else base.getD i 0)
  else base

@[expose] def k1DDiag (l : ℕ) : K1Diag :=
  let nn := l + 1
  let e := k1pId nn
  let a := k1Dmk l [(0, 1), (1, 0), (l - 1, l), (l, l - 1)] false
  let c4 := k1Dmk l [(0, l - 1), (l - 1, 1), (1, l), (l, 0)] true
  let tau := k1Dmk l [(l - 1, l), (l, l - 1)] false
  { marks := [1, 1] ++ List.replicate (l - 3) 2 ++ [1, 1]
    edges := [(0, 2, 1), (1, 2, 1)] ++
      (List.range (l - 2 - 2)).map (fun i => (i + 2, i + 3, 1)) ++
      [(l - 2, l - 1, 1), (l - 2, l, 1)]
    long := []
    omega := if l % 2 = 0 then
        [e, a, k1Dmk l [(0, l - 1), (l - 1, 0), (1, l), (l, 1)] true,
         k1Dmk l [(0, l), (l, 0), (1, l - 1), (l - 1, 1)] true]
      else
        [e, c4, k1pMul c4 c4, k1pMul c4 (k1pMul c4 c4)]
    tau := tau
    tau0 := if l % 2 = 1 then tau else k1pId nn }

@[expose] def k1DiagOf : GGKacTypeCl → K1Diag
  | .A l => k1ADiag l
  | .C l => k1CDiag l
  | .D l => k1DDiag l

@[expose] def k1InsertBy {α : Type} (le : α → α → Bool) (a : α) : List α → List α
  | [] => [a]
  | b :: bs => if le a b then a :: b :: bs else b :: k1InsertBy le a bs

@[expose] def k1SortBy {α : Type} (le : α → α → Bool) : List α → List α
  | [] => []
  | a :: as => k1InsertBy le a (k1SortBy le as)

@[expose] def k1SortNat (l : List ℕ) : List ℕ := k1SortBy (fun a b => decide (a ≤ b)) l

@[expose] def k1LexLtNat : List ℕ → List ℕ → Bool
  | [], [] => false
  | [], _ :: _ => true
  | _ :: _, [] => false
  | x :: xs, y :: ys =>
      if x < y then true else if y < x then false else k1LexLtNat xs ys

@[expose] def k1LexLtKey : List (List ℕ) → List (List ℕ) → Bool
  | [], [] => false
  | [], _ :: _ => true
  | _ :: _, [] => false
  | x :: xs, y :: ys =>
      if k1LexLtNat x y then true
      else if k1LexLtNat y x then false
      else k1LexLtKey xs ys

@[expose] def k1VecsAux : List ℕ → ℕ → List (List ℕ)
  | [], p => if p = 0 then [[]] else []
  | m :: ms, p =>
      (List.range (p / m + 1)).foldr
        (fun v acc => (k1VecsAux ms (p - v * m)).map (fun rest => v :: rest) ++ acc) []

@[expose] def k1ReachAux (D : K1Diag) (nodes : List ℕ) (single : Bool) (start forbid : ℕ) :
    ℕ → List ℕ → List ℕ → List ℕ
  | 0, seen, _ => seen
  | _ + 1, seen, [] => seen
  | fuel + 1, seen, x :: rest =>
      let newNodes := nodes.filter (fun y =>
        decide (y ∉ seen ∧
          (if single then D.adj x y = 1 ∧ ¬ (x = start ∧ y = forbid) else D.adj x y > 0)))
      k1ReachAux D nodes single start forbid fuel (seen ++ newNodes) (rest ++ newNodes)

@[expose] def k1Reach (D : K1Diag) (nodes : List ℕ) (single : Bool) (start forbid : ℕ) : List ℕ :=
  k1ReachAux D nodes single start forbid (nodes.length + 1) [start] [start]

@[expose] def k1Side (D : K1Diag) (nodes : List ℕ) (start forbid : ℕ) : ℕ :=
  (k1Reach D nodes true start forbid).length

@[expose] def k1ArmSize (D : K1Diag) (nodes : List ℕ) (c nb : ℕ) : ℕ :=
  (k1ReachAux D nodes false nb 0 (nodes.length + 1) [c, nb] [nb]).length - 1

@[expose] def k1CompsAux (D : K1Diag) (zero : List ℕ) (seen : List ℕ) : List (List ℕ) :=
  match zero with
  | [] => []
  | i :: rest =>
      if i ∈ seen then k1CompsAux D rest seen
      else
        let comp := k1SortNat (k1Reach D zero false i 0)
        comp :: k1CompsAux D rest (seen ++ comp)

@[expose] def k1Comps (D : K1Diag) (zero : List ℕ) : List (List ℕ) := k1CompsAux D zero []

@[expose] def k1CompType (D : K1Diag) (nodes : List ℕ) : LargeEvenLieTag × ℕ :=
  let nodes := k1SortNat nodes
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
          let arms := k1SortNat ((nodes.filter (fun nb => decide (nb ≠ c ∧ D.adj c nb > 0))).map
            (fun nb => k1ArmSize D nodes c nb))
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
        let a := k1Side D nodes u v
        let b := k1Side D nodes v u
        if r = 2 then (LargeEvenLieTag.C, 2)
        else if a ≥ 2 ∧ b ≥ 2 then (LargeEvenLieTag.F4, 4)
        else (LargeEvenLieTag.C, r)

@[expose] def k1AutOrder (c rk : List ℕ) : ℕ :=
  let rec go (o : ℕ) (cur : List ℕ) (fuel : ℕ) : ℕ :=
    match fuel with
    | 0 => o
    | fuel + 1 =>
        if c.all (fun i => decide (cur.getD i 0 = i)) then o
        else go (o + 1) (k1pMul rk cur) fuel
  go 1 rk (c.length + 1)

@[expose] def k1Tau0Of (fam : LargeEvenLieTag) (r : ℕ) : Bool :=
  match fam with
  | .A => decide (r ≥ 2)
  | .D => decide (r % 2 = 1)
  | .E6 => true
  | _ => false

@[expose] def k1LabelOf (fam : LargeEvenLieTag) (r tw nEff : ℕ) : GGKacOrbit :=
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

@[expose] def k1TagIdx : LargeEvenLieTag → ℕ
  | .A => 0 | .twA => 1 | .B => 2 | .C => 3 | .D => 4 | .twD => 5
  | .E6 => 6 | .E7 => 7 | .E8 => 8 | .F4 => 9 | .twE6 => 10 | .triD4 => 11
  | .G2 => 12 | .twB2 => 13 | .twF4 => 14 | .B2der => 15 | .G2der => 16 | .twF4der => 17

@[expose] def k1OrbitKey (o : GGKacOrbit) : List ℕ :=
  [k1TagIdx o.lab.tag, o.lab.rank, o.lab.n, if o.qs then 1 else 0]

@[expose] def k1DatumKey (D : GGKacDatum) : List (List ℕ) := D.orbits.map k1OrbitKey

structure K1Keyed where
  keys : List (List ℕ)
  rZ : ℕ
  stabΩ : ℕ
  datum : GGKacDatum

@[expose] def k1KeyedLe (a b : K1Keyed) : Bool :=
  if k1LexLtKey a.keys b.keys then true
  else if k1LexLtKey b.keys a.keys then false
  else if a.rZ < b.rZ then true
  else if b.rZ < a.rZ then false
  else decide (a.stabΩ ≤ b.stabΩ)

@[expose] def k1SortDatums (raw : List GGKacDatum) : List GGKacDatum :=
  (k1SortBy k1KeyedLe
    (raw.map (fun D => ⟨k1DatumKey D, D.rZ, D.stabΩ, D⟩))).map (fun k => k.datum)

@[expose] def k1NodeOrbit (rho : List ℕ) (i : ℕ) : List ℕ :=
  let rec go (f : ℕ) (cur : ℕ) (acc : List ℕ) : List ℕ :=
    match f with
    | 0 => acc
    | f + 1 =>
        if cur = i then acc else go f (rho.getD cur 0) (acc ++ [cur])
  go (rho.length + 1) (rho.getD i 0) [i]

@[expose] def k1NumRhoOrbits (rho : List ℕ) (removed : List ℕ) : ℕ :=
  let rec go (nodes seen : List ℕ) (count : ℕ) : ℕ :=
    match nodes with
    | [] => count
    | i :: rest =>
        if i ∈ seen then go rest seen count
        else go rest (seen ++ k1NodeOrbit rho i) (count + 1)
  go removed [] 0

@[expose] def k1CompOrbit (img : List ℕ → List ℕ) (fuel : ℕ) (c : List ℕ) : List (List ℕ) :=
  let rec go (f : ℕ) (cur : List ℕ) (acc : List (List ℕ)) : List (List ℕ) :=
    match f with
    | 0 => acc
    | f + 1 =>
        if cur = c then acc else go f (img cur) (acc ++ [cur])
  go fuel (img c) [c]

@[expose] def k1CompOrbits (img : List ℕ → List ℕ) (fuel : ℕ) (cs seen : List (List ℕ)) :
    List (List (List ℕ)) :=
  match cs with
  | [] => []
  | c :: rest =>
      if c ∈ seen then k1CompOrbits img fuel rest seen
      else
        let orb := k1CompOrbit img fuel c
        orb :: k1CompOrbits img fuel rest (seen ++ orb)

@[expose] def k1Datum (D : K1Diag) (s rho : List ℕ) (d n stabΩ : ℕ) : GGKacDatum :=
  let nNodes := D.marks.length
  let zero := (List.range nNodes).filter (fun i => decide (s.getD i 0 = 0))
  let comps := k1Comps D zero
  let img : List ℕ → List ℕ := fun c => k1SortNat (c.map (fun i => rho.getD i 0))
  let orbits := (k1CompOrbits img (nNodes + 1) comps []).map (fun orb =>
    let k := orb.length
    let c := orb.headD []
    let p := k1CompType D c
    let rk := k1pPow rho k
    let o := k1AutOrder c rk
    let tw := if d = 2 ∧ k % 2 = 1 ∧ k1Tau0Of p.1 p.2 then
                (if o = 1 then 2 else if o = 2 then 1 else o) else o
    k1LabelOf p.1 p.2 tw (k * n))
  let orbitsSorted := k1SortBy (fun a b => k1LexLtNat (k1OrbitKey a) (k1OrbitKey b)) orbits
  let removed := (List.range nNodes).filter (fun i => decide (s.getD i 0 > 0))
  ⟨orbitsSorted, k1NumRhoOrbits rho removed - 1, stabΩ⟩

@[expose] def k1Rho0 (D : K1Diag) (tw : Bool) (d : ℕ) : List ℕ :=
  let tau := if tw then D.tau else k1pId D.marks.length
  if d = 1 then tau else k1pMul D.tau0 tau

@[expose] def k1BaseAux (rho0 s : List ℕ) : List (List ℕ) → Option (List ℕ)
  | [] => none
  | a0 :: rest =>
      let r := k1pMul a0 rho0
      if k1pAct r s = s then some r else k1BaseAux rho0 s rest

@[expose] def k1KacBase (D : K1Diag) (rho0 s : List ℕ) : Option (List ℕ) :=
  k1BaseAux rho0 s D.omega

@[expose] def k1FormRepsAux (stab : List (List ℕ)) (base : List ℕ) (fuel : ℕ)
    (as seenF acc : List (List ℕ)) :
    List (List ℕ) :=
  match fuel with
  | 0 => acc
  | fuel + 1 =>
      match as with
      | [] => acc
      | a :: rest =>
          let rho := k1pMul a base
          if rho ∈ seenF then k1FormRepsAux stab base fuel rest seenF acc
          else
            let conj := stab.map (fun b => k1pMul b (k1pMul rho (k1pInv b)))
            k1FormRepsAux stab base fuel rest (seenF ++ conj) (acc ++ [rho])

@[expose] def k1FormReps (stab : List (List ℕ)) (base : List ℕ) : List (List ℕ) :=
  k1FormRepsAux stab base (stab.length + 1) stab [] []

@[expose] def k1OrbMin (D : K1Diag) (s : List ℕ) : List ℕ :=
  (k1SortBy k1LexLtNat (D.omega.map (fun a => k1pAct a s))).headD []

@[expose] def k1DatumsOf (D : K1Diag) (rho0 s : List ℕ) (d n : ℕ) : List GGKacDatum :=
  match k1KacBase D rho0 s with
  | none => []
  | some base =>
      let stab := D.omega.filter (fun a => decide (k1pAct a s = s))
      (k1FormReps stab base).map (fun rho => k1Datum D s rho d n stab.length)

@[expose] def k1RawDatums (D : K1Diag) (tw : Bool) (p n d : ℕ) : List GGKacDatum :=
  let rho0 := k1Rho0 D tw d
  ((k1VecsAux D.marks p).filter (fun s => decide (k1OrbMin D s = s))).foldr
    (fun s acc => k1DatumsOf D rho0 s d n ++ acc) []

@[expose] def ggKacTableCl (T : GGKacTypeCl) (tw : Bool) (p n : ℕ) : List GGKacDatum :=
  let D := k1DiagOf T
  let q := 2 ^ n
  if p ∣ q - 1 then k1SortDatums (k1RawDatums D tw p n 1)
  else if p ∣ q + 1 then k1SortDatums (k1RawDatums D tw p n 2)
  else []

@[expose] def ggKacTypeClOfLabel : LargeEvenLabel → Option (GGKacTypeCl × Bool × ℕ)
  | ⟨.A, r, n⟩ => some (.A r, false, n)
  | ⟨.twA, r, n⟩ => some (.A r, true, n)
  | ⟨.B, r, n⟩ => if 2 ≤ r then some (.C r, false, n) else none
  | ⟨.C, r, n⟩ => if 2 ≤ r then some (.C r, false, n) else none
  | ⟨.D, r, n⟩ =>
      if 4 ≤ r then some (.D r, false, n) else if r = 3 then some (.A 3, false, n) else none
  | ⟨.twD, r, n⟩ =>
      if 4 ≤ r then some (.D r, true, n) else if r = 3 then some (.A 3, true, n)
      else if r = 2 then some (.A 1, false, 2 * n) else none
  | _ => none

@[expose] def GGKacValidCl (lab : LargeEvenLabel) (p : ℕ) (D : GGKacDatum) : Prop :=
  ∃ T tw m, ggKacTypeClOfLabel lab = some (T, tw, m) ∧ D ∈ ggKacTableCl T tw p m

example : ggKacTableCl (.C 2) false 3 1 =
  [⟨[⟨⟨.A, 1, 1⟩, false⟩], 1, 1⟩,
  ⟨[⟨⟨.A, 1, 1⟩, false⟩], 1, 1⟩,
  ⟨[⟨⟨.B2der, 0, 1⟩, true⟩], 0, 1⟩] := by decide

example : ggKacTableCl (.C 3) false 3 1 =
  [⟨[⟨⟨.A, 1, 1⟩, false⟩, ⟨⟨.A, 1, 1⟩, false⟩], 1, 1⟩,
  ⟨[⟨⟨.twA, 2, 1⟩, false⟩], 1, 1⟩,
  ⟨[⟨⟨.C, 3, 1⟩, true⟩], 0, 1⟩,
  ⟨[⟨⟨.B2der, 0, 1⟩, true⟩], 1, 1⟩] := by decide

example : ggKacTableCl (.A 2) false 3 1 =
  [⟨[], 1, 3⟩,
  ⟨[⟨⟨.A, 2, 1⟩, true⟩], 0, 1⟩] := by decide

example : ggKacTableCl (.A 2) true 3 1 =
  [⟨[], 0, 3⟩,
  ⟨[], 0, 3⟩,
  ⟨[], 2, 3⟩,
  ⟨[⟨⟨.A, 1, 1⟩, false⟩], 1, 1⟩,
  ⟨[⟨⟨.A, 1, 1⟩, false⟩], 1, 1⟩,
  ⟨[⟨⟨.twA, 2, 1⟩, false⟩], 0, 1⟩] := by decide

example : ggKacTableCl (.A 5) false 3 1 =
  [⟨[⟨⟨.A, 1, 1⟩, false⟩, ⟨⟨.A, 1, 2⟩, true⟩], 1, 3⟩,
  ⟨[⟨⟨.A, 2, 2⟩, true⟩], 1, 1⟩,
  ⟨[⟨⟨.A, 3, 1⟩, true⟩], 1, 1⟩,
  ⟨[⟨⟨.A, 5, 1⟩, true⟩], 0, 1⟩] := by decide

example : ggKacTableCl (.A 3) false 5 4 =
  [⟨[], 3, 1⟩,
  ⟨[⟨⟨.A, 1, 4⟩, true⟩], 2, 1⟩,
  ⟨[⟨⟨.A, 1, 4⟩, true⟩], 2, 1⟩,
  ⟨[⟨⟨.A, 1, 4⟩, true⟩], 2, 1⟩,
  ⟨[⟨⟨.A, 1, 4⟩, true⟩], 2, 1⟩,
  ⟨[⟨⟨.A, 1, 4⟩, true⟩], 2, 1⟩,
  ⟨[⟨⟨.A, 1, 4⟩, true⟩], 2, 1⟩,
  ⟨[⟨⟨.A, 1, 4⟩, true⟩, ⟨⟨.A, 1, 4⟩, true⟩], 1, 1⟩,
  ⟨[⟨⟨.A, 1, 4⟩, true⟩, ⟨⟨.A, 1, 4⟩, true⟩], 1, 1⟩,
  ⟨[⟨⟨.A, 2, 4⟩, true⟩], 1, 1⟩,
  ⟨[⟨⟨.A, 2, 4⟩, true⟩], 1, 1⟩,
  ⟨[⟨⟨.A, 2, 4⟩, true⟩], 1, 1⟩,
  ⟨[⟨⟨.A, 2, 4⟩, true⟩], 1, 1⟩,
  ⟨[⟨⟨.A, 3, 4⟩, true⟩], 0, 1⟩] := by decide

example : ggKacTableCl (.D 4) false 3 1 =
  [⟨[⟨⟨.A, 1, 1⟩, false⟩, ⟨⟨.A, 1, 1⟩, false⟩, ⟨⟨.A, 1, 1⟩, false⟩], 1, 1⟩,
  ⟨[⟨⟨.twA, 2, 1⟩, false⟩], 2, 1⟩,
  ⟨[⟨⟨.twA, 3, 1⟩, true⟩], 1, 1⟩,
  ⟨[⟨⟨.twA, 3, 1⟩, true⟩], 1, 1⟩,
  ⟨[⟨⟨.twA, 3, 1⟩, true⟩], 1, 1⟩,
  ⟨[⟨⟨.D, 4, 1⟩, true⟩], 0, 1⟩] := by decide

example : ggKacTableCl (.D 4) true 3 1 =
  [⟨[⟨⟨.A, 1, 1⟩, false⟩, ⟨⟨.A, 1, 2⟩, true⟩], 1, 1⟩,
  ⟨[⟨⟨.A, 3, 1⟩, true⟩], 1, 1⟩,
  ⟨[⟨⟨.twA, 2, 1⟩, false⟩], 1, 1⟩,
  ⟨[⟨⟨.twD, 4, 1⟩, true⟩], 0, 1⟩] := by decide

example : ggKacTableCl (.D 5) true 5 2 =
  [⟨[⟨⟨.A, 1, 2⟩, true⟩, ⟨⟨.A, 1, 2⟩, true⟩], 3, 1⟩,
  ⟨[⟨⟨.A, 1, 2⟩, true⟩, ⟨⟨.A, 1, 2⟩, true⟩, ⟨⟨.A, 1, 2⟩, true⟩], 2, 1⟩,
  ⟨[⟨⟨.A, 1, 2⟩, true⟩, ⟨⟨.A, 1, 2⟩, true⟩, ⟨⟨.A, 1, 2⟩, true⟩], 2, 1⟩,
  ⟨[⟨⟨.A, 1, 2⟩, true⟩, ⟨⟨.A, 1, 2⟩, true⟩, ⟨⟨.twA, 2, 2⟩, true⟩], 1, 1⟩,
  ⟨[⟨⟨.A, 1, 2⟩, true⟩, ⟨⟨.A, 1, 2⟩, true⟩, ⟨⟨.twA, 2, 2⟩, true⟩], 1, 1⟩,
  ⟨[⟨⟨.A, 1, 2⟩, true⟩, ⟨⟨.twA, 2, 2⟩, true⟩], 2, 1⟩,
  ⟨[⟨⟨.A, 1, 2⟩, true⟩, ⟨⟨.twA, 2, 2⟩, true⟩], 2, 1⟩,
  ⟨[⟨⟨.A, 1, 2⟩, true⟩, ⟨⟨.twA, 2, 2⟩, true⟩], 2, 1⟩,
  ⟨[⟨⟨.A, 1, 2⟩, true⟩, ⟨⟨.twA, 2, 2⟩, true⟩], 2, 1⟩,
  ⟨[⟨⟨.A, 1, 2⟩, true⟩, ⟨⟨.twA, 3, 2⟩, true⟩], 1, 1⟩,
  ⟨[⟨⟨.A, 1, 2⟩, true⟩, ⟨⟨.twA, 3, 2⟩, true⟩], 1, 1⟩,
  ⟨[⟨⟨.twA, 2, 2⟩, true⟩], 3, 1⟩,
  ⟨[⟨⟨.twA, 2, 2⟩, true⟩], 3, 1⟩,
  ⟨[⟨⟨.twA, 3, 2⟩, true⟩], 2, 1⟩,
  ⟨[⟨⟨.twA, 3, 2⟩, true⟩], 2, 1⟩,
  ⟨[⟨⟨.twA, 3, 2⟩, true⟩], 2, 1⟩,
  ⟨[⟨⟨.twA, 3, 2⟩, true⟩], 2, 1⟩,
  ⟨[⟨⟨.twA, 3, 2⟩, true⟩], 2, 1⟩,
  ⟨[⟨⟨.twA, 3, 2⟩, true⟩], 2, 1⟩,
  ⟨[⟨⟨.twA, 3, 2⟩, true⟩], 2, 1⟩,
  ⟨[⟨⟨.twA, 4, 2⟩, true⟩], 1, 1⟩,
  ⟨[⟨⟨.twA, 4, 2⟩, true⟩], 1, 1⟩,
  ⟨[⟨⟨.twA, 4, 2⟩, true⟩], 1, 1⟩,
  ⟨[⟨⟨.twA, 4, 2⟩, true⟩], 1, 1⟩,
  ⟨[⟨⟨.D, 4, 2⟩, true⟩], 1, 1⟩,
  ⟨[⟨⟨.D, 4, 2⟩, true⟩], 1, 1⟩,
  ⟨[⟨⟨.twD, 5, 2⟩, true⟩], 0, 1⟩] := by decide

example : ggKacTableCl (.C 4) false 5 2 =
  [⟨[⟨⟨.A, 1, 2⟩, true⟩, ⟨⟨.A, 1, 2⟩, true⟩], 2, 1⟩,
  ⟨[⟨⟨.A, 1, 2⟩, true⟩, ⟨⟨.A, 1, 2⟩, true⟩], 2, 1⟩,
  ⟨[⟨⟨.A, 1, 2⟩, true⟩, ⟨⟨.A, 1, 2⟩, true⟩], 2, 1⟩,
  ⟨[⟨⟨.A, 1, 2⟩, true⟩, ⟨⟨.twA, 2, 2⟩, true⟩], 1, 1⟩,
  ⟨[⟨⟨.A, 1, 2⟩, true⟩, ⟨⟨.twA, 2, 2⟩, true⟩], 1, 1⟩,
  ⟨[⟨⟨.A, 1, 2⟩, true⟩, ⟨⟨.C, 2, 2⟩, true⟩], 1, 1⟩,
  ⟨[⟨⟨.A, 1, 2⟩, true⟩, ⟨⟨.C, 2, 2⟩, true⟩], 1, 1⟩,
  ⟨[⟨⟨.twA, 2, 2⟩, true⟩], 2, 1⟩,
  ⟨[⟨⟨.twA, 2, 2⟩, true⟩], 2, 1⟩,
  ⟨[⟨⟨.twA, 3, 2⟩, true⟩], 1, 1⟩,
  ⟨[⟨⟨.twA, 3, 2⟩, true⟩], 1, 1⟩,
  ⟨[⟨⟨.C, 2, 2⟩, true⟩], 2, 1⟩,
  ⟨[⟨⟨.C, 3, 2⟩, true⟩], 1, 1⟩,
  ⟨[⟨⟨.C, 3, 2⟩, true⟩], 1, 1⟩,
  ⟨[⟨⟨.C, 4, 2⟩, true⟩], 0, 1⟩] := by decide

end CFSG.StandardType

end

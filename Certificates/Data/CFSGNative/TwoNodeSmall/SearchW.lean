module

public import Certificates.Data.CFSGNative.TwoNodeSmall.Verify
public import Certificates.Data.CFSGNative.TwoNodeSmall.SearchO

public section

namespace CFSG.TwoNodeSmall

set_option compiler.extract_closed false

private def fzw_invMod (P : Pt) (a : Nat) : Nat :=
  ((List.range P.p).find? (fun x => x != 0 && (a * x) % P.p == 1)).getD 1

private def fzw_norm (P : Pt) (cb : Vec × Vec) : Vec × Vec :=
  match (List.range P.D).find? (fun i => cb.1.getD i 0 % P.p != 0) with
  | none => cb
  | some i =>
    let hi := cb.1.getD i 0 % P.p
    let iv := fzw_invMod P hi
    ((List.range P.D).map fun j => (cb.1.getD j 0 * iv) % P.p,
     (List.range P.D).map fun j => (cb.2.getD j 0 * hi) % P.p)

private def fzw_key (P : Pt) (cb : Vec × Vec) : Nat :=
  P.code cb.1 * (P.p ^ P.D) + P.code cb.2

private def fzw_conj (P : Pt) (s t : Vec × Vec) : Vec × Vec :=
  let a := P.dotv t.2 s.1
  let b := P.dotv s.2 t.1
  ((List.range P.D).map fun i => (t.1.getD i 0 + (P.p - (b * s.1.getD i 0) % P.p)) % P.p,
   (List.range P.D).map fun i => (t.2.getD i 0 + (P.p - (a * s.2.getD i 0) % P.p)) % P.p)

private structure fzw_R where
  cb : Vec × Vec
  psi : Word
  k : Nat

private structure fzw_E where
  cb : Vec × Vec
  w : Word
  i : Nat

private def fzw_mkR (P : Pt) (f h : Vec) (psi : Word) (k : Nat) : fzw_R :=
  { cb := fzw_norm P (h, f), psi := psi, k := k }

private def fzw_genRs (P : Pt) : List fzw_R :=
  P.gens.zipIdx.map fun p => fzw_mkR P p.1.f p.1.h [] p.2

private def fzw_conjR (P : Pt) (s t : fzw_R) : fzw_R :=
  { cb := fzw_norm P (fzw_conj P s.cb t.cb), psi := s.k :: t.psi, k := t.k }

private def fzw_insert (P : Pt) (seen : List fzw_R) (r : fzw_R) : List fzw_R :=
  if seen.any (fun s => fzw_key P s.cb == fzw_key P r.cb) then seen else seen ++ [r]

private def fzw_insertAll (P : Pt) (seen : List fzw_R) (rs : List fzw_R) : List fzw_R :=
  rs.foldl (fzw_insert P) seen

private def fzw_closureAux (P : Pt) (G : List fzw_R) :
    Nat → List fzw_R → List fzw_R → Option (List fzw_R)
  | 0, seen, _ => if seen.length > 150 then none else some seen
  | fuel + 1, seen, frontier =>
    if seen.length > 150 then none
    else if frontier.isEmpty then some seen
    else
      let cands := frontier.flatMap fun t => G.map fun s => fzw_conjR P s t
      let seen' := fzw_insertAll P seen cands
      fzw_closureAux P G fuel seen' (seen'.drop seen.length)

private def fzw_closure (P : Pt) : Option (List fzw_R) :=
  let G := fzw_genRs P
  let seen0 := fzw_insertAll P [] G
  fzw_closureAux P G 200 seen0 seen0

private def fzw_compat (P : Pt) (i j : Nat) (ri rj : fzw_R) : Bool :=
  let a := P.dotv ri.cb.2 rj.cb.1
  let b := P.dotv rj.cb.2 ri.cb.1
  if (e8M.getD i []).getD j 0 == 2 then a == 0 && b == 0
  else (a * b) % P.p == 1

private def fzw_okChoice (P : Pt) (i : Nat) (chosen : List (Nat × fzw_R))
    (r : fzw_R) : Bool :=
  P.dotv r.cb.2 r.cb.1 == 2 % P.p &&
  chosen.all fun p =>
    fzw_compat P i p.1 r p.2 && (fzw_key P r.cb != fzw_key P p.2.cb)

private def fzw_firstSome (f : fzw_R → Option (List (Nat × fzw_R))) :
    List fzw_R → Option (List (Nat × fzw_R))
  | [] => none
  | a :: as =>
    match f a with
    | some b => some b
    | none => fzw_firstSome f as

private def fzw_searchSys (P : Pt) (R : List fzw_R) :
    List Nat → List (Nat × fzw_R) → Option (List (Nat × fzw_R))
  | [], chosen => some chosen
  | i :: rest, chosen =>
    fzw_firstSome (fun r =>
      if fzw_okChoice P i chosen r then
        fzw_searchSys P R rest ((i, r) :: chosen)
      else none) R

private def fzw_order : List Nat := [0, 2, 3, 1, 4, 5, 6, 7]

private def fzw_findSys (P : Pt) (R : List fzw_R) : Option (List (Nat × fzw_R)) :=
  fzw_searchSys P R fzw_order []

private def fzw_sigmas (chosen : List (Nat × fzw_R)) : List fzw_R :=
  (List.range 8).map fun i =>
    match chosen.find? (fun p => p.1 == i) with
    | some p => p.2
    | none => { cb := ([], []), psi := [], k := 0 }

private def fzw_sigma (chosen : List (Nat × fzw_R)) : List (Word × Nat) :=
  (List.range 8).map fun i =>
    match chosen.find? (fun p => p.1 == i) with
    | some p => (p.2.psi, p.2.k)
    | none => ([], 0)

private def fzw_sAt (S : List fzw_R) (j : Nat) : fzw_R :=
  match S[j]? with
  | some r => r
  | none => { cb := ([], []), psi := [], k := 0 }

private def fzw_initE (S : List fzw_R) : List fzw_E :=
  S.zipIdx.map fun p => { cb := p.1.cb, w := [], i := p.2 }

private def fzw_conjE (P : Pt) (S : List fzw_R) (j : Nat) (e : fzw_E) : fzw_E :=
  { cb := fzw_norm P (fzw_conj P (fzw_sAt S j).cb e.cb), w := j :: e.w, i := e.i }

private def fzw_insertE (P : Pt) (seen : List fzw_E) (x : fzw_E) : List fzw_E :=
  if seen.any (fun y => fzw_key P y.cb == fzw_key P x.cb) then seen else seen ++ [x]

private def fzw_insertAllE (P : Pt) (seen : List fzw_E) (xs : List fzw_E) : List fzw_E :=
  xs.foldl (fzw_insertE P) seen

private def fzw_closureEAux (P : Pt) (S : List fzw_R) :
    Nat → List fzw_E → List fzw_E → List fzw_E
  | 0, seen, _ => seen
  | fuel + 1, seen, frontier =>
    if frontier.isEmpty then seen
    else
      let cands := frontier.flatMap fun e => (List.range 8).map fun j => fzw_conjE P S j e
      let seen' := fzw_insertAllE P seen cands
      fzw_closureEAux P S fuel seen' (seen'.drop seen.length)

private def fzw_closureE (P : Pt) (S : List fzw_R) : List fzw_E :=
  let init := fzw_initE S
  fzw_closureEAux P S 200 init init

private def fzw_exprsAux (P : Pt) (E : List fzw_E) :
    List fzw_R → Option (List Word)
  | [] => some []
  | r :: rs =>
    match E.find? (fun e => fzw_key P e.cb == fzw_key P r.cb) with
    | some e =>
      match fzw_exprsAux P E rs with
      | some ws => some ((e.w ++ [e.i] ++ e.w.reverse) :: ws)
      | none => none
    | none => none

private def fzw_exprs (P : Pt) (S : List fzw_R) : Option (List Word) :=
  fzw_exprsAux P (fzw_closureE P S) (fzw_genRs P)

private def fzw_refWord (r : fzw_R) : Word := r.psi ++ [r.k] ++ r.psi.reverse

private def fzw_refOrbit (P : Pt) (strong : List fzw_R) (v0 : Vec) : List (Vec × Nat × Nat) :=
  Id.run do
    let mut index : Array Nat := (List.replicate (P.p ^ P.D) 0).toArray
    let mut tree : Array (Vec × Nat × Nat) := #[]
    let mut queue : Array Vec := #[v0]
    index := index.set! (P.code v0) 1
    tree := tree.push (v0, 0, 0)
    let mut head := 0
    while head < queue.size do
      let v := queue[head]!
      for p in strong.zipIdx do
        let w := P.sigmaApply p.1.cb v
        let c := P.code w
        if index[c]! == 0 then
          index := index.set! c (tree.size + 1)
          tree := tree.push (w, head, p.2)
          queue := queue.push w
      head := head + 1
    return tree.toList

private def fzw_refChain (P : Pt) (R : List fzw_R) (target : Nat) : Option OWit :=
  let rec go (strong : List fzw_R) (prod : Nat) (acc : List Level) (fuel : Nat) : Option OWit :=
    match fuel with
    | 0 => none
    | fuel + 1 =>
      match (List.range P.D).find? (fun i => strong.any fun r => P.dotv r.cb.2 (P.unit i) != 0) with
      | none => none
      | some i =>
        let base := P.unit i
        let tree := fzw_refOrbit P strong base
        let level : Level := { base := base, strong := strong.map fzw_refWord, tree := tree }
        let prod' := prod * tree.length
        if prod' > target then some ⟨(level :: acc).reverse⟩
        else
          let strong' := strong.filter fun r => P.dotv r.cb.2 base == 0
          go strong' prod' (level :: acc) fuel
  go R 1 [] 64

def findW (P : Pt) : Option WWit :=
  match fzw_closure P with
  | none => none
  | some R =>
    match fzw_findSys P R with
    | none => none
    | some chosen =>
      match fzw_exprs P (fzw_sigmas chosen) with
      | none => none
      | some expr =>
        match fzw_refChain P R 696729599 with
        | none => none
        | some chain =>
          some { kind := 4, sigma := fzw_sigma chosen, expr := expr, chain := chain }

end CFSG.TwoNodeSmall

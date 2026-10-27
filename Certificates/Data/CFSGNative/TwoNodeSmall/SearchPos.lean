module

public import Certificates.Data.CFSGNative.TwoNodeSmall.VerifyPos
public import Certificates.Data.CFSGNative.TwoNodeSmall.SearchT
public import Certificates.Data.CFSGNative.TwoNodeSmall.SearchO
public import Certificates.Data.CFSGNative.TwoNodeSmall.SearchPosO

public section

namespace CFSG.TwoNodeSmall

set_option compiler.extract_closed false

private def fze_words (n : Nat) : Nat → List Word
  | 0 => [[]]
  | k + 1 => (fze_words n k).flatMap fun w => (List.range n).map fun i => i :: w

private def fze_wordsLE (n k : Nat) : List Word :=
  (List.range (k + 1)).flatMap (fze_words n)

private def fze_findC (Q : SPt) : Option CWit :=
  let P := Q.pt
  let ws := fze_wordsLE (P.nFrame + 1) 4
  let js := (List.range (P.nFrame - 2)).map (· + Q.s)
  let cands : List CWit :=
    js.flatMap fun j => js.flatMap fun j' =>
      if j = j' then [] else ws.map fun psi => { psi := psi, j := j, j' := j' }
  cands.find? (fun c => verifyC Q c)

private def fze_cycleWit (Q : SPt) : Option PWitness :=
  match fze_findC Q with
  | some c => if verifyExcl Q (.cycle c) then some (.cycle c) else none
  | none => none

private def fzp_invMod (P : Pt) (a : Nat) : Nat :=
  ((List.range P.p).find? (fun x => x != 0 && (a * x) % P.p == 1)).getD 1

private def fzp_norm (P : Pt) (cb : Vec × Vec) : Vec × Vec :=
  match (List.range P.D).find? (fun i => cb.1.getD i 0 % P.p != 0) with
  | none => cb
  | some i =>
    let hi := cb.1.getD i 0 % P.p
    let iv := fzp_invMod P hi
    ((List.range P.D).map fun j => (cb.1.getD j 0 * iv) % P.p,
     (List.range P.D).map fun j => (cb.2.getD j 0 * hi) % P.p)

private def fzp_key (P : Pt) (cb : Vec × Vec) : Nat :=
  P.code cb.1 * (P.p ^ P.D) + P.code cb.2

private def fzp_conj (P : Pt) (s t : Vec × Vec) : Vec × Vec :=
  let a := P.dotv t.2 s.1
  let b := P.dotv s.2 t.1
  ((List.range P.D).map fun i => (t.1.getD i 0 + (P.p - (b * s.1.getD i 0) % P.p)) % P.p,
   (List.range P.D).map fun i => (t.2.getD i 0 + (P.p - (a * s.2.getD i 0) % P.p)) % P.p)

private structure fzp_R where
  cb : Vec × Vec
  psi : Word
  k : Nat

private structure fzp_E where
  cb : Vec × Vec
  w : Word
  i : Nat

private def fzp_mkR (P : Pt) (f h : Vec) (psi : Word) (k : Nat) : fzp_R :=
  { cb := fzp_norm P (h, f), psi := psi, k := k }

private def fzp_genRs (P : Pt) : List fzp_R :=
  P.gens.zipIdx.map fun p => fzp_mkR P p.1.f p.1.h [] p.2

private def fzp_conjR (P : Pt) (s t : fzp_R) : fzp_R :=
  { cb := fzp_norm P (fzp_conj P s.cb t.cb), psi := s.k :: t.psi, k := t.k }

private def fzp_insert (P : Pt) (seen : List fzp_R) (r : fzp_R) : List fzp_R :=
  let kr := fzp_key P r.cb
  if seen.any (fun s => fzp_key P s.cb == kr) then seen else seen ++ [r]

private def fzp_insertAll (P : Pt) (seen : List fzp_R) : List fzp_R → List fzp_R
  | [] => seen
  | r :: rs => if seen.length > 64 then seen else fzp_insertAll P (fzp_insert P seen r) rs

private def fzp_closureAux (P : Pt) (cap : Nat) (G : List fzp_R) :
    Nat → List fzp_R → List fzp_R → Option (List fzp_R)
  | 0, seen, _ => if seen.length > cap then none else some seen
  | fuel + 1, seen, frontier =>
    if seen.length > cap then none
    else if frontier.isEmpty then some seen
    else
      let cands := frontier.flatMap fun t => G.map fun s => fzp_conjR P s t
      let seen' := fzp_insertAll P seen cands
      fzp_closureAux P cap G fuel seen' (seen'.drop seen.length)

private def fzp_closure (P : Pt) : Option (List fzp_R) :=
  let G := fzp_genRs P
  let seen0 := fzp_insertAll P [] G
  fzp_closureAux P 64 G 200 seen0 seen0

private def fzp_classOf (P : Pt) (cap : Nat) (j : Nat) : Option (List fzp_R) :=
  let G := fzp_genRs P
  match G[j]? with
  | none => none
  | some g => fzp_closureAux P cap G 200 [g] [g]

private def fzp_edgeMul (kind n i j : Nat) : Option Nat :=
  if kind = 0 then
    (if i + 1 == j || j + 1 == i then some 1 else none)
  else if kind = 1 then
    (if (i == n - 1 && j == n - 2) || (j == n - 1 && i == n - 2) then some 2
     else if i + 1 == j || j + 1 == i then some 1 else none)
  else if kind = 2 then
    (if (i + 1 == j && j + 2 < n) || (j + 1 == i && i + 2 < n) ||
        (i + 3 == n && (j + 2 == n || j + 1 == n)) ||
        (j + 3 == n && (i + 2 == n || i + 1 == n)) then some 1 else none)
  else
    (if (i == 0 && j == 2) || (i == 2 && j == 0) ||
        (i == 1 && j == 3) || (i == 3 && j == 1) ||
        (i == 2 && j == 3) || (i == 3 && j == 2) ||
        (i == 3 && j == 4) || (i == 4 && j == 3) ||
        (i == 4 && j == 5) || (i == 5 && j == 4) ||
        (i == 5 && j == 6) || (i == 6 && j == 5) then some 1 else none)

private def fzp_compat (P : Pt) (kind : Nat) (i j : Nat) (ri rj : fzp_R) : Bool :=
  let a := P.dotv ri.cb.2 rj.cb.1
  let b := P.dotv rj.cb.2 ri.cb.1
  match fzp_edgeMul kind P.D i j with
  | some m => (a * b) % P.p == m
  | none => a == 0 && b == 0

private def fzp_okChoice (P : Pt) (kind : Nat) (i : Nat) (chosen : List (Nat × fzp_R))
    (r : fzp_R) : Bool :=
  P.dotv r.cb.2 r.cb.1 == 2 % P.p &&
  chosen.all fun p =>
    fzp_compat P kind i p.1 r p.2 && (fzp_key P r.cb != fzp_key P p.2.cb)

private def fzp_firstSome (f : fzp_R → Option (List (Nat × fzp_R))) :
    List fzp_R → Option (List (Nat × fzp_R))
  | [] => none
  | a :: as =>
    match f a with
    | some b => some b
    | none => fzp_firstSome f as

private def fzp_searchSys (P : Pt) (kind : Nat) (R : List fzp_R) :
    List Nat → List (Nat × fzp_R) → Option (List (Nat × fzp_R))
  | [], chosen => some chosen
  | i :: rest, chosen =>
    fzp_firstSome (fun r =>
      if fzp_okChoice P kind i chosen r then
        fzp_searchSys P kind R rest ((i, r) :: chosen)
      else none) R

private def fzp_order (kind n : Nat) : List Nat :=
  if kind = 3 then [0, 2, 3, 1, 4, 5, 6] else List.range n

private def fzp_sigmas (n : Nat) (chosen : List (Nat × fzp_R)) : List fzp_R :=
  (List.range n).map fun i =>
    match chosen.find? (fun p => p.1 == i) with
    | some p => p.2
    | none => { cb := ([], []), psi := [], k := 0 }

private def fzp_sigma (n : Nat) (chosen : List (Nat × fzp_R)) : List (Word × Nat) :=
  (List.range n).map fun i =>
    match chosen.find? (fun p => p.1 == i) with
    | some p => (p.2.psi, p.2.k)
    | none => ([], 0)

private def fzp_sAt (S : List fzp_R) (j : Nat) : fzp_R :=
  match S[j]? with
  | some r => r
  | none => { cb := ([], []), psi := [], k := 0 }

private def fzp_initE (S : List fzp_R) : List fzp_E :=
  S.zipIdx.map fun p => { cb := p.1.cb, w := [], i := p.2 }

private def fzp_conjE (P : Pt) (S : List fzp_R) (j : Nat) (e : fzp_E) : fzp_E :=
  { cb := fzp_norm P (fzp_conj P (fzp_sAt S j).cb e.cb), w := j :: e.w, i := e.i }

private def fzp_insertE (P : Pt) (seen : List fzp_E) (x : fzp_E) : List fzp_E :=
  if seen.any (fun y => fzp_key P y.cb == fzp_key P x.cb) then seen else seen ++ [x]

private def fzp_insertAllE (P : Pt) (seen : List fzp_E) (xs : List fzp_E) : List fzp_E :=
  xs.foldl (fzp_insertE P) seen

private def fzp_closureEAux (P : Pt) (S : List fzp_R) (n : Nat) :
    Nat → List fzp_E → List fzp_E → List fzp_E
  | 0, seen, _ => seen
  | fuel + 1, seen, frontier =>
    if frontier.isEmpty then seen
    else
      let cands := frontier.flatMap fun e => (List.range n).map fun j => fzp_conjE P S j e
      let seen' := fzp_insertAllE P seen cands
      fzp_closureEAux P S n fuel seen' (seen'.drop seen.length)

private def fzp_closureE (P : Pt) (S : List fzp_R) : List fzp_E :=
  let n := P.D
  let init := fzp_initE S
  fzp_closureEAux P S n 200 init init

private def fzp_exprsAux (P : Pt) (E : List fzp_E) :
    List fzp_R → Option (List Word)
  | [] => some []
  | r :: rs =>
    match E.find? (fun e => fzp_key P e.cb == fzp_key P r.cb) with
    | some e =>
      match fzp_exprsAux P E rs with
      | some ws => some ((e.w ++ [e.i] ++ e.w.reverse) :: ws)
      | none => none
    | none => none

private def fzp_exprs (P : Pt) (S : List fzp_R) : Option (List Word) :=
  fzp_exprsAux P (fzp_closureE P S) (fzp_genRs P)

private def fzp_refWord (r : fzp_R) : Word := r.psi ++ [r.k] ++ r.psi.reverse

private def fzp_refOrbit (P : Pt) (strong : List fzp_R) (v0 : Vec) : List (Vec × Nat × Nat) :=
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

private def fzp_refChain (P : Pt) (R : List fzp_R) (target : Nat) : Option OWit :=
  let rec go (strong : List fzp_R) (prod : Nat) (acc : List Level) (fuel : Nat) : Option OWit :=
    match fuel with
    | 0 => none
    | fuel + 1 =>
      match (List.range P.D).find? (fun i => strong.any fun r => P.dotv r.cb.2 (P.unit i) != 0) with
      | none => none
      | some i =>
        let base := P.unit i
        let tree := fzp_refOrbit P strong base
        let level : Level := { base := base, strong := strong.map fzp_refWord, tree := tree }
        let prod' := prod * tree.length
        if prod' > target then some ⟨(level :: acc).reverse⟩
        else
          let strong' := strong.filter fun r => P.dotv r.cb.2 base == 0
          go strong' prod' (level :: acc) fuel
  go R 1 [] 64

private def fzp_orderOf (kind n : Nat) : Nat :=
  if kind = 0 then natFact (n + 1)
  else if kind = 1 then 2 ^ n * natFact n
  else if kind = 2 then 2 ^ (n - 1) * natFact n
  else 2903040

private def fzp_tryKind (P : Pt) (kind : Nat) (R : List fzp_R) : Option WWit :=
  let n := P.D
  match fzp_searchSys P kind R (fzp_order kind n) [] with
  | none => none
  | some chosen =>
    let S := fzp_sigmas n chosen
    match fzp_exprs P S with
    | none => none
    | some expr =>
      match fzp_refChain P R (fzp_orderOf kind n - 1) with
      | none => none
      | some chain => some { kind := kind, sigma := fzp_sigma n chosen, expr := expr, chain := chain }

private def fzp_kindOf (n m : Nat) : Option Nat :=
  if m = n * (n + 1) / 2 then some 0
  else if m = n * (n - 1) then some 2
  else if m = n * n then some 1
  else if m = 63 && n = 7 then some 3
  else none

private def fzp_pairMat (P : Pt) (R : List fzp_R) : Array (Array Nat) :=
  let Ra := R.toArray
  Ra.map fun ri => Ra.map fun rj => P.dotv ri.cb.2 rj.cb.1 % P.p

private def fzp_pairOK (P : Pt) (kind : Nat) (R : List fzp_R) : Bool :=
  let A := fzp_pairMat P R
  let n := A.size
  let pr (i j : Nat) : Nat := (A.getD i #[]).getD j 0
  (List.range n).all (fun i => (List.range n).all fun j =>
    i == j || (((pr i j == 0) == (pr j i == 0)) &&
      (let m := (pr i j * pr j i) % P.p; m == 0 || m == 1 || (kind == 1 && m == 2)))) &&
  (List.range n).all (fun i => (List.range n).all fun j => (List.range n).all fun k =>
    !(i < j && j < k) || pr i j == 0 || pr j k == 0 || pr k i == 0 ||
      (pr i j * pr j k * pr k i) % P.p == (pr j i * pr k j * pr i k) % P.p)

private def fzp_weylOf (P : Pt) (R : List fzp_R) : Option WWit :=
  match fzp_kindOf P.D R.length with
  | none => none
  | some k => if fzp_pairOK P k R then fzp_tryKind P k R else none

private def fzp_findCClass (Q : SPt) : Option CWit :=
  let P := Q.pt
  let js := (List.range (P.nFrame - 2)).map (· + Q.s)
  js.findSome? fun j =>
    match fzp_classOf P 2000 j with
    | none => none
    | some cls =>
      cls.findSome? fun t => js.findSome? fun j' =>
        if j == j' then none
        else
          let c : CWit := { psi := t.psi, j := j, j' := j' }
          if verifyC Q c then some c else none

private def fzp_cycleWit (Q : SPt) : Option PWitness :=
  if 5 ≤ Q.pt.p then
    (match fzp_findCClass Q <|> fze_findC Q with
     | some c => if verifyPos Q (.cycle c) then some (.cycle c) else none
     | none => none)
  else none

private def fzp_orderWit (Q : SPt) : Option PWitness :=
  let cut := 100000 < Q.pt.p ^ Q.pt.D
  let cap := if cut then 3000 else 1000000000
  let samples := if cut then 16 else 40
  (List.range 9).findSome? fun k =>
    match findOCap { Q.pt with x := Q.pt.x ++ List.replicate k 1 } Q.pt.bound cap samples with
    | some o => if verifyPos Q (.order o) then some (.order o) else none
    | none => none

private def fzp_weylWit (Q : SPt) (R : List fzp_R) : Option PWitness :=
  match fzp_weylOf Q.pt R with
  | some c => if verifyPos Q (.weyl c) then some (.weyl c) else none
  | none => none

def findPos (Q : SPt) : Option PWitness :=
  (if verifyPos Q .fixed then some .fixed else none) <|>
  (match findT Q.pt with
    | some t => if verifyPos Q (.transv t) then some (.transv t) else none
    | none => none) <|>
  (match fzp_closure Q.pt with
   | some R => fzp_weylWit Q R <|> fzp_cycleWit Q <|> fzp_orderWit Q
   | none => fzp_orderWit Q <|> fzp_cycleWit Q)

def findExcl (Q : SPt) : Option PWitness :=
  if verifyExcl Q .fixed then some .fixed
  else if verifyExcl Q .self_ then some .self_
  else match findT Q.pt with
    | some t => if verifyExcl Q (.transv t) then some (.transv t) else fze_cycleWit Q
    | none => fze_cycleWit Q

end CFSG.TwoNodeSmall

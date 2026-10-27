module

public import Certificates.Data.Kernel.E6Syl3

public section

namespace CFSG.KC.E6Syl3

@[expose] def wordG (gw : List (List ℕ)) (ks : List ℕ) : List ℕ :=
  ks.foldr (fun k t => wordT (gw.getD k []) t) (List.range 6)

@[expose] def wdOK (gw : List (List ℕ)) (Q : List (List ℕ)) (wd : List (List ℕ)) : Bool :=
  Q.getD 0 [] == List.range 6 && wd.all (fun ks => ks.all fun k => decide (k < 4)) &&
    (List.range 81).all fun i => wordG gw (wd.getD i []) == Q.getD i []

@[expose] def ltAt (lt : List (List ℕ)) (k i : ℕ) : ℕ := (lt.getD k []).getD i 0

@[expose] def ltOK (gw : List (List ℕ)) (Q : List (List ℕ)) (lt : List (List ℕ)) : Bool :=
  (List.range 4).all fun k => (List.range 81).all fun i =>
    decide (ltAt lt k i < 81) && wordT (gw.getD k []) (Q.getD i []) == Q.getD (ltAt lt k i) []

@[expose] def mulI (lt wd : List (List ℕ)) (i j : ℕ) : ℕ :=
  (wd.getD i []).foldr (fun k x => ltAt lt k x) j

@[expose] def powI (lt wd : List (List ℕ)) (i : ℕ) : ℕ → ℕ
  | 0 => 0
  | n + 1 => mulI lt wd (powI lt wd i n) i

@[expose] def ord3 (lt wd : List (List ℕ)) (i : ℕ) : Bool := i != 0 && powI lt wd i 3 == 0

@[expose] def o3OK (lt wd : List (List ℕ)) (o3 : List ℕ) : Bool :=
  (List.range 81).all (fun i => o3.contains i == ord3 lt wd i) && o3.all fun i => decide (i < 81)

@[expose] def commI (lt wd : List (List ℕ)) (i j : ℕ) : Bool := mulI lt wd i j == mulI lt wd j i

@[expose] def gEl (lt wd : List (List ℕ)) (i j a b : ℕ) : ℕ :=
  mulI lt wd (powI lt wd i a) (powI lt wd j b)

@[expose] def is3A2 (kw : List (List ℕ)) (x : ℕ) : Bool := kw.getD x [] == [1]

@[expose] def is2A2 (kw : List (List ℕ)) (x : ℕ) : Bool :=
  match kw.getD x [] with
  | [3, _, _, _, _] => true
  | _ => false

@[expose] def has3 (kw lt wd : List (List ℕ)) (i j : ℕ) : Bool :=
  (List.range 3).any fun a => (List.range 3).any fun b => is3A2 kw (gEl lt wd i j a b)

@[expose] def has3k (kw lt wd : List (List ℕ)) (i j k : ℕ) : Bool :=
  (List.range 3).any fun a => (List.range 3).any fun b => (List.range 3).any fun c =>
    is3A2 kw (mulI lt wd (gEl lt wd i j a b) (powI lt wd k c))

@[expose] def outG (lt wd : List (List ℕ)) (i j k : ℕ) : Bool :=
  (List.range 3).all fun a => (List.range 3).all fun b => gEl lt wd i j a b != k

@[expose] def badOK (Q kw lt wd : List (List ℕ)) (o3 : List ℕ) (i j : ℕ) (e : List ℕ) : Bool :=
  match e with
  | [i', j', r, a, b, c, d] =>
    i' == i && j' == j && decide (r < 72) && actV (Q.getD i []) (rvL r) == rvL r &&
      actV (Q.getD j []) (rvL r) == rvL r && (a * d + 2 * (b * c)) % 3 != 0 &&
      is2A2 kw (gEl lt wd i j a b) && is2A2 kw (gEl lt wd i j c d) &&
      o3.all fun k => !(commI lt wd i k && commI lt wd j k && outG lt wd i j k) || has3k kw lt wd i j k
  | _ => false

@[expose] def pairOK (Q kw lt wd : List (List ℕ)) (o3 : List ℕ) (bw : List (List ℕ))
    (i j : ℕ) : Bool :=
  !(commI lt wd i j && j != i && j != powI lt wd i 2) || has3 kw lt wd i j ||
    bw.any (badOK Q kw lt wd o3 i j)

@[expose] def pairsCheck (Q kw lt wd : List (List ℕ)) (o3 : List ℕ) (bw : List (List ℕ)) : Bool :=
  o3.all fun i => o3.all fun j => pairOK Q kw lt wd o3 bw i j

end CFSG.KC.E6Syl3

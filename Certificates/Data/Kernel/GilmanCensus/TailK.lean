module

public import Certificates.Data.Kernel.GilmanCensus.MkDataK

public section

namespace Certificates.GilmanCensusK

@[expose] def distinctK : List (List Int) → Bool
  | [] => true
  | x :: xs => !(xs.contains x) && distinctK xs

@[expose] def gramOkK (dk : DK) (Bl : List (List Int)) : Bool :=
  (List.range dk.N).all fun i => (List.range dk.N).all fun j =>
    gramK Bl ((toI dk.R).getD i []) ((toI dk.R).getD j []) == gI dk i j

@[expose] def lanesOkK (dk : DK) (rows : List (List Nat)) : Bool :=
  (List.range dk.N).all fun i => (List.range 128).all fun j =>
    (dk.reflP.getD i 0 >>> (7 * j)) % 128 == (rows.getD i []).getD j 0

@[expose] def tailOkK (dk : DK) (n : Nat) (Bl : List (List Int)) : Bool :=
  distinctK (toI dk.R) && dk.R.all (fun r => r.length == n) && dk.R.length == dk.N &&
    decide (dk.N < 128) && distinctK (toI dk.AR) && dk.AR.all (fun r => r.length == n) &&
    decide (dk.AR.length < 128) && dk.F.all (fun r => r.length == dk.d) && dk.F.length == dk.N &&
    dk.H.all (fun r => r.length == dk.d) && dk.H.length == dk.N &&
    dk.F.all (fun f => f.any (· != 0)) &&
    (dedupK (dk.H.flatMap fun h => [h.map fun x => x * 1 % 3, h.map fun x => x * 2 % 3])).length ==
      2 * dk.N &&
    gramOkK dk Bl && fhOkK dk.F dk.H (gI dk) dk.N true && adjK (gI dk) dk.N == dk.adj &&
    adjK (fun i j => gramK Bl ((toI dk.AR).getD i []) ((toI dk.AR).getD j [])) dk.AR.length ==
      dk.aadj &&
    (reflK (toI dk.R) (gI dk) n dk.N true).1 &&
    lanesOkK dk (reflK (toI dk.R) (gI dk) n dk.N true).2 && linesK dk.d == dk.lines

@[expose] def bK (A : List (List Int)) (sc : List Int) (n : Nat) : List (List Int) :=
  (List.range n).map fun i => (List.range n).map fun j => (A.getD i []).getD j 0 * sc.getD j 0

@[expose] def emb3K (A : List (List Int)) (n : Nat) : List (List Nat) :=
  (List.range n).foldl (fun e i =>
    let c := (List.range n).map fun j => imod3K ((A.getD j []).getD i 0)
    if rank3K (e ++ [c]) n > e.length then e ++ [c] else e) []

@[expose] def modeOkK (dk : DK) (m n : Nat) (A : List (List Int)) (sc : List Int)
    (emb : List (List Nat)) : Bool :=
  dk.mode == m && dk.R == dk.AR && dk.absidx == (List.range dk.AR.length).map (fun i => [i]) &&
    dk.rho == List.range n && emb.length == dk.d &&
    (toI dk.AR).foldl (fhStepK m n A (bK A sc n) sc emb) (true, [], []) == (true, dk.F, dk.H)

end Certificates.GilmanCensusK

end

module

public import Certificates.Data.Kernel.GilmanCensus.MkDataK

public section

namespace Certificates.GilmanCensusK

@[expose] def rrK (rho : List Nat) (n : Nat) (r : List Int) : List Int :=
  (List.range n).map fun j => r.getD j 0 + r.getD (rho.getD j 0) 0

@[expose] def relFK (n : Nat) (A : List (List Int)) (r : List Int) (v : List Nat) : Nat :=
  imod3K ((List.range' 0 n).foldl (fun t i => (List.range' 0 n).foldl
    (fun t j => t + r.getD i 0 * (A.getD i []).getD j 0 * ((v.getD j 0 : Nat) : Int)) t) 0)

@[expose] def relEmbK : List (List Nat) :=
  [[1, 0, 0, 0, 0, 1], [0, 0, 1, 0, 1, 0], [0, 1, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0]]

@[expose] def relHK (AR : List (List Int)) (rr : List Int) (grp : List Nat) : List Nat :=
  let hv := if grp.length == 2 then rr else AR.getD (grp.getD 0 0) []
  [imod3K (hv.getD 0 0), imod3K (hv.getD 2 0), imod3K (hv.getD 1 0), imod3K (hv.getD 3 0)]

@[expose] def mode1OkK (dk : DK) (n : Nat) (A : List (List Int)) : Bool :=
  let keys := (toI dk.AR).map (rrK dk.rho n)
  dk.mode == 1 && dk.rho == [5, 1, 4, 3, 2, 0] && dk.d == 4 && toI dk.R == dedupK keys &&
    dk.absidx == (toI dk.R).map (fun rr => idxsK rr keys 0) &&
    dk.F == (toI dk.R).map (fun rr =>
      relEmbK.map (relFK n A ((toI dk.AR).getD ((idxsK rr keys 0).getD 0 0) []))) &&
    dk.H == (toI dk.R).map (fun rr => relHK (toI dk.AR) rr (idxsK rr keys 0))

end Certificates.GilmanCensusK

end

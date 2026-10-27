module

public import CFSG.HardMathSupport.Timmesfeld.CrossChar.E6ThreeCharData

public section

namespace CFSG.KC.E6RegPair

open CFSG.Blueprint.Chevalley CFSG.HardMathSupport.Timmesfeld.Steinberg
  CFSG.HardMathSupport.Timmesfeld.CrossChar

@[expose] def r7 : List ℕ := [0, 0, 0, 1, 0, 0]

@[expose] def c0 : List ℕ := [1, 1, 1, 0, 1, 1]

@[expose] def killsL (T : RootTables) (b : List ℕ) (k : ℕ) : Bool :=
  decide (dotL (T.vecs.getD k []) (b.map fun x : ℕ => (x : ℤ)) % 3 = 0)

@[expose] def rowAux (T : RootTables) (rep : List ℕ) (is7 : Bool) (pidx : List ℕ) :
    ℕ → List ℕ → Bool
  | _, [] => true
  | n, k :: ks =>
    ((decide (k < 72) && killsL T rep k && killsL T (digits3 .E6 n) k) ||
        (is7 && pidx.contains n)) &&
      rowAux T rep is7 pidx (n + 1) ks

@[expose] def rowOK (rows : List (List ℕ)) (ps : List (ℕ × List ℕ)) (ρ : ℕ) : Bool :=
  decide ((rows.getD ρ []).length = 729) &&
    rowAux (RootTables.ofCert e6Certificate) (e6ThreeReps.getD ρ []) (ρ == 7) (ps.map Prod.fst) 0
      (rows.getD ρ [])

@[expose] def partnerOK (p : ℕ × List ℕ) : Bool :=
  decide (p.1 < 729) && p.2.all (fun i => decide (i < 6)) &&
    actL (negCartanRows .E6) p.2 r7 == r7 && actL (negCartanRows .E6) p.2 (digits3 .E6 p.1) == c0

@[expose] def partnersOK (ps : List (ℕ × List ℕ)) : Bool :=
  decide (ps.length = 24) && ps.all partnerOK && decide (ps.map Prod.fst).Nodup

@[expose] def tupleOfWord (T : RootTables) (w : List ℕ) : List ℕ :=
  w.foldr (imgL T) (List.range 6)

@[expose] def fixesL (t : List ℕ) (k : ℕ) : Bool :=
  decide (k < 72) &&
    (List.ofFn (e6Certificate.tupleVec t (e6Certificate.root k)) == List.ofFn (e6Certificate.root k))

@[expose] def stabEntryOK (T : RootTables) (e : ℕ × List ℕ) : Bool :=
  e.2.all (fun i => decide (i < 6)) && actL (negCartanRows .E6) e.2 r7 == r7 &&
    actL (negCartanRows .E6) e.2 c0 == c0 &&
    (decide (triPairing (vec3 (τ := .E6) r7) (e6ShiftT e6Certificate (tupleOfWord T e.2)) = 0) ||
      fixesL (tupleOfWord T e.2) e.1)

@[expose] def stabOKWith (T : RootTables) (es : List (ℕ × List ℕ)) : Bool :=
  decide (es.length = 27) && es.all (stabEntryOK T) &&
    decide (es.map fun e => (tupleOfWord T e.2).map fun k => T.vecs.getD k []).Nodup

@[expose] def stabOK (es : List (ℕ × List ℕ)) : Bool :=
  stabOKWith (RootTables.ofCert e6Certificate) es

@[expose] def idx7 : ℕ → List ℕ → List ℕ
  | _, [] => []
  | m, e :: es => if entryRep e == 7 then m :: idx7 (m + 1) es else idx7 (m + 1) es

@[expose] def orbit7OK (_ : Unit := ()) : Bool :=
  (idx7 0 e6ThreeOrbit).length == 80 && decide (idx7 0 e6ThreeOrbit).Nodup

end CFSG.KC.E6RegPair

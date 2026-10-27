module

public import Certificates.Data.CFSGNative.Chevalley.C2E6StdMatrix

public section

namespace CFSG.Monster.Existence.StdOdd.CertNative

open CFSG.LieType.Chevalley.C2E6Std.MatrixModel.Native

abbrev Letter : Type := Nat × Bool × Bool

@[expose] def letterMat (codes bits : Nat) (l : Letter) : Mat :=
  rootMat codes bits (6 + l.1) l.2.1 l.2.2

@[expose] def wordMat (codes bits : Nat) (w : List Letter) : Mat :=
  w.foldl (fun acc l => mul acc (letterMat codes bits l)) one

@[expose] def twistLetter (gam : List Nat) (l : Letter) : Letter :=
  (gam.getD l.1 0, xor l.2.1 l.2.2, l.2.2)

@[expose] def fixedOK (codes bits : Nat) (gam : List Nat) (ws : List (List Letter)) : Bool :=
  ws.all fun w => eqM (wordMat codes bits (w.map (twistLetter gam))) (wordMat codes bits w)

@[expose] def diagMat (es : List Nat) : Mat :=
  (List.range 78).toArray.map fun l =>
    match es.getD l 0 % 3 with
    | 0 => (1 <<< l, 0)
    | 1 => (0, 1 <<< l)
    | _ => (1 <<< l, 1 <<< l)

@[expose] def torusOK (codes bits : Nat) (hs : List (List Letter)) (es : List (List Nat)) : Bool :=
  (List.range hs.length).all fun j =>
    eqM (wordMat codes bits (hs.getD j [])) (diagMat (es.getD j []))

@[expose] def psiMat (E : List Mat) (ns : List Nat) : Mat :=
  mul (mul (mul (mul (pow (E.getD 0 one) (ns.getD 0 0)) (pow (E.getD 1 one) (ns.getD 1 0)))
    (pow (E.getD 2 one) (ns.getD 2 0))) (pow (E.getD 3 one) (ns.getD 3 0)))
    (pow (E.getD 4 one) (ns.getD 4 0))

@[expose] def conjOK (codes bits : Nat) (rs es : List (List Letter)) (cols : List (List Nat)) :
    Bool :=
  let R := rs.map (wordMat codes bits)
  let E := es.map (wordMat codes bits)
  (List.range 6).all fun i => (List.range 5).all fun j =>
    eqM (mul (R.getD i one) (E.getD j one))
      (mul (psiMat E (cols.getD (5 * i + j) [])) (R.getD i one))

@[expose] def splitOK (codes bits : Nat) (rs : List (List Letter)) (tAi tBi : List Nat)
    (pw : List (List Nat)) (ra rb : List Nat) : Bool :=
  let R := (rs.map (wordMat codes bits)).toArray
  let tA := lineProd R tAi
  let tB := lineProd R tBi
  let W := pw.map (lineProd #[tA, tB])
  eqM (pow tA 3) one && eqM (pow tB 3) one &&
    (List.range 81).all fun j =>
      eqM (mul (W.getD j one) tA) (W.getD (ra.getD j 0) one) &&
        eqM (mul (W.getD j one) tB) (W.getD (rb.getD j 0) one)

end CFSG.Monster.Existence.StdOdd.CertNative

module

public import Certificates.Data.Kernel.YoshQ.TabN
public import Certificates.Data.GH74.Ivk8Two

public section

namespace CFSG.KC.Ivk8N

open CFSG.KC.Enum CFSG.KC.YoshQ Certificates.Ivk8Two

@[expose] noncomputable def evalN (n w : Nat) (gs gis : List Nat) : List Int → Nat
  | [] => pidn n w
  | z :: wd =>
    pmN n w (if 0 < z then gs.getD (z.toNat - 1) (pidn n w) else gis.getD ((-z).toNat - 1) (pidn n w))
      (evalN n w gs gis wd)

@[expose] noncomputable def subprodsN (n w : Nat) : List Nat → List Nat
  | [] => [pidn n w]
  | t :: ts => subprodsN n w ts ++ (subprodsN n w ts).map (pmN n w t)

@[expose] noncomputable def allDistinctN (n w : Nat) : List Nat → Bool
  | [] => true
  | t :: ts => ts.all (fun s => !eqN n w t s) && allDistinctN n w ts

@[expose] noncomputable def invOKN (n w x : Nat) : Bool := eqN n w (pmN n w (invN n w x) x) (pidn n w)

@[expose] noncomputable def twoTablesN (n w : Nat) (gs : List Nat) (wa w₁ w₂ w₃ wx wy : List Int) :
    List Nat :=
  [evalN n w gs (gs.map (invN n w)) wa, evalN n w gs (gs.map (invN n w)) w₁,
    evalN n w gs (gs.map (invN n w)) w₂, evalN n w gs (gs.map (invN n w)) w₃,
    evalN n w gs (gs.map (invN n w)) wx, evalN n w gs (gs.map (invN n w)) wy]

@[expose] noncomputable def twoProdsN (n w : Nat) (ts : List Nat) : List Nat :=
  (w8Words.map (evalN n w ts (ts.map (invN n w)))).flatMap fun x =>
    (subprodsN n w (ts.take 4)).map (pmN n w x)

@[expose] noncomputable def twoOKN (n w : Nat) (gs : List Nat) (wa w₁ w₂ w₃ wx wy : List Int) :
    Bool :=
  gs.all (invOKN n w) && (twoTablesN n w gs wa w₁ w₂ w₃ wx wy).all (invOKN n w) &&
    dataRels.all (fun r =>
      eqN n w (evalN n w (twoTablesN n w gs wa w₁ w₂ w₃ wx wy)
          ((twoTablesN n w gs wa w₁ w₂ w₃ wx wy).map (invN n w)) r.1)
        (evalN n w (twoTablesN n w gs wa w₁ w₂ w₃ wx wy)
          ((twoTablesN n w gs wa w₁ w₂ w₃ wx wy).map (invN n w)) r.2)) &&
    !eqN n w ((twoTablesN n w gs wa w₁ w₂ w₃ wx wy).headD (pidn n w)) (pidn n w) &&
    (twoProdsN n w (twoTablesN n w gs wa w₁ w₂ w₃ wx wy)).length == 128 &&
    allDistinctN n w (twoProdsN n w (twoTablesN n w gs wa w₁ w₂ w₃ wx wy))

end CFSG.KC.Ivk8N

end

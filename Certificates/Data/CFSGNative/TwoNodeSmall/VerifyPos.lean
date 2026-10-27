module

public import Certificates.Data.CFSGNative.TwoNodeSmall.Verify
public import Certificates.Data.CFSGNative.TwoNodeSmall.CorePos

public section

namespace CFSG.TwoNodeSmall

set_option compiler.extract_closed false

@[expose] def verifyF (P : Pt) : Bool := P.dotv P.lastRefl.f P.x == 0

@[expose] def verifyS (P : Pt) : Bool := !(wfCheck P)

@[expose] def verifyC (Q : SPt) (c : CWit) : Bool :=
  let P := Q.pt
  let w := c.psi ++ [c.j] ++ c.psi.reverse
  let ht := P.applyWord c.psi (P.hK c.j)
  let a1 := P.alphaK c.j (P.hK c.j')
  let a2 := P.alphaK c.j' ht
  let a3 := P.alphaK c.j (P.applyWord c.psi.reverse (P.hK c.j))
  let b1 := P.alphaK c.j' (P.hK c.j)
  let b2 := P.alphaK c.j (P.applyWord c.psi.reverse (P.hK c.j'))
  let b3 := P.alphaK c.j ht
  decide (5 ≤ P.p) && P.wordOK c.psi && decide (Q.s ≤ c.j) && decide (c.j < Q.s + (P.nFrame - 2)) &&
    decide (Q.s ≤ c.j') && decide (c.j' < Q.s + (P.nFrame - 2)) &&
    decide (c.j ≠ c.j') && decide ((a1 * a2 * a3) % P.p ≠ (b1 * b2 * b3) % P.p) &&
    (List.range P.D).any fun i => P.applyWord (w ++ [c.j']) (P.unit i) != P.applyWord ([c.j'] ++ w) (P.unit i)

@[expose] def verifyWPos (P : Pt) (c : WWit) : Bool :=
  decide (c.kind < 4) &&
  (c.kind == 0 && decide (1 ≤ P.D) || c.kind == 1 && decide (2 ≤ P.D) ||
   c.kind == 2 && decide (4 ≤ P.D) || c.kind == 3 && decide (P.D = 7)) &&
  c.sigma.length == P.D &&
  c.sigma.all (fun s => P.wordOK s.1 && decide (s.2 < P.gens.length)) &&
  (let S := c.sigma.map fun s => P.sigmaVecs s.1 s.2
   S.all (fun cb => P.dotv cb.2 cb.1 == 2 % P.p) &&
   (List.range P.D).all (fun i => (List.range P.D).all fun j =>
     i == j ||
       (let a := P.dotv (S.getD i ([], [])).2 (S.getD j ([], [])).1
        let b := P.dotv (S.getD j ([], [])).2 (S.getD i ([], [])).1
        if c.kind == 0 then
          (if i + 1 == j || j + 1 == i then (a * b) % P.p == 1 else a == 0 && b == 0)
        else if c.kind == 1 then
          (if (i == P.D - 1 && j == P.D - 2) || (j == P.D - 1 && i == P.D - 2) then
              (a * b) % P.p == 2
           else if i + 1 == j || j + 1 == i then (a * b) % P.p == 1
           else a == 0 && b == 0)
        else if c.kind == 2 then
          (if ((i + 1 == j && j + 2 < P.D) || ((j + 1 == i && i + 2 < P.D) || ((i + 3 == P.D && (j + 2 == P.D || j + 1 == P.D)) || (j + 3 == P.D && (i + 2 == P.D || i + 1 == P.D))))) then
              (a * b) % P.p == 1
           else a == 0 && b == 0)
        else
          (if ((i == 0 && j == 2) || ((i == 2 && j == 0) || ((i == 1 && j == 3) || ((i == 3 && j == 1) || ((i == 2 && j == 3) || ((i == 3 && j == 2) || ((i == 3 && j == 4) || ((i == 4 && j == 3) || ((i == 4 && j == 5) || ((i == 5 && j == 4) || ((i == 5 && j == 6) || (i == 6 && j == 5)))))))))))) then
              (a * b) % P.p == 1
           else a == 0 && b == 0))) &&
  c.expr.length == P.gens.length &&
  ((c.expr.zip P.gens).all fun (w, r) =>
     w.all (fun i => decide (i < P.D)) &&
       (List.range P.D).all fun j =>
         P.vecEq (P.sigmaWord S w (P.unit j)) (P.applyRefl r (P.unit j)))) &&
  verifyO P c.chain
    ((if c.kind == 0 then natFact (P.D + 1)
      else if c.kind == 1 then 2 ^ P.D * natFact P.D
      else if c.kind == 2 then 2 ^ (P.D - 1) * natFact P.D
      else 2903040) - 1)

@[expose] def verifyPos (Q : SPt) : PWitness → Bool
  | .fixed => verifyF Q.pt
  | .self_ => verifyS Q.pt
  | .transv t => wfCheck Q.pt && verifyT Q.pt t
  | .cycle c => wfCheck Q.pt && verifyC Q c
  | .order o => wfCheck Q.pt && verifyO Q.pt o Q.pt.bound
  | .weyl c => wfCheck Q.pt && verifyWPos Q.pt c

@[expose] def verifyExcl (Q : SPt) : PWitness → Bool
  | .order _ => false
  | .weyl _ => false
  | w => verifyPos Q w

end CFSG.TwoNodeSmall

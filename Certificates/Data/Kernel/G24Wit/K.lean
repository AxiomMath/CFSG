module

public import Certificates.Data.Kernel.Misc.G24
public import Certificates.Data.G24IdentWit

public section

namespace CFSG.KC.G24Wit

open CFSG.KC.Misc.G24 CFSG.Quasithin.St84.G24Wit CFSG.Quasithin.St84.G24Ident
  CFSG.Quasithin.St84.G24Pc CFSG.Quasithin.St84.G24DC

@[expose] noncomputable def oneK : Nat := oneF2 28

@[expose] noncomputable def getK (g : List Nat) (i : Nat) : Nat := g.getD i oneK

@[expose] noncomputable def wK (Gb : List Nat) (w : List (Fin 6 × Bool)) : Nat :=
  wordF4 Gb (w.map fun l => 2 * l.1.val + if l.2 then 1 else 0)

@[expose] noncomputable def matsK (Gb : List Nat) (ws : List Word) : List Nat × List Nat :=
  (ws.map (wK Gb), ws.map fun w => wK Gb w.reverse)

@[expose] noncomputable def evalPK {n : Nat} (g : List Nat) (w : List (Fin n)) : Nat :=
  w.foldr (fun l A => mulF2 28 (getK g l.val) A) oneK

@[expose] noncomputable def evalPInvK {n : Nat} (g : List Nat) (w : List (Fin n)) : Nat :=
  w.foldl (fun A l => mulF2 28 (getK g l.val) A) oneK

@[expose] noncomputable def evalLK {n : Nat} (G : List Nat × List Nat) (w : List (Fin n × Bool)) :
    Nat :=
  w.foldr (fun l A => mulF2 28 (if l.2 then getK G.1 l.1.val else getK G.2 l.1.val) A) oneK

@[expose] noncomputable def conjK (g x g' : Nat) : Nat := mulF2 28 (mulF2 28 g x) g'

@[expose] noncomputable def cocK (P2 A2 : List Nat × List Nat) (D : List (List (Fin 10))) :
    List Nat × List Nat :=
  ((List.range 3).map fun t => mulF2 28 (evalPK P2.1 (D.getD t [])) (getK A2.1 t),
   (List.range 3).map fun t => mulF2 28 (getK A2.2 t) (evalPInvK P2.2 (D.getD t [])))

@[expose] def digsN (A : Native.Mat) : List (List Nat) :=
  (List.range 14).map fun i => (List.range 14).map fun j => Native.rowVal (A.getD i Native.zeroRow) j

@[expose] noncomputable def decK (A : Native.Mat) : Nat := blow14 (digsN A)

@[expose] def frobRow (r : Native.Row) : Native.Row := (r.1 ^^^ r.2, r.2)

@[expose] def frobN (A : Native.Mat) : Native.Mat := A.map frobRow

@[expose] noncomputable def evalFK (g : List Nat) (w : List (Fin 4)) : Nat :=
  w.foldl (fun acc l => mulF2 28 acc (getK g l.val)) oneK

@[expose] noncomputable def gbK : List Nat := (Native.gBN ()).toList.map decK

@[expose] noncomputable def gbFK : List Nat := (Native.gBN ()).toList.map fun A => decK (frobN A)

@[expose] noncomputable def wRowK (g : List Nat) (i : Nat) : List Nat :=
  (Native.wWords.getD i []).map (evalFK g)

@[expose] noncomputable def witK (Gb : List Nat) : Bool :=
  let P1 := matsK Gb pc1
  let P2 := matsK Gb pc2
  let A1 := matsK Gb [a1, b1, k1]
  let A2 := matsK Gb [a2, b2, k2]
  let be : List Nat × List Nat := (e1Q.map (evalPK P1.1), e1Q.map (evalPInvK P1.2))
  let al : List Nat × List Nat := (e1A.map (evalLK A1), e1A.map fun w => evalLK A1 (invW w))
  let cs := e2Coc.map (cocK P2 A2)
  let gb := gbK
  (Native.gBN ()).toList.all (fun A => shape4 (digsN A) && shape4 (digsN (frobN A))) &&
  relsQ1.all (fun r => Nat.beq (evalLK be r) oneK) &&
  (List.range 10).all (fun j => Nat.beq (evalPK be.1 (e1Q.getD j [])) (getK P1.1 j)) &&
  relsA.all (fun r => Nat.beq (evalLK al r) oneK) &&
  (List.range 3).all (fun t => (List.range 10).all fun j =>
    Nat.beq (conjK (getK A1.1 t) (getK P1.1 j) (getK A1.2 t))
      (evalPK P1.1 ((conjQ1.getD t []).getD j [])) &&
    Nat.beq (evalPK be.1 ((conjQ1.getD t []).getD j []))
      (conjK (getK al.1 t) (getK be.1 j) (getK al.2 t))) &&
  (List.range 4).all (fun k =>
    Nat.beq (getK gb k) (mulF2 28 (evalPK P1.1 (dec1.getD k ([], [])).1)
      (evalPK A1.1 (dec1.getD k ([], [])).2)) &&
    Nat.beq (getK (wRowK gb 2) k) (mulF2 28 (evalPK be.1 (dec1.getD k ([], [])).1)
      (evalPK al.1 (dec1.getD k ([], [])).2))) &&
  cs.all (fun c => relsA.all fun r => Nat.beq (evalLK c r) oneK) &&
  (List.range 4).all (fun k =>
    Nat.beq (getK gb k) (mulF2 28 (evalPK P2.1 (dec2.getD k ([], [])).1)
      (evalPK A2.1 (dec2.getD k ([], [])).2)) &&
    (List.range 4).all fun s =>
      Nat.beq (getK (wRowK gb (4 + s)) k) (mulF2 28 (evalPK P2.1 (dec2.getD k ([], [])).1)
        (evalPK (cs.getD s ([], [])).1 (dec2.getD k ([], [])).2))) &&
  (wRowK gb 0 == gb) &&
  (wRowK gb 1 == gbFK) &&
  (wRowK gb 3 == wRowK gbFK 2) &&
  (List.range 4).all (fun s => wRowK gb (8 + s) == wRowK gbFK (4 + s)) &&
  (Native.wWords.length == 12) && Native.wWords.all (fun r => r.length == 4)

end CFSG.KC.G24Wit

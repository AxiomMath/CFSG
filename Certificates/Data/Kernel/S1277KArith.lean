module

public import Certificates.Data.Kernel.S1277KSig
public import Certificates.Data.Kernel.S1277KCand

public section

namespace CFSG.KC.S1277Ar

open CFSG.KC.S1277Lat CFSG.KC.S1277Mod CFSG.KC.S1277Sig CFSG.KC.S1277Cand

@[expose] noncomputable def xChk (d L u : ℕ) (ts : List (List ℕ)) : Bool :=
  Nat.beq L (2 ^ u) && Nat.blt u (2 ^ d) && Nat.beq ts.length 8 &&
    allL (List.range 8) (fun j => tChk d L [] 0 (ts.getD j []) &&
      allLt (2 ^ d) (fun x => Nat.beq (apK (ts.getD j []) x ^^^ x) 0 ||
        Nat.beq (apK (ts.getD j []) x ^^^ x) u) &&
      allLt j fun j' => !eqL (ts.getD j []) (ts.getD j' []))

@[expose] def chainOrd (d : ℕ) (T : List (List (List ℕ))) : ℕ :=
  ((List.range d).map fun k => (T.getD k []).length).prod

@[expose] noncomputable def arChk (nb ol xi : ℕ) (nx : List ℕ) (is ds ls tx : List ℕ)
    (sd sl : List ℕ) (sT : List (List (List (List ℕ)))) (ab ak : List ℕ) (j : ℕ) : Bool :=
  let i := is.getD j 0
  let t := tx.getD j 0
  let n := 2 ^ nx.getD i 0
  let e := nb * 64 / n
  let s := chainOrd (sd.getD t 0) (sT.getD t [])
  Nat.blt t sd.length && Nat.beq (ds.getD j 0) (sd.getD t 0) && Nat.beq (ls.getD j 0) (sl.getD t 0) &&
    Nat.beq (n * e) (nb * 64) && Nat.beq s (e * (ab.getD j 0 * 2 ^ ak.getD j 0)) &&
    ((Nat.beq (ab.getD j 0) 3 && Nat.ble (nx.getD i 0 + 2) (nx.getD ol 0)) ||
      (Nat.beq (ab.getD j 0) 7 && Nat.blt (ak.getD j 0) 3 && Nat.beq t xi))

@[expose] noncomputable def arAll (nb ol xi sv : ℕ) (nx : List ℕ) (is ds ls tx : List ℕ)
    (sd sl : List ℕ) (sT : List (List (List (List ℕ)))) (ab ak : List ℕ) : Bool :=
  Nat.beq tx.length is.length &&
    allL (List.range is.length) fun j =>
      Nat.beq (is.getD j 0) sv || arChk nb ol xi nx is ds ls tx sd sl sT ab ak j

@[expose] noncomputable def covChk (n : ℕ) (is₁ is₂ is₃ is₄ : List ℕ) : Bool :=
  allLt n fun i => memL i is₁ || memL i is₂ || memL i is₃ || memL i is₄

end CFSG.KC.S1277Ar

end

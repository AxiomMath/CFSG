module

public import Certificates.Data.Kernel.E6Syl3

public section

namespace CFSG.KC.E6O2

open CFSG.KC.E6Syl3

@[expose] def pcTups (n : ℕ) (gw : List (List ℕ)) : List (List ℕ) :=
  gw.foldr (fun w acc => (List.range n).flatMap fun a => acc.map (powT w a)) [List.range 6]

@[expose] def subCheck (gw : List (List ℕ)) (N : ℕ) (Q : List (List ℕ)) : Bool :=
  gw.all (fun w => w.all fun i => decide (i < 6)) && Q.length == N && nodupB Q &&
    Q.contains (List.range 6) && Q.all fun t => gw.all fun w => Q.contains (wordT w t)

@[expose] def om3L : List ℤ := [4, 3, 5, 6, 4, 2]

@[expose] def shL (t : List ℕ) : List ℤ := (addV (actV t om3L) (negV om3L)).map (· / 3)

@[expose] def colL (t : List ℕ) (c j : ℕ) : List ℤ :=
  if j < 6 then addV (rvL (t.getD j 0)) (negV (eV j)) else addV (shL t) (smulV (-(c : ℤ)) om3L)

@[expose] def combL (t : List ℕ) (c : ℕ) (x : List ℕ) : List ℤ :=
  (List.range 7).foldr (fun j acc => addV (smulV (x.getD j 0 : ℤ) (colL t c j)) acc) zeroV

@[expose] def cong3 (u v : List ℤ) : Bool :=
  (List.range 6).all fun i => (u.getD i 0 - v.getD i 0) % 3 == 0

@[expose] def uV (i f₀ f₁ a b : ℕ) : List ℤ :=
  addV (eV i) (addV (smulV (-(a : ℤ)) (eV f₀)) (smulV (-(b : ℤ)) (eV f₁)))

@[expose] def killW (t : List ℕ) (c : ℕ) (w : List ℕ) : Bool :=
  decide (w.getD 1 0 < 72) && cong3 (rvL (w.getD 1 0)) (combL t c (w.drop 2))

@[expose] def blkW (w : List ℕ) (i : ℕ) : List ℕ := w.drop (3 + 9 * i)

@[expose] def smallW (t : List ℕ) (c : ℕ) (w : List ℕ) : Bool :=
  decide (w.getD 1 0 < 6) && decide (w.getD 2 0 < 6) && (List.range 6).all fun i =>
    cong3 (uV i (w.getD 1 0) (w.getD 2 0) ((blkW w i).getD 0 0) ((blkW w i).getD 1 0))
      (combL t c ((blkW w i).drop 2))

@[expose] def witOK (t : List ℕ) (c : ℕ) (w : List ℕ) : Bool :=
  (w.headD 9 == 0 && killW t c w) || (w.headD 9 == 1 && smallW t c w)

@[expose] def o2At (t : List ℕ) (ws : List (List ℕ)) : Bool :=
  t == List.range 6 || (List.range 3).all fun c => witOK t c (ws.getD c [])

@[expose] def o2Check (Q : List (List ℕ)) (W : List (List (List ℕ))) : Bool :=
  Q.length == W.length && (Q.zip W).all fun p => o2At p.1 p.2

end CFSG.KC.E6O2

module

public import CFSG.Certificates.PresentationLetters
public import Mathlib

public section

namespace CFSG.KC.MiscCoset.CovAct

open CFSG.Certificates.CosetEnumeration

variable {M : ℕ}

@[expose] def projB (mb : ℕ) (u : List (Fin M × Bool)) : List (Fin M × Bool) :=
  u.filter fun l => decide (l.1.val < mb)

@[expose] def zl (q mb : ℕ) (zs : List ℕ) (l : Fin M × Bool) : ℕ :=
  if l.1.val < mb then 0
  else if l.2 then zs.getD (l.1.val - mb) 0 % q else (q - zs.getD (l.1.val - mb) 0 % q) % q

@[expose] def zsum (q mb : ℕ) (zs : List ℕ) (u : List (Fin M × Bool)) : ℕ :=
  (u.map (zl q mb zs)).sum

@[expose] def expandW (mb : ℕ) (mac : List (List ℕ)) (w : List ℕ) : List ℕ :=
  w.flatMap fun c => if 2 * mb ≤ c then mac.getD (c - 2 * mb) [] else [c]

@[expose] def hintOK (q mb : ℕ) (zs : List ℕ) (mac : List (List ℕ)) (chk : List (List ℕ × ℕ))
    (u : List (Fin M × Bool)) (h : ℕ × ℕ × ℕ) : Bool :=
  if h.1 = 0 then (FreeGroup.reduce (projB mb u)).isEmpty && zsum q mb zs u % q == 0
  else
    decide (h.1 - 1 < chk.length) &&
    (if h.2.2 = 0 then
      decide (h.2.1 ≤ (projB mb u).length) &&
        (((projB mb u).rotate h.2.1).map letterCode == expandW mb mac (chk.getD (h.1 - 1) ([], 0)).1) &&
        ((chk.getD (h.1 - 1) ([], 0)).2 + zsum q mb zs u) % q == 0
    else
      decide (h.2.1 ≤ (projB mb u).length) &&
        (((FreeGroup.invRev (projB mb u)).rotate h.2.1).map letterCode ==
          expandW mb mac (chk.getD (h.1 - 1) ([], 0)).1) &&
        (q - (chk.getD (h.1 - 1) ([], 0)).2 + zsum q mb zs u) % q == 0)

@[expose] def symOK (q mb L : ℕ) (zs : List ℕ) (mac : List (List ℕ)) (chk : List (List ℕ × ℕ))
    (ws : List (List (Fin M × Bool))) (hint : List (ℕ × ℕ × ℕ)) : Bool :=
  decide (0 < q) && decide (mb ≤ M) && L == 2 * mb + mac.length &&
    mac.all (fun w => w.all fun c => decide (c < 2 * mb)) &&
    chk.all (fun wt => decide (wt.2 < q) && wt.1.all fun c => decide (c < L)) &&
    ws.length == hint.length &&
    (ws.zip hint).all fun p => hintOK q mb zs mac chk p.1 p.2

end CFSG.KC.MiscCoset.CovAct

end

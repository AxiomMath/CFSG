module

public import Certificates.Data.Kernel.Compat

public section

namespace CFSG.KC.OctadBig

open CFSG.KC.Ord CFSG.KC.LQT.P CFSG.KC.LQT.W CFSG.KC.LQT.Syl CFSG.KC.Sym6Sq CFSG.KC.Compat

@[expose] noncomputable def cosK (E B C : List Nat) : Bool :=
  andB (nodupK C) (andB (allL C fun c => memI B 16 c)
  (andB (allL C fun c => allL C fun c' => anyL C fun c'' =>
      memI E 64 (mul 24 (mul 24 c c') (inv 24 c'')))
    (allL C fun c => allL C fun c' =>
      impB (memI E 64 (mul 24 c' (inv 24 c))) (Nat.beq c c'))))

@[expose] noncomputable def ordK (B : List Nat) (p r : Nat) : Bool :=
  andB (Nat.beq (pow 24 p r) (one 24)) (andB (notB (Nat.beq p (one 24)))
    (strictA (inv 24 p) fun pi => allL B fun b => memI B 16 (cjK p b pi)))

@[expose] noncomputable def obK (G : List Nat) (rgw bw b0w nw : List (List Int))
    (w3 w5 w7 : List Int) : Bool :=
  forceA (lstK 24 6 (rlGK 24 G rgw bw)) fun E =>
  forceA (b0w.map (evalZK 24 G)) fun BB =>
  forceA (lstK 24 4 BB) fun B =>
  strictA (eltK 24 4 BB (nat_lit 4)) fun c1 => strictA (eltK 24 4 BB (nat_lit 8)) fun c2 =>
  forceA (nw.map (evalZK 24 G)) fun NG =>
    andB (cosK E B [one 24, c1, c2, mul 24 c1 c2])
      (andB (ordK B (evalZK 24 NG w3) (nat_lit 3))
        (andB (ordK B (evalZK 24 NG w5) (nat_lit 5)) (ordK B (evalZK 24 NG w7) (nat_lit 7))))

end CFSG.KC.OctadBig

end

module

public import Certificates.Data.Kernel.J2Five

public section

namespace CFSG.KD.KS152Gen

open CFSG.KC.Enum CFSG.KS CFSG.KC.YoshQ CFSG.KD.J2Five

@[expose] noncomputable def valsOK (G E : List Nat) (Ws : List (List Nat)) : Bool :=
  bAnd(Nat.beq (lenN E) (lenW Ws), allN (lenN E) fun i =>
    bAnd(letOK (lenN G) (getW Ws i), eq (getN E i) (wordN G (getW Ws i))))

@[expose] noncomputable def invsOK (E Ei : List Nat) : Bool :=
  bAnd(Nat.beq (lenN Ei) (lenN E), allN (lenN E) fun i => eq (pm (getN E i) (getN Ei i)) one)

@[expose] noncomputable def cubeOK (E Ei : List Nat) : Bool :=
  bAnd(Nat.beq (lenN Ei) (lenN E), allN (lenN E) fun i =>
    eq (getN Ei i) (pm (getN E i) (pm (getN E i) (getN E i))))

@[expose] noncomputable def comm (x y : Nat) : Bool := eq (pm x y) (pm y x)

@[expose] noncomputable def normOK (H : List Nat) (nh : Nat) (Q : List Nat) (W : List (List Nat))
    (nI : List (List Nat)) : Bool :=
  allN nh fun h => allN (lenN Q) fun k => strictB (getN (getW nI h) k) fun q =>
    bAnd(Nat.blt q (lenW W), eq (pm (getN H h) (getN Q k)) (pm (elt Q W q) (getN H h)))

@[expose] noncomputable def shapeW (w : List Nat) : Bool :=
  List.rec (motive := fun _ => Bool) false
    (fun c hs _ => bAnd(Nat.ble (nat_lit 2) c, bAnd(Nat.blt c (nat_lit 14), letOK (nat_lit 2) hs)))
    w

@[expose] noncomputable def shapeOK (R : List (Nat × List Nat)) : Bool :=
  List.rec (motive := fun _ => Bool) true (fun r _ ih => bAnd(shapeW r.2, ih)) R

@[expose] noncomputable def genL (Q Qi : List Nat) (r ri : Nat) : List Nat :=
  [getN Q 0, getN Q 1, getN Q 2, getN Q 3, r, getN Qi 0, getN Qi 1, getN Qi 2, getN Qi 3, ri]

@[expose] noncomputable def genOK (a b y yi : Nat) (C Ci Q Qi : List Nat)
    (aw bw : List (List Nat)) : Bool :=
  allN (nat_lit 12) fun j =>
    strictB (pm (pm (getN Ci (Nat.add 2 j)) y) (getN C (Nat.add 2 j))) fun r =>
      strictB (pm (pm (getN Ci (Nat.add 2 j)) yi) (getN C (Nat.add 2 j))) fun ri =>
        bAnd(letOK (nat_lit 10) (getW aw j), bAnd(letOK (nat_lit 10) (getW bw j),
          bAnd(eq a (wordN (genL Q Qi r ri) (getW aw j)),
            eq b (wordN (genL Q Qi r ri) (getW bw j)))))

@[expose] noncomputable def ord5 (y : Nat) : Bool :=
  bAnd(eq (pm y (pm y (pm y (pm y y)))) one, bIf(eq y one, false, true))

@[expose] noncomputable def ord3 (t : Nat) : Bool :=
  bAnd(eq (pm t (pm t t)) one, bIf(eq t one, false, true))

@[expose] def pts : List Nat := [0, 4, 3]

@[expose] noncomputable def ckT (S : List Nat) (W C : List (List Nat)) (i₀ : Nat)
    (xI Q : List Nat) : Bool :=
  bAnd(grpOK S pts W C i₀, bAnd(Nat.beq (lenW W) (nat_lit 128), bAnd(Nat.beq (lenN xI) (nat_lit 4),
    bAnd(Nat.beq (lenN Q) (nat_lit 4), allN (nat_lit 4) fun k => strictB (getN xI k) fun i =>
      bAnd(Nat.blt i (nat_lit 128), strictB (elt S W i) fun x => eq (getN Q k) (pm x x))))))

@[expose] noncomputable def ckW (Q : List Nat) (W C : List (List Nat)) (i₀ : Nat) (H : List Nat)
    (nI : List (List Nat)) : Bool :=
  bAnd(grpOK Q pts W C i₀, normOK H (nat_lit 2) Q W nI)

@[expose] noncomputable def ckS (S : List Nat) (W C : List (List Nat)) (i₀ zi y : Nat) : Bool :=
  bAnd(grpOK S pts W C i₀, bAnd(Nat.beq (lenW W) (nat_lit 27), bAnd(Nat.beq (lenN S) (nat_lit 2),
    bAnd(Nat.blt zi (lenW W), bAnd(ord5 y, strictB (elt S W zi) fun z =>
      bAnd(bIf(eq z one, false, true), bAnd(comm z (getN S 0), bAnd(comm z (getN S 1),
        comm z y))))))))

@[expose] noncomputable def ckF (y : Nat) (F : List Nat) (aW aC : List (List Nat)) (ai0 : Nat)
    (kW kC : List (List Nat)) (ki0 : Nat) : Bool :=
  bAnd(Nat.beq (lenN F) (nat_lit 4),
    bAnd(grpOK [y, getN F 0] pts aW aC ai0, bAnd(Nat.beq (lenW aW) (nat_lit 25),
    bAnd(grpOK [getN F 1, getN F 2] pts kW kC ki0, bAnd(Nat.beq (lenW kW) (nat_lit 4),
    bAnd(comm (getN F 0) y, bAnd(comm (getN F 1) y, bAnd(comm (getN F 2) y,
    bAnd(comm (getN F 3) y, ord3 (getN F 3))))))))))

@[expose] noncomputable def ckC (G Gi : List Nat) (y : Nat) (R : List (Nat × List Nat)) : Bool :=
  bAnd(Nat.beq (lenN G) (nat_lit 14), bAnd(shapeOK R, orbOK G Gi y pts R (nat_lit 2016)))

end CFSG.KD.KS152Gen

end

module

public import Certificates.Data.Kernel.HMathieu.Pred24
public import Certificates.Data.Kernel.HMathieu.PredQK

public section

namespace CFSG.KC.HMathieu

open CFSG.KC.Enum CFSG.Quasithin.H.Mathieu

@[expose] noncomputable def nodupMK (l : List Nat) (acc : Nat) : Bool :=
  List.rec (motive := fun _ => Nat → Bool) (fun _ => true)
    (fun x _ ih acc => bIf(Nat.beq (Nat.land (Nat.shiftRight acc x) (nat_lit 1)) (nat_lit 1), false,
      strictB (Nat.lor acc (Nat.shiftLeft (nat_lit 1) x)) ih)) l acc

@[expose] noncomputable def xiCandsF (Mc : List (List Nat)) (S : List Nat) : List Nat :=
  List.rec (motive := fun _ => List Nat) []
    (fun s _ ih => Bool.rec (motive := fun _ => List Nat)
      (List.append (fixLstQ (Mc.getD s []) (List.range (nat_lit 2048))) ih) ih
      (Nat.beq s (nat_lit 191))) S

@[expose] noncomputable def xiF (Mc : List (List Nat)) (S : List Nat) : Bool :=
  (fun b => bAnd(Nat.ble (nat_lit 11) (lenK b), nodupMK (combos b) (nat_lit 0)))
    (pickBasis (xiCandsF Mc S))

@[expose] noncomputable def pred24F (Mc : List (List Nat)) (L S : List Nat)
    (st : List (List Nat) × List Nat) : Bool :=
  strictB (lenK L) fun k => strictB (lenK st.2) fun c =>
    bAnd(Nat.ble k (nat_lit 6),
      bAnd(bIf(Nat.beq k (nat_lit 0), true,
          bIf(Nat.blt c (Nat.shiftLeft (nat_lit 1) (Nat.sub (nat_lit 10) k)), true,
            avoidK 11 3 o2Masks24 st.2)),
        bAnd(bIf(Nat.beq k (nat_lit 1), Nat.blt c (nat_lit 256), true),
          bIf(Nat.beq k (nat_lit 6),
            bIf(bAnd(Nat.ble (nat_lit 8) c, Nat.blt c (nat_lit 16)), true, xiF Mc S), true))))

@[expose] noncomputable def pred24FK (Mc : List (List Nat)) (L S : List Nat)
    (st : List (List Nat) × List Nat) : Bool :=
  bIf(pred24F Mc L S st, true, pred24K Mc L S st)

end CFSG.KC.HMathieu

end

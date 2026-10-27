module

public import Certificates.Data.Kernel.TwoF4LieK

public section

namespace CFSG.KC.TitsLocK

open CFSG.KC.Enum CFSG.KS CFSG.KC.TwoF4LieK

@[expose] noncomputable def wordDe (w : List Nat) : Bool → Bool :=
  List.rec (motive := fun _ => Bool → Bool) (fun e => e)
    (fun c _ ih e => bAnd(Nat.ble (nat_lit 2) c, bAnd(Nat.blt c (nat_lit 10),
      ih (bIf(Nat.beq (Nat.shiftRight c (nat_lit 1)) (nat_lit 2), bIf(e, false, true), e))))) w

@[expose] noncomputable def wordD (w : List Nat) : Bool := wordDe w true

@[expose] noncomputable def pairK (F FI A B lp : Nat → Nat) (base : List Nat) (r : List Nat) :
    Bool :=
  bAnd(wordD (r.drop 8), bAnd(rowF F FI A B lp base (r.take 4 ++ r.drop 8),
    rowF F FI A B lp base (r.drop 4)))

@[expose] noncomputable def pchK (F FI A B lp : Nat → Nat) (base : List Nat) (z₀ z₁ e₀ e₁ : Nat) :
    List (List Nat) → Nat → Nat → Nat → Nat → Bool :=
  List.rec (motive := fun _ => Nat → Nat → Nat → Nat → Bool)
    (fun ia ja ib jb => bAnd(Nat.beq ia z₀, bAnd(Nat.beq ja z₁, bAnd(Nat.beq ib e₀, Nat.beq jb e₁))))
    (fun r _ ih ia ja ib jb => bAnd(Nat.beq (r.getD 2 0) ia, bAnd(Nat.beq (r.getD 3 0) ja,
      bAnd(Nat.beq (r.getD 6 0) ib, bAnd(Nat.beq (r.getD 7 0) jb,
      bAnd(pairK F FI A B lp base r, ih (r.getD 0 0) (r.getD 1 0) (r.getD 4 0) (r.getD 5 0)))))))

@[expose] noncomputable def conjPt (F FI : Nat → Nat) (Z : Nat) (m : List Nat) (x : Nat) : Nat :=
  wPt F FI m (gp Z (wInv F FI m x))

@[expose] noncomputable def uK (F FI A B lp : Nat → Nat) (base : List Nat) (Z : Nat)
    (u : List Nat) : Bool :=
  strictB (A (u.getD 1 0)) (fun a => strictB (B (u.getD 2 0)) (fun b =>
    bAnd(Nat.beq (wPt F FI (u.drop 3) 0) (u.headD 0),
    bAnd(stabS lp (conjPt F FI Z (u.drop 3)),
      List.all base (fun p => Nat.beq (conjPt F FI Z (u.drop 3) p) (gp a (gp b p)))))))

@[expose] noncomputable def endK (A B lp : Nat → Nat) (e : List Nat) : Bool :=
  bAnd(bIf(Nat.beq (gp (A (e.getD 0 0)) (gp (B (e.getD 1 0)) (e.getD 2 0))) (e.getD 2 0), false,
      true),
    bAnd(onLine lp 0 (e.getD 3 0), onLine lp (e.getD 2 0) (e.getD 3 0)))

@[expose] noncomputable def locK (F FI A B lp : Nat → Nat) (base : List Nat) (Z : Nat)
    (r₀ r₁ : List Nat) (U : List (List Nat)) (P : List (List (List Nat))) (E : List (List Nat))
    (i₀ : Nat) : Bool :=
  allL (fun k u => bAnd(uK F FI A B lp base Z u, bAnd(endK A B lp (E.getD k []),
    pchK F FI A B lp base (r₀.headD 0) (r₀.tail.headD 0) ((E.getD k []).headD 0)
      ((E.getD k []).getD 1 0) (P.getD k []) (u.getD 1 0) (u.getD 2 0) (r₁.headD 0)
      (r₁.tail.headD 0)))) U i₀

@[expose] noncomputable def fixK (T C : Nat) (U : List (List Nat)) : Bool :=
  allN (nat_lit 1755) (fun p => bIf(Nat.beq (gp T p) p,
    bIf(Nat.beq p (nat_lit 0), true, bIf(Nat.beq p (gp C (nat_lit 0)), true,
      bIf(Nat.beq p (gp C (gp C (nat_lit 0))), true, List.any U (fun u => Nat.beq (u.headD 0) p)))),
    true))

@[expose] noncomputable def qK (F FI lp : Nat → Nat) (Z T C : Nat) (w : List Nat) : Bool :=
  bAnd(wordD w, strictB (wN F FI w) (fun Q => strictB (mul C (mul Z (mul C C))) (fun Z₁ =>
    bAnd(stabS lp (gp Q), bAnd(Nat.beq (mul Q Q) Z, bAnd(Nat.beq (mul Q T) (mul T Q),
      Nat.beq (mul Q Z₁) (mul Z₁ Q)))))))

end CFSG.KC.TitsLocK

end

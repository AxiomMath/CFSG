module

public import Certificates.Data.Kernel.Child3
public import Certificates.Data.Kernel.Fendel

public section

namespace CFSG.KC.E3

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.Fendel CFSG.KC.Child3

@[expose] noncomputable def cnj (GP GIP : Nat → Nat) (i X : Nat) : Nat := pc (pc (GP i) X) (GIP i)

@[expose] noncomputable def repPos (TB : Nat → Nat) (CS OFF : List Nat) (M CC : Nat → Nat)
    (c m p : Nat) : Bool :=
  bAnd(Nat.beq (CC p) (pidn 276 9), bAnd(Nat.beq (TB m) 1,
    bIf(Nat.blt (Nat.succ c) CS.length, Nat.blt m (M (lget OFF (Nat.succ c))), true)))

@[expose] noncomputable def stepPos (E GP GIP : Nat → Nat) (M PA LB CC CV : Nat → Nat)
    (o k m p : Nat) : Bool :=
  bAnd(Nat.blt (PA p) k, bAnd(Nat.blt (LB p) 3,
  bAnd(Nat.beq (E m) (cnj GP GIP (LB p) (E (M (Nat.add o (PA p))))),
  bAnd(prodOK (GP (LB p)) (CC (Nat.add o (PA p))) (CC p),
  bAnd(invEqK 276 9 (mask 9) (Nat.mul 276 9) (CC p) (pinvS 276 9 (mask 9) (CC p)),
  bAnd(Nat.blt (CV p) 4608, Nat.beq (E (CV p)) (pinvS 276 9 (mask 9) (CC p))))))))

@[expose] noncomputable def cloPos (E GP GIP : Nat → Nat) (M PA LB K : Nat → Nat)
    (o s k m p i : Nat) : Bool :=
  strictB (K (Nat.add (Nat.mul 3 p) i)) (fun q => bAnd(Nat.blt q s,
    bAnd(Nat.beq (E (M (Nat.add o q))) (cnj GP GIP i (E m)),
      bIf(Nat.beq q 0, true, bIf(lexLtK k i (PA (Nat.add o q)) (LB (Nat.add o q)), false,
        true)))))

@[expose] noncomputable def lexPos (PA LB : Nat → Nat) (s k p : Nat) : Bool :=
  bIf(Nat.beq k 0, true, bIf(Nat.blt (Nat.succ k) s,
    lexLtK (PA p) (LB p) (PA (Nat.succ p)) (LB (Nat.succ p)), true))

@[expose] noncomputable def cdPosK (E GP GIP TB : Nat → Nat) (CS OFF : List Nat)
    (CI M PA LB CC CV K MI : Nat → Nat) (N p : Nat) : Bool :=
  strictB (CI p) (fun c => strictB (lget OFF c) (fun o => strictB (lget CS c) (fun s =>
  strictB (Nat.sub p o) (fun k => strictB (M p) (fun m =>
  bAnd(Nat.blt c CS.length, bAnd(Nat.ble o p, bAnd(Nat.blt k s, bAnd(Nat.blt m 4608,
  bAnd(Nat.beq (MI m) p,
  bAnd(bIf(Nat.beq k 0, repPos TB CS OFF M CC c m p, stepPos E GP GIP M PA LB CC CV o k m p),
  bAnd(lexPos PA LB s k p,
    allN 3 (fun i => cloPos E GP GIP M PA LB K o s k m p i)))))))))))))

@[expose] noncomputable def cdMemK (TB : Nat → Nat) (CS OFF : List Nat) (CI M MI : Nat → Nat)
    (N j : Nat) : Bool :=
  bIf(Nat.beq (TB j) 1, strictB (MI j) (fun p => bAnd(Nat.blt p N, bAnd(Nat.beq (M p) j,
    Nat.ble (M (lget OFF (CI p))) j))), true)

@[expose] noncomputable def ckF (CI MI : Nat → Nat) (N j : Nat) : Nat :=
  nIf(Nat.blt (MI j) N, CI (MI j), 0)

@[expose] noncomputable def ciF (CS OFF : List Nat) (CI CV MI : Nat → Nat) (N j : Nat) : Nat :=
  nIf(Nat.blt (MI j) N, nIf(Nat.beq (lget OFF (CI (MI j))) (MI j), 0, CV (MI j)), 0)

@[expose] noncomputable def zcK (A Z EA X : Nat) : Nat :=
  nIf(Nat.beq X (pidn 276 9), 0, nIf(Nat.beq X Z, 1, nIf(Nat.beq X A, 2, nIf(Nat.beq X EA, 3, 4))))

@[expose] noncomputable def prodP (Ys : List Nat) : List Nat → Nat
  | [] => pidn 276 9
  | i :: w => pc (lget Ys i) (prodP Ys w)

@[expose] noncomputable def powR (t : Nat) : Nat → Nat
  | 0 => pidn 276 9
  | m + 1 => pc (powR t m) t

@[expose] noncomputable def profK (A Z EA t : Nat) : Nat → List Nat → Bool
  | _, [] => true
  | acc, e :: es => strictB (pc acc t) (fun a' => bAnd(Nat.beq (zcK A Z EA a') e, profK A Z EA t a' es))

@[expose] noncomputable def testK (A Z EA : Nat) (Ys : List Nat) (ws : List (List Nat × List Nat)) :
    Bool :=
  ws.all fun p => profK A Z EA (prodP Ys p.1) (pidn 276 9) p.2

@[expose] noncomputable def failK (A Z EA : Nat) (Ys : List Nat) (ws : List (List Nat × List Nat))
    (u m : Nat) : Bool :=
  bAnd(Nat.blt u ws.length, strictB (prodP Ys (ws.getD u ([], [])).1) (fun t =>
    bAnd(Nat.blt m (ws.getD u ([], [])).2.length,
      bIf(Nat.beq (zcK A Z EA (powR t (Nat.succ m))) (lget (ws.getD u ([], [])).2 m), false, true))))

@[expose] noncomputable def treeP (PP LL YP : Nat → Nat) : Nat → Nat → Nat
  | 0, _ => pidn 276 9
  | f + 1, j => nIf(Nat.beq j 0, pidn 276 9, pc (treeP PP LL YP f (PP j)) (YP (LL j)))

end CFSG.KC.E3

end

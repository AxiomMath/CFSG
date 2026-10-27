module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Kc3J4Dec2B1ZFrameNative
public import CFSG.Sporadic.J4.QT2LocVLNative
public import Std.Data.HashSet

public section

namespace CFSG.QuasithinUnique.A5

open CFSG.Sporadic.J4.Native CFSG.Sporadic.J4.QT CFSG.Sporadic.J4.QT2A CFSG.Sporadic.J4.QT2

@[expose] def zfGensOK : Bool :=
  zcLocWf && (List.range 3).all fun g => lenOK (zcGenTabs.getD g []) && actT (zcGenTabs.getD g []) 1 == 1

@[expose] def zfSeqT (s : List Nat) : List Nat :=
  s.foldr (fun g acc => compT (zcGenTabs.getD g []) acc) idT

@[expose] def zfSeqW (s : List Nat) : List Int := s.flatMap fun g => zcGenWords.getD g []

@[expose] def zfSeqR (s : List Nat) : Array V2 :=
  s.foldr (fun g acc => mulRows (wR (zcGenWords.getD g [])) acc) idRows

@[expose] def zfSeqRi (s : List Nat) : Array V2 :=
  s.foldl (fun acc g => mulRows (wR (invW (zcGenWords.getD g []))) acc) idRows

@[expose] def zfP : List (List (List Nat)) → List Nat → List Nat
  | lv :: C, t :: ts => compT (zfSeqT (lv.getD t [])) (zfP C ts)
  | _, _ => idT

@[expose] def zfW : List (List (List Nat)) → List Nat → List Int
  | lv :: C, t :: ts => zfSeqW (lv.getD t []) ++ zfW C ts
  | _, _ => []

@[expose] def zfChainOK : List (List (List Nat)) → List Nat → Bool
  | [], [] => true
  | lv :: C, b :: base => decide (b < 2048) && lv.head? == some [] && lv.all (·.all (· < 3)) &&
      C.all (fun lv' => lv'.all fun s => actT (zfSeqT s) b == b) &&
      decide (lv.map fun s => actT (zfSeqT s) b).Nodup && zfChainOK C base
  | _, _ => false

@[expose] def zfVs (Ts : List (List Nat)) : List (List Nat) :=
  (List.range 16).map fun m =>
    (List.range 4).foldl (fun acc i => if m.testBit i then compT acc (Ts.getD i []) else acc) idT

@[expose] def zfCons (Vs : List (List Nat)) (bs : List Nat) (P : List Nat) : Bool :=
  bs.all fun bj => bs.all fun bl => Vs.all fun v =>
    actT v bj != bl || actT P bl == actT v (actT P bj)

@[expose] def zfBtGo (Ts Vs : List (List Nat)) :
    List (List (List Nat)) → List Nat → List Nat → List Nat → List Nat → List (List Nat)
  | [], _, _, P, tup => if Ts.all (fun T => compT P T == compT T P) then [tup.reverse] else []
  | lv :: C, b :: base, bs, P, tup => (List.range lv.length).flatMap fun t =>
      if zfCons Vs (bs ++ [b]) (compT P (zfSeqT (lv.getD t []))) then
        zfBtGo Ts Vs C base (bs ++ [b]) (compT P (zfSeqT (lv.getD t []))) (t :: tup)
      else []
  | _ :: _, [], _, _, _ => []

@[expose] def zfBt (Ts : List (List Nat)) (C : List (List (List Nat))) (base : List Nat) :
    List (List Nat) :=
  zfBtGo Ts (zfVs Ts) C base [] idT []

@[expose] def zfMasks (Ts : List (List Nat)) (d : List Nat) : List Nat :=
  (List.range 2048).filter fun c =>
    (List.range 4).all fun i => (c ^^^ actT (Ts.getD i []) c) == d.getD i 0

@[expose] def zfSurvOK (ms : Fin 4 → Array V2) (Ts : List (List Nat)) (C : List (List (List Nat)))
    (surv sq D : List (List Nat)) (E : List Nat) (u : Nat) : Bool :=
  (sq.getD u []).all (· < 3) && (D.getD u []).all (· < 2048) && decide (E.getD u 0 < 2048) &&
    zfSeqT (sq.getD u []) == zfP C (surv.getD u []) &&
    (List.finRange 4).all (fun i =>
      eqRows (mulRows (mulRows (mulRows (ms i) (zfSeqR (sq.getD u []))) (ms i))
        (zfSeqRi (sq.getD u []))) (etaE ((D.getD u []).getD i 0))) &&
    ((zfMasks Ts (D.getD u [])).isEmpty ||
      (eqRows (mulRows (zfSeqR (sq.getD u [])) (zfSeqR (sq.getD u []))) (etaE (E.getD u 0)) &&
        (zfMasks Ts (D.getD u [])).all fun c =>
          (c ^^^ actT (zfSeqT (sq.getD u [])) c) == E.getD u 0))

@[expose] def zfI (Ts : List (List Nat)) (surv D : List (List Nat)) : List (Nat × Nat) :=
  (List.range surv.length).flatMap fun u => (zfMasks Ts (D.getD u [])).map fun c => (u, c)

@[expose] def zfRowsOf (sq : List (List Nat)) (q : Nat × Nat) : Array V2 :=
  mulRows (etaE q.2) (zfSeqR (sq.getD q.1 []))

@[expose] def chkZLightT (T₀ : Array V2) (gW : List Int) (Ts : List (List Nat)) : Bool :=
  Ts.length == 4 && eqRows (zConjBy gW T₀) (etaE 1) &&
    (List.finRange 4).all (fun i =>
      wfRows (zMs T₀ gW i) && eqRows (mulRows (zMs T₀ gW i) (zMs T₀ gW i)) idRows &&
        zTabOK (zMs T₀ gW i) (zMs T₀ gW i) (Ts.getD i [])) &&
    (List.finRange 4).all (fun i => (List.finRange 4).all fun j =>
      eqRows (mulRows (zMs T₀ gW i) (zMs T₀ gW j)) (mulRows (zMs T₀ gW j) (zMs T₀ gW i))) &&
    wfRows (zYR gW) &&
    (List.finRange 4).all fun i =>
      eqRows (mulRows (mulRows (zYR gW) (zMs T₀ gW i)) (zYiR gW))
        (zProdRows ((zS i).map (zMs T₀ gW)))

@[expose] def chkZFr (k : Nat) (T₀ : Array V2) (gW : List Int) (Ts : List (List Nat))
    (base : List Nat) (C : List (List (List Nat))) (surv sq D : List (List Nat)) (E : List Nat) :
    Bool :=
  chkZLightT T₀ gW Ts && zfChainOK C base && (C.map List.length).prod == 887040 &&
    zfBt Ts C base == surv && sq.length == surv.length && D.length == surv.length &&
    decide ((List.range surv.length).map fun u => zfSeqT (sq.getD u [])).Nodup &&
    (List.range surv.length).all (zfSurvOK (zMs T₀ gW) Ts C surv sq D E) &&
    decide (((zfI Ts surv D).filter fun q =>
      eqRows (mulRows (zfRowsOf sq q) (zYR gW)) (mulRows (zYR gW) (zfRowsOf sq q))).length ≤ k) &&
    decide (16 * k < (zfI Ts surv D).length)

end CFSG.QuasithinUnique.A5

end

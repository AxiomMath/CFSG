module

public import Certificates.Data.Kernel.LyReplay.Defs

public section

namespace CFSG.KC.LyDce

open CFSG.KC.LyReplay CFSG.Sporadic.Recognition.LyonsSims.LyFinal

@[expose] def rootC : Nat → List Nat
  | 0 => []
  | 1 => [10]
  | 2 => [10, 6, 10]
  | 3 => [10, 2, 10]
  | 4 => [10, 3, 6, 10, 0, 6, 4, 3, 6, 8]
  | _ => []

@[expose] def startW (i j : Nat) (r v a : List Nat) : List (Fin 6 × Bool) :=
  wordOf (rootC i ++ r ++ [10]) ++ derivInv (wordOf v) ++ derivInv (wordOf (rootC j)) ++
    derivInv (wordOf a)

@[expose] def stepOKD (bOK : List (Fin 6 × Bool) → Bool)
    (kR eR tR dR : List (List (Fin 6 × Bool) × List (Fin 6 × Bool))) (k : Nat)
    (old new : List (Fin 6 × Bool)) : Bool :=
  match k with
  | 0 => bOK (old ++ derivInv new)
  | 1 => ruleOK kR old new
  | 2 => ruleOK eR old new
  | 3 => ruleOK tR old new
  | 4 => ruleOK dR old new
  | _ => false

@[expose] def replayD (bOK : List (Fin 6 × Bool) → Bool)
    (kR eR tR dR : List (List (Fin 6 × Bool) × List (Fin 6 × Bool))) :
    List (Fin 6 × Bool) → List (Nat × Nat × List Nat × List Nat) → Bool
  | cur, [] => cur.isEmpty
  | cur, s :: ss =>
    stepOKD bOK kR eR tR dR s.2.1 (wordOf s.2.2.1) (wordOf s.2.2.2) &&
      match replaceAt cur s.1 (wordOf s.2.2.1) (wordOf s.2.2.2) with
      | some cur' => replayD bOK kR eR tR dR cur' ss
      | none => false

@[expose] def factOKD (bOK : List (Fin 6 × Bool) → Bool)
    (kR eR tR dR : List (List (Fin 6 × Bool) × List (Fin 6 × Bool))) (nt : Nat × Nat)
    (r v a : List Nat) (ss : List (Nat × Nat × List Nat × List Nat)) : Bool :=
  Nat.blt nt.1 5 && Nat.blt nt.2 5 && isBWord (wordOf r) && isBWord (wordOf v) &&
    isBWord (wordOf a) && replayD bOK kR eR tR dR (startW nt.1 nt.2 r v a) ss

@[expose] def dRuleOf (r : List (Fin 6 × Bool)) (m l : Nat) :
    List (List (Fin 6 × Bool) × List (Fin 6 × Bool)) :=
  [(r.take (m + l), derivInv (r.drop (m + l + m)) ++ r.take m),
   (r.take m ++ derivInv ((r.drop m).take l), r.drop (m + l + m) ++ r.take m)]

@[expose] def dShapeOK (r : List (Fin 6 × Bool)) (m l : Nat) : Bool :=
  r == r.take (m + l) ++ derivInv (r.take m) ++ r.drop (m + l + m)

@[expose] def dRulesOK (RD : List (List (Fin 6 × Bool))) (lens : List (Nat × Nat))
    (dR : List (List Nat × List Nat)) : Bool :=
  RD.length == lens.length && (RD.zip lens).all (fun p => dShapeOK p.1 p.2.1 p.2.2) &&
    rulesOf dR == (RD.zip lens).flatMap fun p => dRuleOf p.1 p.2.1 p.2.2

end CFSG.KC.LyDce

end

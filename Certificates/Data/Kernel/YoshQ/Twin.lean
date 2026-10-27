module

public import Certificates.Data.Kernel.YoshQ.TabN
public import CFSG.LocalAnalysis.EvenSporadicStandard.M12Std.YoshQCheck
public import CFSG.CharacterTheory.Blocks.Defs
public import CFSG.GH74.M12.Reductions
public import CFSG.LocalAnalysis.EvenSporadicStandard.Common
public import CFSG.LocalAnalysis.EvenSporadicStandard.M12Std.Data
public import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
public import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Isaacs.VII.lemma_7_7
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Basic

public section

namespace CFSG.KC.YoshQ

open CFSG.KC.Enum CFSG.KS CFSG.Sporadic.Th.Native CFSG.EvenSporadicStandard.M12Std.Yosh

@[expose] noncomputable def cjN (n w m t : Nat) : Nat := pmN n w (pmN n w m t) (invN n w m)

@[expose] noncomputable def comN (n w a b : Nat) : Nat :=
  pmN n w (pmN n w a b) (pmN n w (invN n w a) (invN n w b))

@[expose] noncomputable def memN (n w : Nat) (L : List Nat) (t : Nat) : Bool :=
  L.any fun s => eqN n w s t

@[expose] noncomputable def ctN (n w x y : Nat) : Bool := eqN n w (pmN n w x y) (pmN n w y x)

@[expose] noncomputable def commInN (n w c a b : Nat) : Bool :=
  eqN n w (comN n w a b) (pidn n w) || eqN n w (comN n w a b) c

@[expose] noncomputable def sqInN (n w c a : Nat) : Bool :=
  eqN n w (pmN n w a a) (pidn n w) || eqN n w (pmN n w a a) c

@[expose] noncomputable def apN (n w x i : Nat) : Nat := pg w (mask w) (x % 2 ^ (n * w)) i

@[expose] noncomputable def invoN (n w x : Nat) : Bool :=
  allIn 0 n fun i => apN n w x (apN n w x i) == i

@[expose] noncomputable def involN (n w x : Nat) : Bool := invoN n w x && !eqN n w x (pidn n w)

@[expose] noncomputable def letterN {m : Nat} (G Gi : Fin m → Nat) : Fin m × Bool → Nat
  | (i, true) => G i
  | (i, false) => Gi i

@[expose] noncomputable def evalN (n w : Nat) {m : Nat} (G Gi : Fin m → Nat)
    (wd : List (Fin m × Bool)) : Nat :=
  wd.foldr (fun l acc => pmN n w (letterN G Gi l) acc) (pidn n w)

@[expose] noncomputable def modelTN (n w k : Nat) (GS : List Nat) (wd : List (Fin k × Bool)) : Nat :=
  evalN n w (fun i : Fin k => GS.getD i.val 0) (fun i : Fin k => invN n w (GS.getD i.val 0)) wd

@[expose] noncomputable def nTN (GS : List Nat) (wd : List (Fin 9 × Bool)) : Nat :=
  modelTN 16 5 9 GS wd

@[expose] noncomputable def conjToN (NL : List Nat) (t₁ t₂ : Nat) : Bool :=
  NL.any fun m => eqN 16 5 (cjN 16 5 m t₁) t₂

@[expose] noncomputable def chainRunN (GS NL : List Nat) (α : Nat) :
    List (Fin 9 × Bool) → List (List Int × Bool) → Option (List (Fin 9 × Bool))
  | w, [] => some w
  | w, (W, dir) :: rest =>
    if conjToN NL (nTN GS w) (nTN GS (if dir then jOut α (swN W) else jIn α (swN W))) then
      chainRunN GS NL α (if dir then jIn α (swN W) else jOut α (swN W)) rest
    else none

@[expose] noncomputable def isSqNN (NL : List Nat) (t : Nat) : Bool :=
  NL.any fun z => eqN 16 5 (pmN 16 5 z z) t

@[expose] noncomputable def isCommNN (NL : List Nat) (t : Nat) : Bool :=
  (NL.filter (ctN 16 5 t)).any fun a => (NL.filter (ctN 16 5 t)).any fun b =>
    eqN 16 5 (comN 16 5 a b) t

@[expose] noncomputable def witnessNN (NL : List Nat) (t : Nat) : Bool := isSqNN NL t || isCommNN NL t

@[expose] noncomputable def goodRepsN (GS NL : List Nat) (α k : Nat) : List (List (Fin 9 × Bool)) :=
  (goodChains α k).filterMap fun c => chainRunN GS NL α (swN c.1) c.2

@[expose] noncomputable def badRepsN (GS NL : List Nat) (α k : Nat) : List (List (Fin 9 × Bool)) :=
  (badChains α k).filterMap fun c => chainRunN GS NL α (swN c.1) c.2

@[expose] noncomputable def fusionChainsN (GS NL : List Nat) (α k : Nat) : Bool :=
  (goodChains α k).all (fun c => c.1 == [6] && (chainRunN GS NL α (swN c.1) c.2).isSome) &&
  (badChains α k).all (fun c =>
    witnessNN NL (nTN GS (swN c.1)) && (chainRunN GS NL α (swN c.1) c.2).isSome)

@[expose] noncomputable def classN (NL : List Nat) (t : Nat) : List Nat := NL.map fun m => cjN 16 5 m t

@[expose] noncomputable def goodTabsN (GS NL : List Nat) (α k : Nat) : List Nat :=
  (goodRepsN GS NL α k).flatMap fun w => classN NL (nTN GS w)

@[expose] noncomputable def badTabsN (GS NL : List Nat) (α k : Nat) : List Nat :=
  (badRepsN GS NL α k).flatMap fun w => classN NL (nTN GS w)

@[expose] noncomputable def fusionCoverN (GS NL : List Nat) (α k : Nat) : Bool :=
  NL.all (fun y => !involN 16 5 y || memN 16 5 (goodTabsN GS NL α k) y ||
      memN 16 5 (badTabsN GS NL α k) y) &&
    (NL.filter (memN 16 5 (goodTabsN GS NL α k))).length == goodCount α

@[expose] noncomputable def normCenRestN (n w : Nat) (G GE L LE : List Nat) (c : Nat) : Bool :=
  LE.any (fun y => eqN n w c y) &&
  GE.all (fun x => G.any (fun x' => eqN n w x x')) &&
  G.all (fun m' => LE.all (fun y =>
    LE.any (fun y' => eqN n w (pmN n w m' y) (pmN n w y' m')) &&
      LE.any (fun y'' => eqN n w (pmN n w y m') (pmN n w m' y'')))) &&
  L.all (fun T => !(GE.all (fun y => ctN n w T y)) || LE.any (fun y => eqN n w T y)) &&
  LE.all (fun T => !(GE.all (fun y => ctN n w T y)) || eqN n w T (pidn n w) || eqN n w T c)

@[expose] noncomputable def ueN (GE GS : List Nat) (c : Nat) (lE lS : List Nat) : Bool :=
  GE.all (memN 16 5 lS) &&
  lS.all (fun s => GE.all fun g => memN 16 5 lE (cjN 16 5 s g)) &&
  memN 16 5 lE c &&
  lE.all (sqInN 16 5 c) &&
  lE.all (fun a => lE.all fun b => commInN 16 5 c a b) &&
  GS.any (fun a => GS.any fun b => !memN 16 5 lE (comN 16 5 a b)) &&
  (lS.filter fun y => !memN 16 5 lE y && sqInN 16 5 c y).all (fun y =>
    decide ((lE.filter fun x => commInN 16 5 c x y).length ≤ 32)) &&
  ((lS.filter fun y => !memN 16 5 lE y && sqInN 16 5 c y).map fun y =>
      (y, lE.map fun x => commInN 16 5 c x y)).all (fun p =>
    ((lS.filter fun y => !memN 16 5 lE y && sqInN 16 5 c y).map fun y =>
      (y, lE.map fun x => commInN 16 5 c x y)).all fun q =>
        p.2 != q.2 || memN 16 5 lE (pmN 16 5 (invN 16 5 p.1) q.1))

@[expose] noncomputable def esN (GE GS : List Nat) (c : Nat) (lE lS GN : List Nat) : Bool :=
  GS.all (ctN 16 5 c) &&
  lS.all (fun y => !GS.all (ctN 16 5 y) || eqN 16 5 y (pidn 16 5) || eqN 16 5 y c) &&
  lE.all (fun y => !GE.all (ctN 16 5 y) || eqN 16 5 y (pidn 16 5) || eqN 16 5 y c) &&
  GN.all (fun T => GE.all fun g => memN 16 5 lE (cjN 16 5 T g))

@[expose] noncomputable def l6N (NL good : List Nat) (e : Nat) (LE : List Nat) : Bool :=
  LE.any fun y1 =>
    (NL.filter (ctN 16 5 y1)).length == 128 &&
    LE.all fun T => !memN 16 5 good T || conjToN NL e T || conjToN NL y1 T

@[expose] noncomputable def l7FusionN (NL good : List Nat) (e u : Nat) (LE : List Nat) : Bool :=
  (LE.filter (memN 16 5 good)).length == 56 &&
    memN 16 5 good u && memN 16 5 good (pmN 16 5 u e) && memN 16 5 LE u &&
    memN 16 5 LE (pmN 16 5 u e) && ctN 16 5 e u &&
    LE.all fun T => !memN 16 5 good T || conjToN NL e T || conjToN NL u T ||
      conjToN NL (pmN 16 5 u e) T

@[expose] noncomputable def l7SylowN (c e u : Nat) (LE LS : List Nat) : Bool :=
  (LS.filter (ctN 16 5 e)).length == 128 && (LE.filter (ctN 16 5 e)).length == 64 &&
    (LS.filter (ctN 16 5 e)).all (fun y => !(LS.filter (ctN 16 5 e)).all (ctN 16 5 y) ||
      eqN 16 5 y (pidn 16 5) || eqN 16 5 y e || eqN 16 5 y c || eqN 16 5 y (pmN 16 5 e c)) &&
    (LE.filter (ctN 16 5 e)).all (fun y => !(LE.filter (ctN 16 5 e)).all (ctN 16 5 y) ||
      eqN 16 5 y (pidn 16 5) || eqN 16 5 y e || eqN 16 5 y c || eqN 16 5 y (pmN 16 5 e c)) &&
    (LS.filter (ctN 16 5 e)).all (fun y => memN 16 5 LE y || !sqInN 16 5 c y ||
      decide (2 * (LE.filter fun x => ctN 16 5 e x && commInN 16 5 c x y).length < 64)) &&
    [u, pmN 16 5 u e].all fun x =>
      (LS.filter (ctN 16 5 x)).length == 128 && (LE.filter (ctN 16 5 x)).length == 64

@[expose] noncomputable def l7AN (bad : List Nat) (c : Nat) (GA LA LE LS : List Nat) : Bool :=
  LA.all (fun a => LA.all fun b => ctN 16 5 a b) &&
    LA.all (fun a => eqN 16 5 (pmN 16 5 a a) (pidn 16 5)) &&
    GA.all (memN 16 5 LE) && GA.all (memN 16 5 bad) &&
    LE.all (fun y => !memN 16 5 bad y || memN 16 5 LA y) &&
    LS.all (fun y => !LA.all (commInN 16 5 c y) || memN 16 5 LE y) &&
    LS.all (fun y => !LA.all (ctN 16 5 y) || memN 16 5 LA y)

@[expose] noncomputable def l7VN (NL GV : List Nat) : Bool :=
  NL.all fun T => !GV.all (ctN 16 5 T) || eqN 16 5 (pmN 16 5 T T) (pidn 16 5)

@[expose] noncomputable def l8FactN (NL : List Nat) (e : Nat) : Bool :=
  (NL.filter (ctN 16 5 e)).length == 384 &&
    ((NL.filter (ctN 16 5 e)).filter fun y => eqN 16 5 (pmN 16 5 y (pmN 16 5 y y)) (pidn 16 5) &&
      !eqN 16 5 y (pidn 16 5)).all fun y =>
        (NL.filter (ctN 16 5 e)).any fun z =>
          !memN 16 5 [pidn 16 5, y, pmN 16 5 y y] (cjN 16 5 z y)

@[expose] noncomputable def l8ZNN (NL : List Nat) (c y0 : Nat) (LE : List Nat) : Bool :=
  LE.all fun y => !NL.all (commInN 16 5 c y) || eqN 16 5 y (pidn 16 5) || eqN 16 5 y c ||
    eqN 16 5 y y0 || eqN 16 5 y (pmN 16 5 y0 c)

end CFSG.KC.YoshQ

end

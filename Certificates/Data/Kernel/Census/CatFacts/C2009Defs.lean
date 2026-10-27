
module

public import CFSG.LocalAnalysis.ComponentClassification.CatFactsSmallConfP45Inputs
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsSmallQ3P45
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsSmallConfChecks2
public import Certificates.Data.Kernel.Census.CatFacts.PkWord

public section

namespace CFSG.Certificates.Kernel.CatFacts

open CFSG.ComponentClassification.CatFactsSmall.PSp43 CFSG.Certificates.Kernel.PkEnum

local notation "V45" => VP 45

@[expose] def lv0 (Q : RawSchreierDatum 45) : List (Fin 45 × StV 45) :=
  levelsV (strongV Q) Q.base 0

structure CA where
  q0 : List V45
  h : List V45
  e : List V45
  oz : List (List V45)
  ozt : List (List V45)
  cls1 : List (List V45)
  cls2 : List (List V45)
  icls1 : List (List V45)
  icls2 : List (List V45)
  z : V45
  tz : V45
  zt : V45
  g0i : V45
  lQQ : List (Fin 45 × StV 45)
  lQH : List (Fin 45 × StV 45)
  lQR : List (Fin 45 × StV 45)
  lQE : List (Fin 45 × StV 45)
  lQP : List (Fin 45 × StV 45)
  tA : List (List V45)
  tP : List (List V45)

@[expose] def vXYF : List V45 := [codeV x45, codeV y45, codeV f45]

@[expose] def conjCodes (S : List V45) (ws : List (List ℤ)) (s : V45) : List (List V45) :=
  ws.map fun w => invW (codesW S w) ++ s :: codesW S w

@[expose] def cA0 : CA where
  q0 := q0gens.map codeV
  h := cfHgens.map codeV
  e := cfEgens.map codeV
  oz := cfOz.map fun p => [codeV p.1]
  ozt := cfOzt.map fun p => [codeV p.1]
  cls1 := conjCodes vXYF cfCls1W (codeV s045)
  cls2 := conjCodes vXYF cfCls2W (codeV (s045 * cfZ * cfTau))
  icls1 := conjCodes (vXYF.take 2) cfICls1W (codeV cfZ)
  icls2 := conjCodes (vXYF.take 2) cfICls2W (codeV (cfZ * cfTau))
  z := codeV cfZ
  tz := codeV (cfTau * cfZ)
  zt := codeV (cfZ * cfTau)
  g0i := invV (codeV g045)
  lQQ := lv0 QQ45
  lQH := lv0 cfQH
  lQR := lv0 cfQR
  lQE := lv0 cfQE
  lQP := lv0 QP45
  tA := transL QA45
  tP := transL QP45

@[expose] def cls1P : List (Equiv.Perm (Fin 45)) := (conjCodes vXYF cfCls1W (codeV s045)).map pkpW

@[expose] def forceCA {β : Sort _} (k : CA → β) : β :=
  forceL cA0.q0 fun q0 => forceL cA0.h fun h => forceL cA0.e fun e => forceLL cA0.oz fun oz =>
  forceLL cA0.ozt fun ozt => forceLL cA0.cls1 fun cls1 => forceLL cA0.cls2 fun cls2 =>
  forceLL cA0.icls1 fun icls1 => forceLL cA0.icls2 fun icls2 => forceV cA0.z fun z =>
  forceV cA0.tz fun tz => forceV cA0.zt fun zt => forceV cA0.g0i fun g0i =>
  forceLv cA0.lQQ fun lQQ => forceLv cA0.lQH fun lQH => forceLv cA0.lQR fun lQR =>
  forceLv cA0.lQE fun lQE => forceLv cA0.lQP fun lQP => forceLL cA0.tA fun tA =>
  forceLL cA0.tP fun tP =>
    k ⟨q0, h, e, oz, ozt, cls1, cls2, icls1, icls2, z, tz, zt, g0i, lQQ, lQH, lQR, lQE, lQP, tA, tP⟩

@[expose] def conjW (w : List V45) (a : V45) : List V45 := w ++ a :: invW w

@[expose] def pA (C : CA) (w : List V45) : Bool :=
  (!(C.q0.all fun q => siftW C.lQQ (conjW w q)) || siftW C.lQQ w || siftW C.lQQ (C.g0i :: w)) &&
    (!(C.h.all fun h => siftW C.lQH (conjW w h)) || siftW C.lQR w) &&
    (!(C.e.all fun e => eqW (e :: w) (w ++ [e])) || siftW C.lQE w) &&
    (!isOneW (w ++ w) || siftW C.lQP w || memW w C.cls1 || memW w C.cls2)

@[expose] def nE (C : CA) (w : List V45) : Bool := C.e.all fun e => siftW C.lQE (conjW w e)

@[expose] def ozT (C : CA) (w : List V45) : Bool :=
  memW (invW w ++ C.z :: w) C.oz && memW (invW w ++ C.zt :: w) C.ozt

@[expose] def pP (C : CA) (w : List V45) : Bool :=
  !isOneW (w ++ w) || isOneW w || memW w C.icls1 || memW w C.icls2

@[expose] def chA : Nat := 5

@[expose] def chunkA (k : Nat) : Bool :=
  forceCA fun C => ((List.range chA).map (chA * k + ·)).all fun j => (blockW C.tA j).all (pA C)

@[expose] def allP : Bool :=
  forceCA fun C => (List.range (C.tP.headD []).length).all fun j => (blockW C.tP j).all (pP C)

@[expose] def cntZ : Nat × Nat :=
  forceCA fun C =>
    (((List.range (C.tA.headD []).length).map fun j =>
        ((blockW C.tA j).filter fun w => eqW (w ++ [C.tz]) (C.tz :: w)).length).sum,
      ((List.range (C.tA.headD []).length).map fun j =>
        ((blockW C.tA j).filter fun w => eqW (w ++ [C.z]) (C.z :: w)).length).sum)

@[expose] def cntE : Nat × Bool :=
  forceCA fun C =>
    (((List.range (C.tA.headD []).length).map fun j => ((blockW C.tA j).filter (nE C)).length).sum,
      (List.range (C.tA.headD []).length).all fun j => ((blockW C.tA j).filter (nE C)).all (ozT C))

end CFSG.Certificates.Kernel.CatFacts

end

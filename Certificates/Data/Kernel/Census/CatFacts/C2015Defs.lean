
module

public import CFSG.LocalAnalysis.ComponentClassification.CatFactsSmallQ3P45Inputs
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsSmallPSp43Model
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsSmallArrChecks
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsSmallQ3Gen
public import CFSG.GH74.KGroups.Checks3
public import Certificates.Data.Kernel.Census.CatFacts.PkWord

public section

namespace CFSG.Certificates.Kernel.CatFacts

open CFSG.ComponentClassification.CatFactsSmall.PSp43 CFSG.Certificates.Kernel.PkEnum
  CFSG.Sporadic.Schreier

local notation "V45" => VP 45

@[expose] def prodW {n : Nat} (w : List (VP n)) : VP n := w.foldr mulV (oneV n)

@[expose] def cubeV {n : Nat} (u : VP n) : VP n := forceV u fun u => mulV u (mulV u u)

@[expose] def pow45 {n : Nat} (u : VP n) : VP n :=
  forceV (cubeV (cubeV u)) fun d => mulV d (mulV d (mulV d (mulV d d)))

@[expose] def oddNW : Bool :=
  forceLL (transL QL45) fun T => (productsW T).all fun x => isOneW x ||
    !isOneW [pow45 (prodW x)] ||
      (productsW T).any fun c => !isOneW [pow45 (prodW (x ++ c ++ invW x ++ invW c))]

structure C15 where
  tA : List (List V45)
  tP : List (List V45)
  lP : List (Fin 45 × StV 45)
  s0 : V45
  cj : List (List V45)

@[expose] def gXYF : List V45 := [codeV (tab x45), codeV (tab y45), codeV (tab f45)]

@[expose] def c15 : C15 where
  tA := transL QA45
  tP := transL QP45
  lP := levelsV (strongV QP45) QP45.base 0
  s0 := codeV s045
  cj := admWords.map fun w => codesW gXYF w ++ codeV s045 :: invW (codesW gXYF w)

@[expose] def cnt2015 : Nat × Nat × Nat × Nat :=
  forceLL c15.tA fun tA => forceLL c15.tP fun tP => forceV c15.s0 fun s0 =>
    ((tA.headD []).length, (tP.headD []).length,
      ((List.range 45).map fun j =>
        ((blockW tA j).filter fun w => eqW (w ++ [s0]) (s0 :: w)).length).sum,
      ((List.range 45).map fun j =>
        ((blockW tP j).filter fun w => eqW (w ++ [s0]) (s0 :: w)).length).sum)

end CFSG.Certificates.Kernel.CatFacts

end

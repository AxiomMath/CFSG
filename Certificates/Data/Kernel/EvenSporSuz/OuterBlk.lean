module

public import Certificates.Data.Kernel.EvenSporSuz.Outer
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoSuz.OuterCheck

public section

namespace CFSG.KC.EvenSporSuz

open CFSG.EvenSporadicStandard.TwoSuz

@[expose] def subR (M I : List (List ℕ)) (n : ℕ) (w : ℕ → List ℤ) : List (List ℕ) :=
  (List.range n).map fun s => evalR M I ((w s).map zCode)

@[expose] def subRI (M I : List (List ℕ)) (n : ℕ) (w : ℕ → List ℤ) : List (List ℕ) :=
  (List.range n).map fun s => evalR M I ((outerInvW (w s)).map zCode)

@[expose] def blockW (ws : List (List ℤ)) (p K M : ℕ) : OuterBlock :=
  ⟨(List.range K).map fun s => ws.getD (p + 1 + s) [],
    (List.range M).map fun j => ws.getD (p + 1 + K + 2 * j) [],
    (List.range M).map fun j => ws.getD (p + 2 + K + 2 * j) [],
    (List.range K).map fun s => ws.getD (p + 1 + K + 2 * M + s) [],
    ws.getD (p + 1 + K + 2 * M + K) []⟩

end CFSG.KC.EvenSporSuz

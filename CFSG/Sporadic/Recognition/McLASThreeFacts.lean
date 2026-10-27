module

public import CFSG.Sporadic.Recognition.McLASSpec

public section

namespace CFSG.Sporadic.Recognition.McLAS

open Subgroup CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier
  CFSG.Sporadic.SmallOddCore CFSG.Sporadic.SmallOddCore.Native

structure ThreeFacts : Prop where
  row₁ : ElemFacts 275 mclP 3 threeRow₁
  row₂ : ElemFacts 275 mclP 3 threeRow₂
  cover : ∀ y ∈ mclP, orderOf y = 3 →
    (∃ g ∈ mclP, y = g * tp 275 threeRow₁.rep * g⁻¹) ∨
      ∃ g ∈ mclP, y = g * tp 275 threeRow₂.rep * g⁻¹
  enum₁ : ∀ y ∈ mclP ⊓ centralizer ({tp 275 threeRow₁.rep} : Set (Equiv.Perm (Fin 275))),
    ∃ k < (mulClosureH 275 threeRow₁.centGens.toArray 924000).1.size,
      Rep 275 (mulClosureH 275 threeRow₁.centGens.toArray 924000).1[k]! y

end CFSG.Sporadic.Recognition.McLAS

end

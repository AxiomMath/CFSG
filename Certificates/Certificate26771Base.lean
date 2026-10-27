
module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.TwoHSData.ClassFacts
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.TwoHSData.ClassData
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.TwoHSData.Elems
import Certificates.Kernel.HN1408.Cz1TData

@[expose] public section

open CFSG.EvenSporadicStandard.HNRecog

namespace Certificates

structure InvClassFacts : Prop where
  z : ClassSpec classz elemZ
  az : ClassSpec classaz (elemA * elemZ)
  b : ClassSpec classb elemB
  z₁ : ClassSpec classz₁ elemZ₁
  not_isConj : ∀ i j : Fin 5, i ≠ j →
    ¬ IsConj (![pA, pZ, pA * pZ, pB, pZ₁] i) (![pA, pZ, pA * pZ, pB, pZ₁] j)
  cover : ∀ x : ↥P1408, orderOf x = 2 → ∃ i : Fin 5, IsConj (![pA, pZ, pA * pZ, pB, pZ₁] i) x

end Certificates

public section

open CFSG.EvenSporadicStandard.HNRecog CFSG.KD.HN1408

namespace Certificates

end Certificates

module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight89KCoverPG
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight89KModel
import Certificates.Kernel.Eight89K.Facts

public section

namespace Certificates

open CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.KInputs Subgroup in
theorem certificate1491002 : (∀ i j k l, i < 2 → j < 2 → k < 2 → l < 3 → Finite (CoverPG 6 i j k l) ∧
      Nat.card (CoverPG 6 i j k l) ≤ (if i = j then 2160 else 1080) / (if l = 0 then 1 else 3)) ∧
    (orderOf s6 = 30 ∧ a6 ^ 2 = c6 ^ 3 ∧ b6 ^ 4 = c6 ^ 3 ∧ (a6 * b6 * b6) ^ 5 = 1 ∧
      c6 ∈ center model6) :=
  ⟨CFSG.KC.Eight89K.cover6_facts, CFSG.KC.Eight89K.model6_facts⟩

end Certificates

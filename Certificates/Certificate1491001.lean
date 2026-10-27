module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight89KCoverPG
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight89KModel
import Certificates.Kernel.Eight89K.Facts

public section

namespace Certificates

open CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.KInputs Subgroup in
theorem certificate1491001 : (∀ k l, k < 2 → l < 3 → Finite (CoverPG 3 0 0 k l) ∧
      Nat.card (CoverPG 3 0 0 k l) ≤ if l = 0 then 1080 else 360) ∧
    (orderOf s3 = 15 ∧ a3 ^ 2 = 1 ∧ b3 ^ 4 = 1 ∧ (a3 * b3 * b3) ^ 5 = 1 ∧ c3 ∈ center model3) :=
  ⟨CFSG.KC.Eight89K.cover3_facts, CFSG.KC.Eight89K.model3_facts⟩

end Certificates

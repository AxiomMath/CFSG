module

public import CFSG.RankThree.PartTwo.KFacts.KP4Gen
import Certificates.Kernel.R148Dc.M22CFacts

public section

namespace Certificates

open CFSG.RankThree.PartTwo.KFacts.KP4 in
theorem certificate148010 : ∀ Z : Subgroup CFSG.RankThree.PartTwo.KFacts.KP4.G22, CFSG.RankThree.PartTwo.KFacts.KP4.P0 ⊔ CFSG.RankThree.PartTwo.KFacts.KP4.V 0 ≤ Z →
    Z = ⊤ ∨ Z = CFSG.RankThree.PartTwo.KFacts.KP4.A 0 ∨ Z = CFSG.RankThree.PartTwo.KFacts.KP4.A 1 ∨ Z = Subgroup.normalizer (R 0 : Set CFSG.RankThree.PartTwo.KFacts.KP4.G22) ∨ Nat.card Z ∣ 576 := by
  exact CFSG.KD.R148Dc.M22C.m22c_facts

end Certificates

module

public import CFSG.LocalAnalysis.StandardType.GGNbrFieldFixD4Defs
public import CFSG.LocalAnalysis.StandardType.GGNbrFieldFixRows
public import CFSG.LocalAnalysis.StandardType.GGNbrFieldFixNsRows

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

theorem largeEvenLabelAll_rowPlain_d4A {lab : LargeEvenLabel} (ht : lab.tag = .D)
    (hr : lab.rank = 4) (hq : 3 ∣ 2 ^ lab.n - 1) :
    LargeEvenLabelAll lab (GGNbrWeylRowPlain 3 4) := by
  have h := largeEvenLabelAll_rowPlain_omegaPlus Nat.prime_three (by norm_num)
    (lab := lab) ⟨ht, by omega, hq⟩
  rwa [hr] at h

section Rows

theorem largeEvenLabelAll_rowPlain_d4B {lab : LargeEvenLabel} (ht : lab.tag = .D)
    (hr : lab.rank = 4) (hn2 : 2 ≤ lab.n) (hq : 3 ∣ 2 ^ lab.n + 1) :
    LargeEvenLabelAll lab (GGNbrWeylRowPlain 3 3) :=
  (largeEvenLabelAll_and
    (largeEvenLabelAll_innLift_omegaPlusNs Nat.prime_three (by norm_num)
      ⟨ht, by omega, hn2, hq⟩)
    (largeEvenLabelAll_torusIrredSC_orthNs Nat.prime_three ⟨Or.inl ht, by omega, hq⟩)).mono
    fun _ _ _ _ ⟨⟨hi, hl⟩, hs⟩ =>
      ⟨hi, hl, fun _ _ => ggTorusNoLine_of_ggTorusIrredSC Nat.prime_three hs⟩

end Rows

end CFSG.StandardType

end

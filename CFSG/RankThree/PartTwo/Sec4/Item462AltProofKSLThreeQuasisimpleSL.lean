module

public import CFSG.RankThree.PartTwo.Sec4.LThreePiKind

public section

namespace CFSG.RankThree.PartTwo.Sec4.Item462AltProof.KSLThree

open CFSG CFSG.RankThree.PartTwo.Sec4

theorem isQuasisimple_slPi {π : Bool} {p f : ℕ} {K : Type} [Field K] (hK : PiField π p f K)
    (hq2 : 2 < p ^ f) : IsQuasisimple (slPi π 3 (p ^ f) K) := by
  haveI := hK.finite
  haveI : Fact p.Prime := ⟨hK.prime⟩
  cases π
  · have hnq : ((3 : ℕ), p ^ f) ≠ (3, 2) := fun h => by
      have h2 := congrArg Prod.snd h
      simp only at h2
      omega
    exact (CFSG.LieType.Universal.Unitary.isQuasisimple_statedSU_of_card hK.card le_rfl hnq).1
  · exact CFSG.LieType.Universal.Unitary.isQuasisimple_of_mulEquiv
      (statedSLEquiv 3 K).symm (CFSG.LieType.Universal.SpecialLinear.isQuasisimple 2 K le_rfl)

end CFSG.RankThree.PartTwo.Sec4.Item462AltProof.KSLThree

end

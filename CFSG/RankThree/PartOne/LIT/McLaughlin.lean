module

public import CFSG.RankThree.PartOne.LIT.KF127
public import CFSG.RankThree.PartOne.LIT.McPencil
public import CFSG.RankThree.PartOne.LIT.McSlC
public import CFSG.RankThree.PartOne.LIT.McSpFinal

public section

namespace CFSG.RankThree.PartOne

open CFSG.RankThree.PartOne.LIT

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem mclaughlinFour : McLaughlinFour := by
  intro p _ hp5 V _ _ _ hdim H hirr hgen
  by_cases hua : HasUniqueAxes H
  · exact Or.inr (sp_branch H hp5 hdim hirr hgen hua)
  · obtain ⟨c, hc⟩ := exists_fullCenter_of_not_hasUniqueAxes H hdim hirr hgen hua
    refine Or.inl fun g => ⟨fun hg => ?_, det_one_mem_of_fullCenter H hirr hc g⟩
    obtain ⟨S, hS, hHS⟩ := hgen
    have hker : H ≤ (LinearEquiv.det : (V ≃ₗ[ZMod p] V) →* (ZMod p)ˣ).ker := by
      rw [hHS]
      exact (Subgroup.closure_le _).mpr fun t ht => by
        obtain ⟨v, f, h⟩ := hS t ht
        exact isTransvectionWith_det h
    have h1 := hker hg
    rw [MonoidHom.mem_ker] at h1
    rw [← LinearEquiv.coe_det, h1]
    simp

theorem kf127 : KF127 :=
  kf127_of_mclaughlinFour mclaughlinFour

end CFSG.RankThree.PartOne

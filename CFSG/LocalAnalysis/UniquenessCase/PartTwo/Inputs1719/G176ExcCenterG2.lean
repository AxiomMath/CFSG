module

public import CFSG.Milestones.ASVolI.F411.aSwG2NCenter

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.G176Exc

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.GH74.GLS.IVK.Proofs2.Ivk47

variable {K : Type} [Field K]

theorem card_center_posUnipotent_G2 [Finite K] (h3 : (3 : K) ≠ 0) :
    Nat.card ↥(Subgroup.center ↥(posUnipotent .G2 K)) = Nat.card K := by
  symm
  refine Nat.card_eq_of_bijective (fun t => ⟨⟨Xc t, Xc_mem t⟩, Subgroup.mem_center_iff.2
    fun g => Subtype.ext (Xc_central t g g.2).eq.symm⟩) ⟨fun s t h => Xc_injective ?_, ?_⟩
  · exact congrArg (fun z : ↥(Subgroup.center ↥(posUnipotent .G2 K)) =>
      ((z : ↥(posUnipotent .G2 K)) : ModGL .G2 K)) h
  · rintro ⟨⟨z, hzU⟩, hz⟩
    obtain ⟨t, rfl⟩ := CFSG.ASVolI.burnsideF411a_g2_eq_Xc_of_central h3 hzU fun h hh =>
      congrArg Subtype.val (Subgroup.mem_center_iff.1 hz ⟨h, hh⟩)
    exact ⟨t, rfl⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.G176Exc

module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.RankThree.LocalRank.SelectorCases
public import CFSG.RankThree.PartTwo.Sec13.Item13Res7ProofLinAlg
public import CFSG.RankThree.PartTwo.Sec13.Item13Res7ProofTools
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44Groups

public section

namespace CFSG.RankThree.PartTwo.Sec13.F135Last

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Sec4

@[expose] noncomputable def r5f_map {Q : Type} [Group Q] (R : Subgroup Q) [R.Normal]
    (J : Subgroup (Q ⧸ R)) : ↥(J.comap (QuotientGroup.mk' R)) →* ↥J ⧸ Subgroup.center ↥J :=
  (QuotientGroup.mk' (Subgroup.center ↥J)).comp
    (((QuotientGroup.mk' R).comp (J.comap (QuotientGroup.mk' R)).subtype).codRestrict J
      (fun h => h.2))

theorem r5f_map_surjective {Q : Type} [Group Q] (R : Subgroup Q) [R.Normal]
    (J : Subgroup (Q ⧸ R)) : Function.Surjective (r5f_map R J) := by
  intro x
  obtain ⟨⟨j, hj⟩, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center ↥J) x
  obtain ⟨m, rfl⟩ := QuotientGroup.mk'_surjective R j
  exact ⟨⟨m, hj⟩, rfl⟩

end CFSG.RankThree.PartTwo.Sec13.F135Last

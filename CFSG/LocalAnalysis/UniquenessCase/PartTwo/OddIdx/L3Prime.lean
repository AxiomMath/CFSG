module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.OddIdx.Core
public import CFSG.Quasithin.EmptyFaithful.A38c15IrrClose
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1R925Pure

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.OddIdx

open CFSG.Quasithin CFSG.Quasithin.A38c15 CFSG.Open Subgroup
open CFSG.Blueprint (LieModel)

set_option linter.unusedSectionVars false

section Certified


theorem oddIdxProp_psl3_prime {K : Type} [Group K] [Finite K] {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hq : p % 3 = 2) (hL : LieModel K .PSL 3 p 1) : OddIdxProp K := by
  intro N Y D hN hodd hD hDY hYN hnorm hY hNK
  haveI : Fact p.Prime := ⟨hp⟩
  have hX : IsPSL 3 p 1 K := hL.statedClassicalModel (by decide)
  have hcore : SylowCore p K := sylowCore_of_isPSL3 gl2OddIndex sl3OddIrr hp2 hX
  have hp3 : p ≠ 3 := by rintro rfl; norm_num at hq
  rcases hcore N hodd hN with hsolv | hlevi
  · haveI : Group.IsSolvable ↥N := hsolv
    have hYsolv : Group.IsSolvable ↥Y :=
      Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hYN)
        (Subgroup.inclusion_injective hYN)
    obtain ⟨D', hD'⟩ := hY.exists_card_three
    haveI : Nontrivial D' := Finite.one_lt_card_iff_nontrivial.mp (by rw [hD']; norm_num)
    haveI : Nontrivial ↥Y := D'.subtype_injective.nontrivial
    haveI : Group.IsPerfect ↥Y := ⟨hY.1⟩
    exact (Group.IsPerfect.not_isSolvable ↥Y hYsolv).elim
  · obtain ⟨hp5, hY5⟩ := conclusion_of_levi hp hp2 hp3 hYN hY hNK hlevi
    subst hp5
    exact ⟨hL, hY5⟩

end Certified

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.OddIdx

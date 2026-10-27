module

public import CFSG.RankThree.PartOne.SEITZ2.Fine
public import CFSG.RankThree.PartOne.SEITZ2.OmegaF2
public import CFSG.RankThree.PartOne.SEITZ4.SpPair
public import CFSG.RankThree.PartOne.SEITZ5.UPair
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.RankThree.PartOne.SEITZ2

open CFSG.RankThree.PartOne.CTP

theorem fieldAutOmega8m_of_pair (h : SubfieldPairOmega8m) : FieldAutOmega8m :=
  fun _ hq _ => extSeitzAtOuter_twistedD_of_pair h hq

section

@[expose] def SeitzFieldAutFineNarrow : Prop :=
  SubfieldPairOmega8mSmall ∧ SubfieldPairG2 ∧ SubfieldPairD4 ∧ SubfieldPairSz ∧ SubfieldPairReeF4

theorem seitzFieldAutFine_of_narrow (h : SeitzFieldAutFineNarrow) : SeitzFieldAutFine :=
  seitzFieldAutFine_of_pairs
    ⟨subfieldPairSU_three,
      subfieldPairSU_of_f2 (by norm_num) (SEITZ5.subfieldPairSUF2_of_four_le (by norm_num)),
      subfieldPairSU_of_f2 (by norm_num) (SEITZ5.subfieldPairSUF2_of_four_le (by norm_num)),
      SEITZ4.subfieldPairSp (by norm_num), SEITZ4.subfieldPairSp (by norm_num),
      fieldAutOmega8m_of_pair (subfieldPairOmega8m_of_small h.1), h.2.1, h.2.2.1, h.2.2.2.1,
      h.2.2.2.2⟩

end

end CFSG.RankThree.PartOne.SEITZ2

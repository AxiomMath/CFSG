module

public import CFSG.RankThree.PartTwo.Sec15.Gagen1521Defs
import CFSG.RankThree.PartTwo.Sec15.Gagen1521Four
import CFSG.RankThree.PartTwo.Sec15.ONanKS1424CoreThm
import CFSG.RankThree.PartTwo.Sec15.ONanKS1424CoreEvenM
import CFSG.RankThree.PartTwo.Sec15.KSL3TwoProofSub

public section

namespace CFSG.RankThree.PartTwo.Sec15

open CFSG CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec14

theorem ks1521SubTwoCore : KS1521SubTwoCore := by
  intro X _ _ n hn hiso K N _ hN2 r f _ hKN
  by_contra hne
  obtain ⟨π, F, _, hF, -, ⟨M⟩⟩ := exists_lmodel_gen hn hiso
  have : IsSimpleGroup (↥K ⧸ N) := (KSL3Two.isSimpleGroup_and_not_isSolvable hKN).1
  obtain ⟨t, ht⟩ := exists_orderOf_eq_four_of_isLThreeEpsAt hKN
  have hR1 : N.map K.subtype ≠ ⊥ := fun h =>
    hne ((Subgroup.map_eq_bot_iff_of_injective N K.subtype_injective).mp h)
  have hNK : (N.map K.subtype).subgroupOf K = N :=
    Subgroup.map_subtype_inj.mp (Subgroup.map_subgroupOf_eq_of_le (Subgroup.map_subtype_le N))
  have hH : K ≤ Subgroup.normalizer ((N.map K.subtype : Subgroup X) : Set X) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer (Subgroup.map_subtype_le N)).mp
      (by rw [hNK]; infer_instance)
  exact KS1424.core_even hF M hR1 (hN2.map K.subtype) hH ht (QuotientGroup.mk' N)
    (QuotientGroup.mk'_surjective N)

end CFSG.RankThree.PartTwo.Sec15

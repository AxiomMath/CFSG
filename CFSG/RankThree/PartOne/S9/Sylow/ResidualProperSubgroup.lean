module

public import CFSG.RankThree.PartOne.S9.StatementsSylow
public import CFSG.RankThree.PartOne.S9.Sylow.ResidualBridge
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProperGroups

public section

namespace CFSG.RankThree.PartOne

open CFSG CFSG.Assembly CFSG.Assembly.RankThreeEven CFSG.RankThree.LocalRank
  CFSG.RankThree.GroupTheory

theorem properSubgroupResidual_of (h8 : SectionEightResidualBound) : ProperSubgroupResidual := by
  intro G _ _ hKP he p hp hp3 B hB hBcard K hBK hKtop b hbB hb1
  have := hB
  have : Fact p.Prime := ⟨hp⟩
  have hKgrp : CFSG.IsKGroup K :=
    CFSG.ComponentClassification.CatalogueKProper.proper_subgroup_isKGroup hKP K hKtop
  have heK : evenRank K ≤ 3 := (Sec9A.evenRank_subgroup_le K).trans he
  have hE : IsElementaryAbelian p (B.subgroupOf K) := IsElementaryAbelian.subgroupOf hBK
  have hEcard : Nat.card (B.subgroupOf K) = p ^ 2 := by
    rw [← hBcard]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBK).toEquiv
  have ht1 : (⟨b, hBK hbB⟩ : K) ≠ 1 := fun h => hb1 (congrArg Subtype.val h)
  obtain ⟨-, hres⟩ := h8 K hKgrp heK p hp hp3 (B.subgroupOf K) hE hEcard ⟨b, hBK hbB⟩ hbB ht1
  rw [Sec9A.residualGroup_eq_map hp hBK hbB hb1]
  exact (Sec9A.twoPrimeResidual_map_le_of_injective K.subtype K.subtype_injective _).trans
    (Subgroup.map_mono hres)

end CFSG.RankThree.PartOne

module

public import CFSG.RankThree.PartTwo.Sec18.Item185Leaves
public import CFSG.LocalAnalysis.RankThreeTheoremC.OutCyclicThree
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanIdentCharPBasic

public section

namespace CFSG.RankThree.PartTwo.Sec18.Item185Proof

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Late
open CFSG.ABGLocalTools (IsSylowOf)
open CFSG.Assembly (IsElemAbelian)
open CFSG.RankThree.PartTwo.Sec19.SimsC198 (RankHyp)
open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner centerQuotientOuterHom
  centerQuotient_outer_injective)

section Certified

theorem leafF1_holds : LeafF1 := by
  intro X _ _ hR h3 D hD hD9
  by_contra hDbot
  have hperf : Group.IsPerfect X := hR.quasisimple.1
  have hsimple : IsSimpleGroup (X ⧸ Subgroup.center X) := hR.quasisimple.2.1
  have hnab : ∃ a b : X ⧸ Subgroup.center X, a * b ≠ b * a := hR.quasisimple.2.2
  obtain ⟨i, ⟨e⟩⟩ : Assembly.InCatalog (X ⧸ Subgroup.center X) :=
    KCore.KGroupAllSimple.catalogue_self (C := Assembly.InCatalog)
      Assembly.inCatalog_isoInvariant (hR.kGroup.quotient _)
  have hcat : CFSG.Open.IsCatalogGroup (X ⧸ Subgroup.center X) := ⟨i, ⟨e⟩⟩
  obtain ⟨P⟩ : Nonempty (Sylow 3 X) := inferInstance
  have hP : IsCyclic (P : Subgroup X) :=
    CFSG.AGLEmbedding.isCyclic_sylow_of_pRank_le_one Nat.prime_three (by norm_num) h3 P
  have hT : IsCyclic ((P.mapSurjective (QuotientGroup.mk'_surjective (Subgroup.center X)) :
      Sylow 3 (X ⧸ Subgroup.center X)) : Subgroup (X ⧸ Subgroup.center X)) := by
    rw [Sylow.coe_mapSurjective]
    exact isCyclic_of_surjective _
      ((QuotientGroup.mk' (Subgroup.center X)).subgroupMap_surjective _)
  have hout := CFSG.LocalAnalysis.RankThreeTheoremC.kFactOutCyclic_holds
    (X ⧸ Subgroup.center X) hsimple hnab hcat 3 Nat.prime_three (by norm_num) _ hT
  have hOut := CFSG.SectionRank.pRank_top_le_of_injective (p := 3) (by norm_num)
    (centerQuotientOuterHom X) (centerQuotient_outer_injective X)
  have hf : Function.Injective ((QuotientGroup.mk' (inner X)).comp D.subtype) := by
    rw [injective_iff_map_eq_one]
    intro a ha
    have h1 : (a : MulAut X) ∈ inner X := (QuotientGroup.eq_one_iff _).mp ha
    have h2 : (a : MulAut X) ∈ D ⊓ innerAut X := ⟨a.2, h1⟩
    rw [hDbot] at h2
    exact Subtype.ext (Subgroup.mem_bot.mp h2)
  have hcomm : ∀ a b : ↥D, a * b = b * a := by
    have := hD.1
    exact fun a b => mul_comm' a b
  have hpow : ∀ a : ↥D, a ^ 3 = 1 := fun a => Subtype.ext (by simpa using hD.2 a a.2)
  have hcard : Nat.card ↥D = 3 ^ 2 := by rw [hD9]; norm_num
  have h2 : 2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup (Outer X)) :=
    CFSG.SectionRank.le_pRank_of_injective (by norm_num) hcomm hpow hcard _ hf le_top
  omega

end Certified

end CFSG.RankThree.PartTwo.Sec18.Item185Proof

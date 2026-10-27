module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section19.Defs
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Rank13
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.Quasithin.Background.F1Models

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S19

open Subgroup CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

theorem index_barOfInter {M L : Subgroup G} (hO2 : pCoreOf 2 L ≤ M) :
    (barOfInter M L).index = (L ⊓ M).relIndex L := by
  have hsub : (pCoreOf 2 L).subgroupOf L = CFSG.pCore 2 ↥L := by
    rw [pCoreOf, Subgroup.subgroupOf,
      Subgroup.comap_map_eq_self_of_injective L.subtype_injective]
  have hker : (QuotientGroup.mk' (CFSG.pCore 2 ↥L)).ker ≤ (L ⊓ M).subgroupOf L := by
    intro x hx
    rw [QuotientGroup.ker_mk'] at hx
    rw [← hsub] at hx
    exact Subgroup.mem_subgroupOf.mpr ⟨x.2, hO2 hx⟩
  unfold barOfInter
  exact Subgroup.index_map_eq ((L ⊓ M).subgroupOf L) (QuotientGroup.mk'_surjective _) hker

theorem map_opp_inter_eq_opp_barOfInter (M L : Subgroup G) :
    ((Opp 2 (L ⊓ M)).subgroupOf L).map (QuotientGroup.mk' (CFSG.pCore 2 ↥L)) =
      Opp 2 (barOfInter M L) := by
  have h2 : Nat.Prime 2 := Nat.prime_two
  have hOpp : (Opp 2 (L ⊓ M)).subgroupOf L =
      CFSG.RankThree.PartOne.pElementSubgroup 2 ((L ⊓ M).subgroupOf L) := by
    have h1 := CFSG.LocalAnalysis.UniquenessCase.PartTwo.s13_pElementSubgroup_map h2 L.subtype
      ((L ⊓ M).subgroupOf L)
    rw [Subgroup.map_subgroupOf_eq_of_le inf_le_left] at h1
    show (CFSG.RankThree.PartOne.pElementSubgroup 2 (L ⊓ M)).subgroupOf L = _
    rw [← h1]
    exact Subgroup.comap_map_eq_self_of_injective L.subtype_injective _
  rw [hOpp, CFSG.LocalAnalysis.UniquenessCase.PartTwo.s13_pElementSubgroup_map h2
    (QuotientGroup.mk' (CFSG.pCore 2 ↥L)) ((L ⊓ M).subgroupOf L)]
  rfl

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S19

module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S21a
import CFSG.Adapters.LieModelSimple
import CFSG.Blueprint.LieModelAPI

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.RankOneBorel

open Subgroup
open CFSG.Blueprint (LieModel)

theorem lieModel_quot_center_of_isSp4 {Y : Type} [Group Y] [Finite Y] {n : ℕ}
    (hY : IsSp4 Y n) (hperf : _root_.commutator Y = ⊤) :
    LieModel (Y ⧸ center Y) .PSp 2 2 n := by
  haveI : Group.IsPerfect Y := ⟨hperf⟩
  haveI : IsSimpleGroup Y :=
    CFSG.Blueprint.LieModel.isSimpleGroup_of_mem_classicalTags (by decide) hY
  have hnc : ¬ IsMulCommutative Y := Group.IsPerfect.not_isMulCommutative Y
  exact CFSG.Blueprint.LieModel.quotient_center
    (TauCeti.IsSimpleGroup.center_eq_bot_of_not_isMulCommutative hnc) hY

variable {G : Type} [Group G] [Finite G]

theorem graph_map_eq {L J : Subgroup G} {t : G} (htJ : t ∈ normalizer (J : Set G))
    (htL : t ∈ normalizer (L : Set G)) {θ : MulAut (Bar2 L ⧸ center (Bar2 L))}
    (hθ : InducedQuot L t θ) :
    ((barImage L J).map (QuotientGroup.mk' (center (Bar2 L)))).map θ.toMonoidHom =
      (barImage L J).map (QuotientGroup.mk' (center (Bar2 L))) := by
  classical
  refine le_antisymm ?_ ?_
  · rintro _ ⟨y, hy, rfl⟩
    obtain ⟨z, hz, rfl⟩ := Subgroup.mem_map.1 hy
    obtain ⟨l, hl, rfl⟩ := Subgroup.mem_map.1 hz
    have hjJ : (l : G) ∈ J := Subgroup.mem_subgroupOf.1 hl
    let j' : ↥L := ⟨t * (l : G) * t⁻¹,
      (Subgroup.mem_normalizer_iff.mp htL (l : G)).mp l.2⟩
    have hj'J : (j' : G) ∈ J := (Subgroup.mem_normalizer_iff.mp htJ (l : G)).mp hjJ
    have hθl : θ.toMonoidHom (QuotientGroup.mk' (center (Bar2 L))
        (QuotientGroup.mk' (CFSG.pCore 2 ↥L) l)) =
        QuotientGroup.mk' (center (Bar2 L)) (QuotientGroup.mk' (CFSG.pCore 2 ↥L) j') :=
      hθ l j' rfl
    rw [hθl]
    exact Subgroup.mem_map.2 ⟨_, Subgroup.mem_map.2
      ⟨j', Subgroup.mem_subgroupOf.2 hj'J, rfl⟩, rfl⟩
  · rintro _ hx
    obtain ⟨z, hz, rfl⟩ := Subgroup.mem_map.1 hx
    obtain ⟨l, hl, rfl⟩ := Subgroup.mem_map.1 hz
    have hjJ : (l : G) ∈ J := Subgroup.mem_subgroupOf.1 hl
    let j₀ : ↥L := ⟨t⁻¹ * (l : G) * t,
      (Subgroup.mem_normalizer_iff''.mp htL (l : G)).mp l.2⟩
    have hj₀J : (j₀ : G) ∈ J := (Subgroup.mem_normalizer_iff''.mp htJ (l : G)).mp hjJ
    have hθl : θ.toMonoidHom (QuotientGroup.mk' (center (Bar2 L))
        (QuotientGroup.mk' (CFSG.pCore 2 ↥L) j₀)) =
        QuotientGroup.mk' (center (Bar2 L)) (QuotientGroup.mk' (CFSG.pCore 2 ↥L) l) := by
      refine hθ j₀ l ?_
      show (l : G) = t * (t⁻¹ * (l : G) * t) * t⁻¹
      group
    refine Subgroup.mem_map.2 ⟨_, Subgroup.mem_map.2
      ⟨_, Subgroup.mem_map.2 ⟨j₀, Subgroup.mem_subgroupOf.2 hj₀J, rfl⟩, rfl⟩, hθl⟩

end CFSG.LocalAnalysis.UniquenessCase.UC22.RankOneBorel

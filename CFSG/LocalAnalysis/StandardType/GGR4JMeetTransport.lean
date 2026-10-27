module

public import CFSG.LocalAnalysis.StandardType.GGR4JMeetKGDefs
public import CFSG.LocalAnalysis.StandardType.GGTableBStdSub
public import CFSG.LocalAnalysis.StandardType.GGLemmaThreeThirteenFourteenP

public section

namespace CFSG.StandardType

open CFSG.Assembly

theorem ggR4Meet_transport {G : Type} [Group G] {L J : Subgroup G} {z : G} (hz : z ∈ L)
    (hJ : J = LargeEvenLayer (L ⊓ Subgroup.centralizer ({z} : Set G)))
    (hC : IsComponentOf J (L ⊓ Subgroup.centralizer ({z} : Set G))) :
    J ≤ L ∧
      J.subgroupOf L = LargeEvenLayer (Subgroup.centralizer ({(⟨z, hz⟩ : ↥L)} : Set ↥L)) ∧
      IsComponentOf (J.subgroupOf L) (Subgroup.centralizer ({(⟨z, hz⟩ : ↥L)} : Set ↥L)) := by
  let H : Subgroup G := L ⊓ Subgroup.centralizer ({z} : Set G)
  let H' : Subgroup ↥L := Subgroup.centralizer ({(⟨z, hz⟩ : ↥L)} : Set ↥L)
  have hHsub : H.subgroupOf L = H' := by
    ext x
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_inf]
    constructor
    · intro hx
      rw [Subgroup.mem_centralizer_singleton_iff]
      apply Subtype.ext
      exact Subgroup.mem_centralizer_singleton_iff.mp hx.2
    · intro hx
      refine ⟨x.2, ?_⟩
      rw [Subgroup.mem_centralizer_singleton_iff]
      have h := Subgroup.mem_centralizer_singleton_iff.mp hx
      simpa using congrArg Subtype.val h
  have hHmap : H'.map L.subtype = H := by
    rw [← hHsub]
    exact Subgroup.map_subgroupOf_eq_of_le inf_le_left
  have hJl : J ≤ L := by
    rw [hJ]
    exact sSup_le fun K hK => hK.1.trans inf_le_left
  have hlayer : J.subgroupOf L = LargeEvenLayer H' := by
    have hmap : J = (LargeEvenLayer H').map L.subtype := by
      rw [hJ, ← largeEvenLayer_map_of_injective L.subtype L.subtype_injective H', hHmap]
    have hcongr := congrArg (fun X : Subgroup G => X.subgroupOf L) hmap
    rw [hcongr]
    exact Subgroup.comap_map_eq_self_of_injective L.subtype_injective (LargeEvenLayer H')
  have hcomp : IsComponentOf (J.subgroupOf L) H' := by
    rw [← hHsub]
    exact ggIsComponentOf_subgroupOf hC inf_le_left
  refine ⟨hJl, ?_, ?_⟩
  · simpa [H'] using hlayer
  · simpa [H'] using hcomp

end CFSG.StandardType

end

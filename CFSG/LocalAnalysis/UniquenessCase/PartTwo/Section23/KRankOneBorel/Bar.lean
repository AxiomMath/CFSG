module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S21a

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.RankOneBorel

open Subgroup CFSG.Open

variable {G : Type} [Group G] [Finite G]

theorem pCoreOf_le_inf {T L : Subgroup G} (hTL : CFSG.Quasithin.IsSylowIn 2 (T ⊓ L) L) :
    pCoreOf 2 L ≤ T ⊓ L := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact CFSG.Quasithin.pCoreOf_le_of_isSylowIn hTL

theorem exists_sylow_barImage {T L : Subgroup G} (hTL : CFSG.Quasithin.IsSylowIn 2 (T ⊓ L) L) :
    ∃ S : Sylow 2 (Bar2 L), (S : Subgroup (Bar2 L)) = barImage L (T ⊓ L) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine ⟨hTL.toSylow.mapSurjective (QuotientGroup.mk'_surjective _), ?_⟩
  rw [Sylow.coe_mapSurjective, CFSG.Quasithin.IsSylowIn.coe_toSylow, barImage]

theorem commutator_bar2_eq_top {L : Subgroup G} (hperf : ⁅L, L⁆ = L) :
    _root_.commutator (Bar2 L) = ⊤ := by
  have htopL : (⊤ : Subgroup ↥L).map L.subtype = L := by
    simpa [MonoidHom.range_eq_map] using Subgroup.range_subtype (H := L)
  have hL : _root_.commutator ↥L = ⊤ := by
    apply Subgroup.map_injective L.subtype_injective
    rw [_root_.commutator_def, Subgroup.map_commutator, htopL, hperf]
  have hsurj : Function.Surjective (QuotientGroup.mk' (CFSG.pCore 2 ↥L)) :=
    QuotientGroup.mk'_surjective _
  have hmap : (_root_.commutator ↥L).map (QuotientGroup.mk' (CFSG.pCore 2 ↥L)) =
      _root_.commutator (Bar2 L) := by
    rw [_root_.commutator_def, Subgroup.map_commutator,
      Subgroup.map_top_of_surjective _ hsurj, _root_.commutator_def]
  rw [← hmap, hL, Subgroup.map_top_of_surjective _ hsurj]

theorem mk_mem_barImage_iff {L J : Subgroup G} (hOJ : pCoreOf 2 L ≤ J) (l : ↥L) :
    (QuotientGroup.mk l : Bar2 L) ∈ barImage L J ↔ (l : G) ∈ J := by
  have hOsub : CFSG.pCore 2 ↥L ≤ J.subgroupOf L := fun y hy =>
    hOJ (Subgroup.mem_map_of_mem L.subtype hy)
  unfold barImage
  rw [← QuotientGroup.mk'_apply (N := CFSG.pCore 2 ↥L) l, ← Subgroup.mem_comap,
    QuotientGroup.comap_map_mk', sup_eq_right.mpr hOsub, Subgroup.mem_subgroupOf]

theorem barImage_le_barImage_iff {L J K : Subgroup G} (hOJ : pCoreOf 2 L ≤ J) (hKL : K ≤ L) :
    barImage L K ≤ barImage L J ↔ K ≤ J := by
  constructor
  · intro h k hk
    have hmem : (QuotientGroup.mk ⟨k, hKL hk⟩ : Bar2 L) ∈ barImage L K :=
      Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr hk)
    exact (mk_mem_barImage_iff hOJ ⟨k, hKL hk⟩).mp (h hmem)
  · intro hKJ x hx
    unfold barImage at hx ⊢
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
    exact Subgroup.mem_map_of_mem _ (hKJ (Subgroup.mem_subgroupOf.mp hy))

theorem of_bar {T L J : Subgroup G} (hTL : CFSG.Quasithin.IsSylowIn 2 (T ⊓ L) L)
    (hJ1 : T ⊓ L ≤ J) (hJ2 : J ≤ L)
    (h : barImage L J ≤
        normalizer ((barImage L (T ⊓ L) : Subgroup (Bar2 L)) : Set (Bar2 L)) ∨
      barImage L J = ⊤) :
    J ≤ normalizer ((T ⊓ L : Subgroup G) : Set G) ∨ J = L := by
  have hOJ : pCoreOf 2 L ≤ T ⊓ L := pCoreOf_le_inf hTL
  have hOJT : pCoreOf 2 L ≤ J := hOJ.trans hJ1
  rcases h with hnorm | htop
  · left
    have hOsub : CFSG.pCore 2 ↥L ≤ (T ⊓ L).subgroupOf L := fun y hy =>
      hOJ (Subgroup.mem_map_of_mem L.subtype hy)
    have hSbar : (barImage L (T ⊓ L)).comap (QuotientGroup.mk' (CFSG.pCore 2 ↥L)) =
        (T ⊓ L).subgroupOf L := by
      unfold barImage
      rw [QuotientGroup.comap_map_mk']
      exact sup_eq_right.mpr hOsub
    have hcomap : (Subgroup.normalizer (barImage L (T ⊓ L) : Set (Bar2 L))).comap
        (QuotientGroup.mk' (CFSG.pCore 2 ↥L)) =
        (Subgroup.normalizer (T ⊓ L : Subgroup G)).subgroupOf L := by
      rw [Subgroup.comap_normalizer_eq_of_surjective _ (QuotientGroup.mk'_surjective _),
        Subgroup.subgroupOf_normalizer_eq (show T ⊓ L ≤ L from inf_le_right), hSbar]
    have hJsub : J.subgroupOf L ≤
        (Subgroup.normalizer (barImage L (T ⊓ L) : Set (Bar2 L))).comap
          (QuotientGroup.mk' (CFSG.pCore 2 ↥L)) := by
      intro x hx
      exact hnorm (Subgroup.mem_map_of_mem _ hx)
    rw [hcomap] at hJsub
    intro j hj
    have hjL : j ∈ L := hJ2 hj
    have hm : (⟨j, hjL⟩ : ↥L) ∈ J.subgroupOf L := by
      rw [Subgroup.mem_subgroupOf]
      simpa using hj
    simpa using Subgroup.mem_subgroupOf.mp (hJsub hm)
  · right
    refine le_antisymm hJ2 ?_
    intro l hl
    have hmem : (QuotientGroup.mk ⟨l, hl⟩ : Bar2 L) ∈ barImage L J := by
      rw [htop]
      exact Subgroup.mem_top _
    exact (mk_mem_barImage_iff hOJT ⟨l, hl⟩).mp hmem

end CFSG.LocalAnalysis.UniquenessCase.UC22.RankOneBorel

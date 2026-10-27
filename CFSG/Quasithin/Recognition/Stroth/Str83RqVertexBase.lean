module

public import CFSG.GroupTheory.PCore.OpenTransport
public import CFSG.Quasithin.Background.F1Basic
public import CFSG.GroupTheory.ConjActionModPCore

public section

namespace CFSG.Quasithin.Stroth

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique
open scoped commutatorElement

variable {G : Type} [Group G]

theorem exists_sylow_oTwoQuot_of_isSylowTwoOf {L T : Subgroup G} [Finite ↥L]
    (hT : IsSylowTwoOf T L) :
    ∃ P : Sylow 2 (oTwoQuot ↥L), (P : Subgroup (oTwoQuot ↥L)) =
      (T.subgroupOf L).map (QuotientGroup.mk' (pCore 2 ↥L)) := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨S, hS⟩ := F7.isSylowTwoOf_exists_sylow hT
  refine ⟨S.mapSurjective (QuotientGroup.mk'_surjective _), ?_⟩
  rw [Sylow.coe_mapSurjective, hS]

theorem map_oTwoQuot_injective_of_isSylowTwoOf [Finite G] {L T T' : Subgroup G}
    (hT : IsSylowTwoOf T L) (hT' : IsSylowTwoOf T' L)
    (h : (T.subgroupOf L).map (QuotientGroup.mk' (pCore 2 ↥L)) =
      (T'.subgroupOf L).map (QuotientGroup.mk' (pCore 2 ↥L))) : T = T' := by
  let π : ↥L →* oTwoQuot ↥L := QuotientGroup.mk' (pCore 2 ↥L)
  have hker : π.ker ≤ T.subgroupOf L := by
    rw [show π.ker = pCore 2 ↥L from QuotientGroup.ker_mk' _, ← CFSG.openPCoreOf_subgroupOf 2 L]
    exact Subgroup.comap_mono (F7.isSylowTwoOf_pCoreOf_le hT)
  have hker' : π.ker ≤ T'.subgroupOf L := by
    rw [show π.ker = pCore 2 ↥L from QuotientGroup.ker_mk' _, ← CFSG.openPCoreOf_subgroupOf 2 L]
    exact Subgroup.comap_mono (F7.isSylowTwoOf_pCoreOf_le hT')
  have hsub : T.subgroupOf L = T'.subgroupOf L :=
    Subgroup.map_injective_of_ker_le π hker hker' h
  calc T = (T.subgroupOf L).map L.subtype := (Subgroup.map_subgroupOf_eq_of_le hT.1).symm
    _ = (T'.subgroupOf L).map L.subtype := by rw [hsub]
    _ = T' := Subgroup.map_subgroupOf_eq_of_le hT'.1

theorem conjModPCore_mk_eq_mk_iff {L : Subgroup G} {k : G}
    (hk : k ∈ Subgroup.normalizer (L : Set G)) (l : ↥L) :
    CFSG.GroupTheory.conjModPCore 2 L (Subgroup.normalizer (L : Set G)) le_rfl ⟨k, hk⟩
        (QuotientGroup.mk l) = QuotientGroup.mk l ↔ ⁅k, (l : G)⁆ ∈ pCoreOf 2 L := by
  have hcoe : ∀ h : k * (l : G) * k⁻¹ ∈ L,
      (((⟨k * (l : G) * k⁻¹, h⟩ : ↥L) / l : ↥L) : G) = ⁅k, (l : G)⁆ := by
    intro h
    rw [Subgroup.coe_div, div_eq_mul_inv, commutatorElement_def]
  constructor
  · intro h
    rw [CFSG.GroupTheory.conjModPCore_mk] at h
    have hdiv : ((⟨k * (l : G) * k⁻¹,
        (Subgroup.mem_normalizer_iff.mp hk (l : G)).mp l.2⟩ : ↥L) / l) ∈ pCore 2 ↥L :=
      QuotientGroup.eq_iff_div_mem.mp h
    have hpc := (F1.mem_pCore_iff_coe _).mp hdiv
    rwa [hcoe] at hpc
  · intro hcomm
    rw [CFSG.GroupTheory.conjModPCore_mk]
    refine QuotientGroup.eq_iff_div_mem.mpr ?_
    refine (F1.mem_pCore_iff_coe _).mpr ?_
    rwa [hcoe]

theorem map_oTwoQuot_subgroupOf_eq_top_iff {L Y : Subgroup G} (hY : Y ≤ L)
    (hQ : pCoreOf 2 L ≤ Y) :
    (Y.subgroupOf L).map (QuotientGroup.mk' (pCore 2 ↥L)) = ⊤ ↔ Y = L := by
  constructor
  · intro hmap
    refine le_antisymm hY ?_
    intro l hl
    have hmem : QuotientGroup.mk' (pCore 2 ↥L) (⟨l, hl⟩ : ↥L) ∈
        (Y.subgroupOf L).map (QuotientGroup.mk' (pCore 2 ↥L)) := by
      rw [hmap]
      exact Subgroup.mem_top _
    obtain ⟨y, hy, hyl⟩ := Subgroup.mem_map.mp hmem
    have hyY : (y : G) ∈ Y := Subgroup.mem_subgroupOf.mp hy
    have hdiv : (y / (⟨l, hl⟩ : ↥L)) ∈ pCore 2 ↥L :=
      QuotientGroup.eq_iff_div_mem.mp hyl
    have hdivY : (y : G) * l⁻¹ ∈ Y := by
      have hpc : ((y / (⟨l, hl⟩ : ↥L) : ↥L) : G) ∈ pCoreOf 2 L :=
        (F1.mem_pCore_iff_coe _).mp hdiv
      simpa [Subgroup.coe_div, div_eq_mul_inv] using hQ hpc
    have hinv : l⁻¹ ∈ Y := by
      have hmem' := Y.mul_mem (Y.inv_mem hyY) hdivY
      rwa [inv_mul_cancel_left] at hmem'
    simpa using Y.inv_mem hinv
  · intro hYL
    rw [hYL, Subgroup.subgroupOf_self]
    exact Subgroup.map_top_of_surjective (QuotientGroup.mk' (pCore 2 ↥L))
      (QuotientGroup.mk'_surjective _)

theorem le_sup_pCoreOf_iff_map_subgroupOf_eq_top {L X : Subgroup G} :
    L ≤ X ⊔ pCoreOf 2 L ↔
      (((X ⊔ pCoreOf 2 L) ⊓ L).subgroupOf L).map
        (QuotientGroup.mk' (pCore 2 ↥L)) = ⊤ := by
  rw [map_oTwoQuot_subgroupOf_eq_top_iff inf_le_right
    (le_inf le_sup_right (pCoreOf_le 2 L))]
  constructor
  · intro h
    exact le_antisymm inf_le_right (le_inf h le_rfl)
  · intro h
    have hle : ((X ⊔ pCoreOf 2 L) ⊓ L) ≤ X ⊔ pCoreOf 2 L := inf_le_left
    rwa [h] at hle

end CFSG.Quasithin.Stroth

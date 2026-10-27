module

public import CFSG.Quasithin.Vol2.Ch1Comm
public import CFSG.Quasithin.H13.StatementsFSU
public import CFSG.Quasithin.Background.F7Basic

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.QuasithinUnique

variable {G : Type} [Group G] [Finite G]

theorem fsu_conj_structure {T L I : Subgroup G} (hF : FSU G T L I) (h37 : A37ForSQTK)
    (h38 : A38ForSQTK) {t : G} (htT : t ∈ T) (htL : t ∉ Subgroup.normalizer (L : Set G)) :
    conjClosure L T = L ⊔ conjSub t L ∧ ⁅L, conjSub t L⁆ ≤ pCoreOf 2 (L ⊔ T) ∧
      conjSub t L ∈ cComp (L ⊔ T) := by
  have hloc : quasithinIsLocal T L := hF.maximal.1
  have hX2 : pCoreOf 2 (L ⊔ T) ≠ ⊥ := hloc.2.2.2
  have hLc : L ∈ cComp (L ⊔ T) := hloc.2.1
  have htX : t ∈ L ⊔ T := Subgroup.mem_sup_right htT
  have hLt : conjSub t L ∈ cComp (L ⊔ T) := map_conj_mem_cComp hLc htX
  have hne : L ≠ conjSub t L := fun h => htL (A38.map_conj_eq_iff.mp h.symm)
  have h2 := lemma_1_2_1_two hF.qtke hF.simple hF.nonabelian h37 hX2 hLc hLt hne
  have h3 := lemma_1_2_1_three hF.qtke hF.simple hF.nonabelian h37 h38 hX2 hLc
  rcases h3 with hN | ⟨hcard, -⟩
  · exact absurd ((Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).mp hN htX) htL
  · have hsub : ({L, conjSub t L} : Set (Subgroup G)) ⊆ conjSubgroupsBy (L ⊔ T) L := by
      rintro K (rfl | rfl)
      · exact ⟨1, Subgroup.one_mem _, by ext x; simp⟩
      · exact ⟨t, htX, rfl⟩
    have hset : ({L, conjSub t L} : Set (Subgroup G)) = conjSubgroupsBy (L ⊔ T) L :=
      Set.eq_of_subset_of_ncard_le hsub (by rw [hcard, Set.ncard_pair hne])
    refine ⟨?_, h2.1.trans (h2.2), hLt⟩
    apply le_antisymm
    · refine conjClosure_le fun s hs z hz => ?_
      have hmem : L.map (MulAut.conj s).toMonoidHom ∈ ({L, conjSub t L} : Set (Subgroup G)) := by
        rw [hset]
        exact ⟨s, Subgroup.mem_sup_right hs, rfl⟩
      have hzs : s * z * s⁻¹ ∈ L.map (MulAut.conj s).toMonoidHom := ⟨z, hz, rfl⟩
      rcases hmem with h | h
      · rw [h] at hzs
        exact Subgroup.mem_sup_left hzs
      · rw [h] at hzs
        exact Subgroup.mem_sup_right hzs
    · refine sup_le (le_conjClosure L T) ?_
      rintro _ ⟨z, hz, rfl⟩
      exact mem_conjClosure htT hz

end CFSG.Quasithin.H13

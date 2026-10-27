module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S20
import CFSG.Quasithin.Background.A3ComponentsAmbient

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.KAdjE

theorem suo_mem_normalizer_hinf_of_mem {G : Type} [Group G] {Q : Subgroup G} {e : G}
    (he : e ∈ Q) : e ∈ Subgroup.normalizer (Hinf Q : Set G) := by
  have hH : Hinf Q = CFSG.Quasithin.perfectCore Q :=
    (CFSG.Quasithin.perfectCore_eq_map_perfectResidual Q).symm
  rw [hH]
  exact CFSG.Quasithin.normalizer_le_normalizer_perfectCore Q (Subgroup.le_normalizer he)

theorem suo_conj_mem_hinf {G : Type} [Group G] {Q : Subgroup G} {e t : G} (he : e ∈ Q)
    (ht : t ∈ Hinf Q) : e * t * e⁻¹ ∈ Hinf Q :=
  (Subgroup.mem_normalizer_iff.mp (suo_mem_normalizer_hinf_of_mem he) t).mp ht

theorem suo_hom_eq_one_of_mem_hinf {G A : Type} [Group G] [Group A] {Q : Subgroup G}
    (φ : ↥Q →* A) (hφ : Group.IsSolvable ↥φ.range) {g : G} (hg : g ∈ Hinf Q) :
    ∃ hgQ : g ∈ Q, φ ⟨g, hgQ⟩ = 1 := by
  unfold Hinf CFSG.inSubgroup at hg
  obtain ⟨w, hw, rfl⟩ := hg
  refine ⟨w.2, ?_⟩
  unfold CFSG.perfectResidual at hw
  obtain ⟨n, hn⟩ := hφ.solvable
  have hmap : (derivedSeries ↥Q n).map φ.rangeRestrict = ⊥ := by
    rw [map_derivedSeries_eq φ.rangeRestrict_surjective n, hn]
  have hmem : w ∈ φ.rangeRestrict.ker :=
    (Subgroup.map_eq_bot_iff (H := derivedSeries ↥Q n)).mp hmap ((Subgroup.mem_iInf.mp hw) n)
  have h1 : φ.rangeRestrict w = 1 := MonoidHom.mem_ker.mp hmem
  change (φ.rangeRestrict w : A) = 1
  rw [h1, Subgroup.coe_one]

end CFSG.LocalAnalysis.UniquenessCase.UC22.KAdjE

module

public import CFSG.LocalAnalysis.StandardType.FS81.S7E7Incl
import CFSG.LocalAnalysis.StandardType.FS81.S7ModelCent

public section

namespace CFSG.StandardType.FrameRoute.FS81

open CFSG.Open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.SeitzReduction CFSG.QuasithinUnique

local notation "GF₂" => GaloisField 2 1
local notation "sθ" => rootThree Tag.E8 (GaloisField 2 1) (highRoot Tag.E8)
local notation "Dθ" => EPilot.perpLevi Tag.E8 (GaloisField 2 1)

section E7Model


theorem mem_sup_map_of_centralizes_rootThree {G : Type} [Group G]
    (ι : adjointGroup .E8 GF₂ →* G) (hι : Function.Injective ι) {y : G} (hy : y ∈ ι.range)
    (hyc : y * ι sθ = ι sθ * y) : y ∈ Subgroup.zpowers (ι sθ) ⊔ (Dθ).map ι := by
  obtain ⟨m, rfl⟩ := hy
  have hm : m ∈ Subgroup.centralizer ({sθ} : Set (adjointGroup .E8 GF₂)) := by
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    rw [Set.mem_singleton_iff] at hh
    subst hh
    exact hι (by simpa only [map_mul] using hyc.symm)
  rw [centralizer_rootThree_highRoot_E8 (K := GF₂) natCard_galoisField_two_one] at hm
  rw [← MonoidHom.map_zpowers, ← Subgroup.map_sup]
  exact Subgroup.mem_map_of_mem ι hm

theorem map_perpLevi_centralizes_disjoint {G : Type} [Group G]
    (ι : adjointGroup .E8 GF₂ →* G) (hι : Function.Injective ι) :
    (∀ x ∈ (Dθ).map ι, x * ι sθ = ι sθ * x) ∧
      ∀ x ∈ (Dθ).map ι, x ∈ Subgroup.zpowers (ι sθ) → x = 1 := by
  have hC := centralizer_rootThree_highRoot_E8 (K := GF₂) natCard_galoisField_two_one
  have hD : Dθ ≤ Subgroup.centralizer ({sθ} : Set (adjointGroup .E8 GF₂)) := by
    rw [hC]
    exact le_sup_right
  constructor
  · rintro x ⟨d, hd, rfl⟩
    simpa only [map_mul] using
      congrArg ι (Subgroup.mem_centralizer_iff.1 (hD hd) sθ (Set.mem_singleton _)).symm
  · rintro x ⟨d, hd, rfl⟩ hx
    rw [← MonoidHom.map_zpowers] at hx
    obtain ⟨z, hz, hzd⟩ := Subgroup.mem_map.1 hx
    have hdz : z = d := hι hzd
    have hzD : z ∈ Dθ := by rw [hdz]; exact hd
    have hz1 : z = 1 := Subgroup.disjoint_def.1
      (disjoint_zpowers_rootThree_perpLevi_E8 (K := GF₂)) hz hzD
    rw [← hdz, hz1, map_one]

end E7Model

end CFSG.StandardType.FrameRoute.FS81

end

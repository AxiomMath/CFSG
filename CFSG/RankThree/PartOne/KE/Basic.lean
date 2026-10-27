module

public import CFSG.RankThree.PartOne.KE.Statements

public section

namespace CFSG.RankThree.PartOne

open CFSG CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.RankThree.LocalRank
open CFSG.LocalAnalysis.ComponentInitial
open scoped Pointwise

theorem relIndex_centralizer_eq_card_image_automizer {G : Type*} [Group G] {L W : Subgroup G}
    [Group.IsPerfect L] (hWN : W ≤ Subgroup.normalizer (L : Set G)) :
    (Subgroup.centralizer (L : Set G)).relIndex W =
      Nat.card ((W.subgroupOf (Subgroup.normalizer (L : Set G))).map
        (Finkelstein1977.automizer L)) := by
  set φ : W →* MulAut (L ⧸ Subgroup.center L) :=
    (Finkelstein1977.automizer L).comp (Subgroup.inclusion hWN) with hφ
  have hker : φ.ker = (Subgroup.centralizer (L : Set G)).subgroupOf W := by
    ext w
    simp only [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, hφ, MonoidHom.comp_apply]
    exact Finkelstein1977.automizer_eq_one_iff L _
  have hrange : φ.range =
      (W.subgroupOf (Subgroup.normalizer (L : Set G))).map (Finkelstein1977.automizer L) := by
    ext x
    simp only [MonoidHom.mem_range, Subgroup.mem_map, Subgroup.mem_subgroupOf, hφ,
      MonoidHom.comp_apply]
    constructor
    · rintro ⟨w, rfl⟩
      exact ⟨Subgroup.inclusion hWN w, w.2, rfl⟩
    · rintro ⟨n, hn, rfl⟩
      exact ⟨⟨n, hn⟩, rfl⟩
  rw [Subgroup.relIndex, ← hker, Subgroup.index_ker, hrange]

theorem relIndex_centralizer_eq_card_localCoreProductImage {G : Type*} [Group G] {p : ℕ}
    {E : Subgroup G} {t : G} {L : Subgroup G} (hL : IsComponent L)
    (hWN : localCoreProduct p E t ≤ Subgroup.normalizer (L : Set G)) :
    (Subgroup.centralizer (L : Set G)).relIndex (localCoreProduct p E t) =
      Nat.card (localCoreProductImage p E t L) := by
  have : Group.IsPerfect L := hL.1.1
  exact relIndex_centralizer_eq_card_image_automizer hWN

theorem componentLocalCoreOddConclusion_of_image {G : Type*} [Group G] {p : ℕ} {E : Subgroup G}
    {t : G} {L : Subgroup G} (hL : IsComponent L) (h : ComponentLocalCoreOddImage p E t L) :
    ComponentLocalCoreOddConclusion p E t L := by
  obtain ⟨hset, hWN, hodd, -⟩ := h
  refine ⟨hset, hWN, ?_⟩
  show ¬ 2 ∣ (Subgroup.centralizer (L : Set G)).relIndex (localCoreProduct p E t)
  rw [relIndex_centralizer_eq_card_localCoreProductImage hL hWN]
  exact hodd

theorem componentLocalCoreOddImage_of_residual {G : Type*} [Group G] {p : ℕ} {E : Subgroup G}
    {t : G} {L : Subgroup G} (hL : IsComponent L) (h : ComponentLocalCoreOddResidual p E t L) :
    ComponentLocalCoreOddImage p E t L := by
  obtain ⟨⟨hset, hWN, hodd⟩, hres⟩ := h
  refine ⟨hset, hWN, ?_, hres⟩
  rw [← relIndex_centralizer_eq_card_localCoreProductImage hL hWN]
  exact hodd

theorem componentLocalCoreOddImage_of_le_centralizer {G : Type*} [Group G] {p : ℕ}
    {E : Subgroup G} {t : G} {L : Subgroup G}
    (hset : ((localCoreProduct p E t : Subgroup G) : Set G) =
      ((⁅inSubgroup (aschbacherSolvableCore p) (Subgroup.centralizer ({t} : Set G)), E⁆ :
        Subgroup G) : Set G) * (thetaT p E : Set G))
    (hle : localCoreProduct p E t ≤ Subgroup.centralizer (L : Set G)) (hL : IsComponent L) :
    ComponentLocalCoreOddImage p E t L := by
  have hWN : localCoreProduct p E t ≤ Subgroup.normalizer (L : Set G) :=
    hle.trans (Subgroup.centralizer_le_normalizer _)
  have hodd : ¬ 2 ∣ (Subgroup.centralizer (L : Set G)).relIndex (localCoreProduct p E t) := by
    rw [Subgroup.relIndex_eq_one.mpr hle]
    omega
  refine ⟨hset, hWN, ?_, twoPrimeResidual_le_centralizer_of_odd_relIndex hWN hodd⟩
  rw [← relIndex_centralizer_eq_card_localCoreProductImage hL hWN]
  exact hodd

end CFSG.RankThree.PartOne

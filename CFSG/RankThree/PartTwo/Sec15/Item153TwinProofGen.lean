module

public import CFSG.RankThree.PartTwo.Sec15.Item156StepsProofGen
import CFSG.RankThree.PartTwo.Sec15.Item152GenProofTheta

public section

namespace CFSG.RankThree.PartTwo.Sec15.Proof153Twin

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank CFSG.GH74.GLS
open CFSG.RankThree.PartTwo.Sec15.Proof152Gen CFSG.RankThree.PartTwo.Sec15.Proof156

variable {G : Type} [Group G] [Finite G]

theorem le_sup_of_data156
    (h142 : Item142AllS14) {A : Subgroup G} {c : G} {L : Subgroup G} (h : Sec14Std G A c L)
    {Y X₁ : Subgroup G} {d : G} (D : Data156 A (lB A) Y c L d X₁) {U : Subgroup G}
    (hU : U ∈ scriptQPiStar A (lB A) (Subgroup.normalizer (Subgroup.zpowers c : Set G))
      (piOf 2)) :
    L ≤ U ⊔ X₁ := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hS13 := h.toSec13Data
  have hA : Late.IsE27 A := Late.isE27_of_mem_partTwoE hS13.mem_partTwoE
  have hJ := D.hj
  set J := U ⊔ X₁ with hJdef
  set θ := aschbacherSolvableCore 3 ↥L with hθdef
  set ρ := QuotientGroup.mk' θ with hρ
  have hθL : inSubgroup (aschbacherSolvableCore 3) L ≤ J :=
    (theta_le_of_mem_scriptQPiStar h hJ hU).trans le_sup_left
  obtain ⟨hQ2, hQ64⟩ := sixtyFour_dvd_card_map_inf ks152J2InvolNine_holds h hJ hU
  obtain ⟨hAX, -, -, hXq, htype, -, -, -, hdC, -⟩ := facts_of_data156 D hA
  have hcov := cover_of_data156 h (h142 G A c L h) D
  have hd3 : d ^ 3 = 1 := hA.1.2 d D.mem_d
  obtain ⟨hdL, S3, hdS3, hS3d⟩ := D.central_d
  have hdXL : d ∈ Subgroup.normalizer ((X₁ ⊓ L : Subgroup G) : Set G) :=
    Late.le_normalizer_inf hAX hS13.le_normalizer D.mem_d
  have hW : ((X₁ ⊓ L).subgroupOf X₁).map
      (QuotientGroup.mk' (aschbacherSolvableCore 3 ↥X₁)) = ⊤ :=
    map_subgroupOf_eq_top_of_le_sup inf_le_left hcov
  have hW' := map_inf_centralizer_eq_top inf_le_left hdXL hd3 hdC hW
  obtain ⟨D', hD'W, hD'p, hD'top⟩ := exists_isPerfect_cover hXq.1 hW'
  have hD'X : D' ≤ X₁ := hD'W.trans (inf_le_left.trans inf_le_left)
  have hD'L : D' ≤ L := hD'W.trans (inf_le_left.trans inf_le_right)
  have hD'd : D' ≤ Subgroup.centralizer ({d} : Set G) := hD'W.trans inf_le_right
  set z : ↥L ⧸ θ := ρ ⟨d, hdL⟩ with hz
  have hz1 : z ≠ 1 := by
    intro hz1
    have hmem : (⟨d, hdL⟩ : ↥L) ∈ θ := (QuotientGroup.eq_one_iff _).mp hz1
    have hord : orderOf (⟨⟨d, hdL⟩, hmem⟩ : θ) = 3 := by
      rw [Subgroup.orderOf_mk, Subgroup.orderOf_mk]
      exact orderOf_eq_prime hd3 D.ne_d
    have h3 := orderOf_dvd_natCard (⟨⟨d, hdL⟩, hmem⟩ : θ)
    rw [hord] at h3
    exact (solvable_prime_complement_core_characterization (H := ↥L) Nat.prime_three).2.2.1 h3
  have hzc : ∃ S' : Sylow 3 (↥L ⧸ θ), z ∈ (S' : Subgroup (↥L ⧸ θ)) ∧
      (S' : Subgroup (↥L ⧸ θ)) ≤ Subgroup.centralizer ({z} : Set (↥L ⧸ θ)) := by
    refine ⟨S3.mapSurjective (QuotientGroup.mk'_surjective θ), ?_, ?_⟩
    · rw [Sylow.coe_mapSurjective]
      exact ⟨⟨d, hdL⟩, hdS3, rfl⟩
    · rw [Sylow.coe_mapSurjective]
      rintro _ ⟨s, hs, rfl⟩
      have hs' := hS3d hs
      rw [Subgroup.mem_centralizer_singleton_iff] at hs' ⊢
      rw [hz, ← map_mul, ← map_mul, hs']
  have hD'z : (D'.subgroupOf L).map ρ ≤ Subgroup.centralizer ({z} : Set (↥L ⧸ θ)) := by
    rintro _ ⟨y, hy, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hyd : (y : G) * d = d * y :=
      Subgroup.mem_centralizer_singleton_iff.mp (hD'd (Subgroup.mem_subgroupOf.mp hy))
    rw [hz, ← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext hyd
  obtain ⟨F₀, hF₀D, hF₀p, hF₀60, hF₀z⟩ := exists_sixty_of_cover hXq htype hJ
    (isPGroup_theta_of_j2 h hJ) hD'X hD'L hD'top hD'p hz1 hzc hD'z
  have htop := ks152J2Gen_holds (↥L ⧸ θ) hJ z hz1 hzc _ F₀ hQ2 hQ64 hF₀z hF₀p hF₀60
  have hJbar : (J.subgroupOf L).map ρ = ⊤ := by
    rw [eq_top_iff, ← htop]
    refine sup_le (Subgroup.map_mono fun x hx => ?_)
      (hF₀D.trans (Subgroup.map_mono fun x hx => ?_))
    · exact Subgroup.mem_subgroupOf.mpr
        ((le_sup_left : U ≤ J) (Subgroup.mem_subgroupOf.mp hx).1)
    · exact Subgroup.mem_subgroupOf.mpr
        ((le_sup_right : X₁ ≤ J) (hD'X (Subgroup.mem_subgroupOf.mp hx)))
  intro l hl
  obtain ⟨j, hj, hjl⟩ : ρ ⟨l, hl⟩ ∈ (J.subgroupOf L).map ρ := hJbar ▸ Subgroup.mem_top _
  have hjθ : j⁻¹ * ⟨l, hl⟩ ∈ θ := by
    rw [← QuotientGroup.eq]
    exact hjl
  have h1 : ((j⁻¹ * ⟨l, hl⟩ : ↥L) : G) ∈ J := hθL ⟨_, hjθ, rfl⟩
  have h2 : (j : G) ∈ J := Subgroup.mem_subgroupOf.mp hj
  have h3 : l = (j : G) * ((j⁻¹ * ⟨l, hl⟩ : ↥L) : G) := by
    rw [Subgroup.coe_mul, Subgroup.coe_inv]
    group
  rw [h3]
  exact J.mul_mem h2 h1

end CFSG.RankThree.PartTwo.Sec15.Proof153Twin

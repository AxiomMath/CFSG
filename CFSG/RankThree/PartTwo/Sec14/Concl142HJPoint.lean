module

public import CFSG.RankThree.PartTwo.Sec14.Concl142HJ
public import CFSG.RankThree.PartTwo.Sec13.Statements
import CFSG.RankThree.PartTwo.Sec14.Item1417
import CFSG.RankThree.PartTwo.Sec14.Item1411HJ
import CFSG.RankThree.PartTwo.Sec4.Sporadic.Item415
import CFSG.RankThree.PartTwo.KFacts.KS14HJBasic
import CFSG.RankThree.PartTwo.Sec13.Item13Basic

public section

namespace CFSG.RankThree.PartTwo.Sec14

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.LocalRank

variable {G : Type} [Group G] [Finite G]

section Certificates


theorem exists_three_central_of_j2 {A L : Subgroup G} {c : G} (hD : Sec13Data G A c L)
    (hJ : Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* CFSG.Blueprint.NativeSporadic.J2)) :
    ∃ d ∈ A, d ≠ 1 ∧ ∃ hd : d ∈ L, ∃ S : Sylow 3 ↥L, (⟨d, hd⟩ : ↥L) ∈ (S : Subgroup ↥L) ∧
      (S : Subgroup ↥L) ≤ Subgroup.centralizer {(⟨d, hd⟩ : ↥L)} := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h415 : Sec4.Item4_15 := Sec4.Sporadic.rank3II_4_15
  obtain ⟨-, h9, -⟩ := j2_point_facts hD hJ
  set θ := aschbacherSolvableCore 3 ↥L with hθ
  set π := QuotientGroup.mk' θ with hπ
  have hπs : Function.Surjective π := QuotientGroup.mk'_surjective θ
  have hA3 : IsPGroup 3 A := IsPGroup.of_card (n := 3) (by rw [hD.card_eq]; norm_num)
  have hT3 : IsPGroup 3 (A.subgroupOf L) :=
    hA3.comap_of_ker_isPGroup L.subtype (IsPGroup.ker_isPGroup_of_injective L.subtype_injective)
  obtain ⟨S, hAS⟩ := hT3.exists_le_sylow
  set P := S.mapSurjective hπs with hP
  have hEP : (A.subgroupOf L).map π ≤ (P : Subgroup (↥L ⧸ θ)) := by
    rw [hP, Sylow.coe_mapSurjective]
    exact Subgroup.map_mono hAS
  have hE9 : Nat.card ((A.subgroupOf L).map π) = 9 := by
    rw [hπ, card_map_mk_subgroupOf hD.isElemAbelian, h9]
  have hZE := KFacts.KS14.j2_inf_centralizer_le_of_card_nine h415 hJ P hEP hE9
  obtain ⟨hZ3, -⟩ := j2_sylow_facts h415 hJ P
  have hZne : (P : Subgroup (↥L ⧸ θ)) ⊓ Subgroup.centralizer ((P : Subgroup (↥L ⧸ θ)) :
      Set (↥L ⧸ θ)) ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hZ3
    omega
  obtain ⟨⟨z, hzZ⟩, hz1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hZne
  have hz1' : z ≠ 1 := fun h => hz1 (Subtype.ext h)
  obtain ⟨d', hd'A, hd'z⟩ := hZE hzZ
  have hd'S : d' ∈ (S : Subgroup ↥L) := hAS hd'A
  have hd'Z : π d' ∈ Subgroup.centralizer ((P : Subgroup (↥L ⧸ θ)) : Set (↥L ⧸ θ)) := by
    rw [hd'z]
    exact hzZ.2
  refine ⟨(d' : G), Subgroup.mem_subgroupOf.mp hd'A, fun h => hz1' ?_, d'.2, S, hd'S,
    le_centralizer_of_mk_mem_center S hd'S hd'Z⟩
  rw [← hd'z, show d' = 1 from Subtype.ext h, map_one]

theorem allPointsHJ_of_j2 (h134 : Item134) (h48 : Sec4.Item4_8) {A L : Subgroup G} {c : G}
    (h : Sec14Std G A c L)
    (hJ : Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* CFSG.Blueprint.NativeSporadic.J2)) :
    AllPointsHJ A := by
  obtain ⟨d, hdA, hd1, hdc⟩ := exists_three_central_of_j2 h.toSec13Data hJ
  exact fun e he => exists_hj_of_hj_point h134 h48 Sec4.Sporadic.rank3II_4_15 h
    h.toSec13Data.zpowers_mem_omegaA h.toSec13Data.mem_lA hJ hdA hd1 hdc he

theorem concl142_of_j2 (h134 : Item134) (h48 : Sec4.Item4_8)
    {A L : Subgroup G} {c : G} (h : Sec14Std G A c L)
    (hJ : Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* CFSG.Blueprint.NativeSporadic.J2)) :
    Concl142 A (lB A) :=
  concl142_of_allPointsHJ h (allPointsHJ_of_j2 h134 h48 h hJ)

end Certificates

end CFSG.RankThree.PartTwo.Sec14

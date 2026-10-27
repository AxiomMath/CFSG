module

public import CFSG.LocalAnalysis.UniqueFourCatalog.Standing4Basic
import CFSG.LocalAnalysis.RankThreeUC.CatalogClosureSporOrder
import CFSG.RankThree.PartTwo.Census.Sporadic.J3
import CFSG.RankThree.PartTwo.Census.Sporadic.McL
import CFSG.RankThree.PartTwo.Census.Sporadic.Ly
import CFSG.RankThree.PartTwo.Census.Sporadic.Suz
import CFSG.RankThree.PartTwo.Census.Sporadic.ON
import CFSG.RankThree.PartTwo.Census.Sporadic.Co3
import CFSG.RankThree.PartTwo.Census.Sporadic.HN
import CFSG.RankThree.PartOne.CTP.SporadicOrders
import CFSG.LocalAnalysis.SectionRank.Sporadic.MathieuLocal
import CFSG.LocalAnalysis.SectionRank.Sporadic.J2Local
import CFSG.LocalAnalysis.SectionRank.Sporadic.J4Local
import CFSG.LocalAnalysis.SectionRank.Sporadic.HSLocal
import CFSG.LocalAnalysis.SectionRank.Sporadic.HeLocal
import CFSG.LocalAnalysis.SectionRank.Sporadic.RuLocal

public section

namespace CFSG.Yardstones.Mf4cdcdf2e013

open CFSG.Blueprint
open scoped commutatorElement
open CFSG.LocalAnalysis.RankThreeUC (localRank_le_two_of_cubic cube_free_7920 cube_free_95040
  cube_free_443520 cube_free_10200960 cube_free_244823040 cube_free_175560 cube_free_604800
  cube_free_86775571046077562880 cube_free_44352000 cube_free_4030387200
  cube_free_145926144000 cube_free_50232960)
open CFSG.RankThree.PartTwo.Census (localRank_three_le_two_of_centralizer card_centralizer_j3P
  not_isCharTwoType_McL not_isCharTwoType_Ly not_isCharTwoType_Suz not_isCharTwoType_ON
  not_isCharTwoType_Co3 not_isCharTwoType_HN)

theorem Standing4.false_of_card_cubic {G H : Type} [Group G] [Finite G] [Group H]
    (hS : Standing4 G) (e : G ≃* H) {N : ℕ} (E : Finset ℕ)
    (hN : Nat.card H = N)
    (hE : ∀ r ∈ E, r.Prime → r ≠ 2 → ∃ x y : H, ⁅x, y⁆ ≠ 1 ∧
      Nat.card (Subgroup.closure ({x, y} : Set H)) = r ^ 3 ∧ ¬ r ^ 4 ∣ N)
    (hcube : ∀ r : ℕ, r.Prime → r ≠ 2 → r ∉ E → ¬ r ^ 3 ∣ N) : False :=
  hS.false_of_card e E hN (fun r hr hrp hr2 => by
    obtain ⟨x, y, hxy, hc, h4⟩ := hE r hr hrp hr2
    exact localRank_le_two_of_cubic hrp (hN ▸ h4) hxy hc) hcube

theorem Standing4.false_of_M11
    {G : Type} [Group G] [Finite G] (hS : Standing4 G) (e : G ≃* NativeSporadic.Carrier .M11) :
    False :=
  hS.false_of_card_cubic e ∅ CFSG.Sporadic.Mathieu.card_M11
    (fun _ h => by simp at h) cube_free_7920

theorem Standing4.false_of_M12
    {G : Type} [Group G] [Finite G] (hS : Standing4 G) (e : G ≃* NativeSporadic.Carrier .M12) :
    False := by
  refine hS.false_of_card_cubic e {3} CFSG.Sporadic.Mathieu.card_M12 ?_ cube_free_95040
  intro r hr hrp hr2
  obtain rfl : r = 3 := by simpa using hr
  obtain ⟨x, y, -, -, -, hxy, -, -, hc, -⟩ := CFSG.SectionRank.M12_sylow3_cubic_witness
  exact ⟨x, y, hxy, hc, by norm_num⟩

theorem Standing4.false_of_M22
    {G : Type} [Group G] [Finite G] (hS : Standing4 G) (e : G ≃* NativeSporadic.Carrier .M22) :
    False :=
  hS.false_of_card_cubic e ∅ CFSG.Sporadic.Mathieu.card_M22
    (fun _ h => by simp at h) cube_free_443520

theorem Standing4.false_of_M23
    {G : Type} [Group G] [Finite G] (hS : Standing4 G) (e : G ≃* NativeSporadic.Carrier .M23) :
    False :=
  hS.false_of_card_cubic e ∅ CFSG.RankThree.PartOne.CTP.card_M23
    (fun _ h => by simp at h) cube_free_10200960

theorem Standing4.false_of_M24
    {G : Type} [Group G] [Finite G] (hS : Standing4 G) (e : G ≃* NativeSporadic.Carrier .M24) :
    False := by
  refine hS.false_of_card_cubic e {3} CFSG.Sporadic.Mathieu.card_M24 ?_ cube_free_244823040
  intro r hr hrp hr2
  obtain rfl : r = 3 := by simpa using hr
  obtain ⟨x, y, -, -, -, hxy, -, -, hc, -⟩ := CFSG.SectionRank.M24_sylow3_cubic_witness
  exact ⟨x, y, hxy, hc, by norm_num⟩

theorem Standing4.false_of_J1
    {G : Type} [Group G] [Finite G] (hS : Standing4 G) (e : G ≃* NativeSporadic.Carrier .J1) :
    False :=
  hS.false_of_card_cubic e ∅ CFSG.Sporadic.J1.card_J1
    (fun _ h => by simp at h) cube_free_175560

theorem Standing4.false_of_J2
    {G : Type} [Group G] [Finite G] (hS : Standing4 G) (e : G ≃* NativeSporadic.Carrier .J2) :
    False := by
  refine hS.false_of_card_cubic e {3} CFSG.Sporadic.J2.card_J2 ?_ cube_free_604800
  intro r hr hrp hr2
  obtain rfl : r = 3 := by simpa using hr
  obtain ⟨x, y, -, -, -, hxy, -, -, hc, -⟩ := CFSG.SectionRank.J2_sylow3_cubic_witness
  exact ⟨x, y, hxy, hc, by norm_num⟩

theorem Standing4.false_of_J4
    {G : Type} [Group G] [Finite G] (hS : Standing4 G) (e : G ≃* NativeSporadic.Carrier .J4) :
    False := by
  refine hS.false_of_card_cubic e {3, 11} CFSG.Sporadic.J4.card_J4 ?_
    cube_free_86775571046077562880
  intro r hr hrp hr2
  simp only [Finset.mem_insert, Finset.mem_singleton] at hr
  rcases hr with rfl | rfl
  · obtain ⟨x, y, -, -, -, hxy, -, -, hc, -⟩ := CFSG.SectionRank.J4_sylow3_cubic_witness
    exact ⟨x, y, hxy, hc, by norm_num⟩
  · obtain ⟨x, y, -, -, -, hxy, -, -, hc, -⟩ := CFSG.SectionRank.J4_sylow11_cubic_witness
    exact ⟨x, y, hxy, hc, by norm_num⟩

theorem Standing4.false_of_HS
    {G : Type} [Group G] [Finite G] (hS : Standing4 G) (e : G ≃* NativeSporadic.Carrier .HS) :
    False := by
  refine hS.false_of_card_cubic e {5} CFSG.Sporadic.HS.card_HS ?_ cube_free_44352000
  intro r hr hrp hr2
  obtain rfl : r = 5 := by simpa using hr
  obtain ⟨x, y, -, -, -, hxy, -, -, hc, -⟩ := CFSG.SectionRank.HS_sylow5_cubic_witness
  exact ⟨x, y, hxy, hc, by norm_num⟩

theorem Standing4.false_of_He
    {G : Type} [Group G] [Finite G] (hS : Standing4 G) (e : G ≃* NativeSporadic.Carrier .He) :
    False := by
  refine hS.false_of_card_cubic e {3, 7} CFSG.Sporadic.He.card_He ?_ cube_free_4030387200
  intro r hr hrp hr2
  simp only [Finset.mem_insert, Finset.mem_singleton] at hr
  rcases hr with rfl | rfl
  · obtain ⟨x, y, -, -, -, hxy, -, -, hc, -⟩ := CFSG.SectionRank.He_sylow3_cubic_witness
    exact ⟨x, y, hxy, hc, by norm_num⟩
  · obtain ⟨x, y, -, -, -, hxy, -, -, hc, -⟩ := CFSG.SectionRank.He_sylow7_cubic_witness
    exact ⟨x, y, hxy, hc, by norm_num⟩

theorem Standing4.false_of_Ru
    {G : Type} [Group G] [Finite G] (hS : Standing4 G) (e : G ≃* NativeSporadic.Carrier .Ru) :
    False := by
  refine hS.false_of_card_cubic e {3, 5} CFSG.Sporadic.Ru.card_Ru ?_ cube_free_145926144000
  intro r hr hrp hr2
  simp only [Finset.mem_insert, Finset.mem_singleton] at hr
  rcases hr with rfl | rfl
  · obtain ⟨x, y, -, -, -, hxy, -, -, hc, -⟩ := CFSG.SectionRank.Ru_sylow3_cubic_witness
    exact ⟨x, y, hxy, hc, by norm_num⟩
  · obtain ⟨x, y, -, -, -, hxy, -, -, hc, -⟩ := CFSG.SectionRank.Ru_sylow5_cubic_witness
    exact ⟨x, y, hxy, hc, by norm_num⟩

theorem Standing4.false_of_J3
    {G : Type} [Group G] [Finite G] (hS : Standing4 G) (e : G ≃* NativeSporadic.Carrier .J3) :
    False := by
  refine hS.false_of_card (e.trans CFSG.Sporadic.Schreier.j3PermEquiv) {3}
    ((Nat.card_congr CFSG.Sporadic.Schreier.j3PermEquiv.toEquiv).symm.trans
      CFSG.Sporadic.J3.card_J3) ?_ cube_free_50232960
  intro _ r hr _ _
  obtain rfl : r = 3 := by simpa using hr
  exact localRank_three_le_two_of_centralizer fun t ht h9 => by
    rw [card_centralizer_j3P ht] at h9
    exact absurd h9 (by norm_num)

theorem Standing4.false_of_McL
    {G : Type} [Group G] [Finite G] (hS : Standing4 G) (e : G ≃* NativeSporadic.Carrier .McL) :
    False := by
  have : Finite NativeSporadic.McL := Finite.of_equiv G e.toEquiv
  exact hS.false_of_not_isCharTwoType e not_isCharTwoType_McL

theorem Standing4.false_of_Ly
    {G : Type} [Group G] [Finite G] (hS : Standing4 G) (e : G ≃* NativeSporadic.Carrier .Ly) :
    False := by
  have : Finite NativeSporadic.Ly := Finite.of_equiv G e.toEquiv
  exact hS.false_of_not_isCharTwoType e not_isCharTwoType_Ly

theorem Standing4.false_of_Suz
    {G : Type} [Group G] [Finite G] (hS : Standing4 G) (e : G ≃* NativeSporadic.Carrier .Suz) :
    False := by
  have : Finite NativeSporadic.Suz := Finite.of_equiv G e.toEquiv
  exact hS.false_of_not_isCharTwoType e not_isCharTwoType_Suz

theorem Standing4.false_of_ON
    {G : Type} [Group G] [Finite G] (hS : Standing4 G) (e : G ≃* NativeSporadic.Carrier .ONan) :
    False := by
  have : Finite NativeSporadic.ON := Finite.of_equiv G e.toEquiv
  exact hS.false_of_not_isCharTwoType e not_isCharTwoType_ON

theorem Standing4.false_of_Co3
    {G : Type} [Group G] [Finite G] (hS : Standing4 G) (e : G ≃* NativeSporadic.Carrier .Co3) :
    False := by
  have : Finite NativeSporadic.Co3 := Finite.of_equiv G e.toEquiv
  exact hS.false_of_not_isCharTwoType e not_isCharTwoType_Co3

theorem Standing4.false_of_HN
    {G : Type} [Group G] [Finite G] (hS : Standing4 G) (e : G ≃* NativeSporadic.Carrier .HN) :
    False := by
  have : Finite NativeSporadic.HN := Finite.of_equiv G e.toEquiv
  exact hS.false_of_not_isCharTwoType e not_isCharTwoType_HN

end CFSG.Yardstones.Mf4cdcdf2e013

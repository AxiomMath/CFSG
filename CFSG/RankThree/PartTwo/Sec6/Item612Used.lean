module

public import CFSG.RankThree.PartTwo.Sec6.Item65UsedStatement
public import CFSG.RankThree.PartTwo.Sec4.Statements
public import CFSG.RankThree.PartTwo.Sec21.PairExistence
import CFSG.RankThree.PartTwo.Sec6.Item612
import CFSG.RankThree.PartTwo.Sec5.Tools
public import CFSG.RankThree.PartTwo.Sec6.Statements

public section

namespace CFSG.RankThree.PartTwo.Sec6

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

theorem exists_pair_of_mem_fourGroupsPlusUsed (hG : PartTwoStanding G) (h45 : Sec4.Item4_5)
    (h49 : Sec4.Item4_9) (h65 : Item6_5Used) (h68 : Item6_8) {A E U : Subgroup G}
    (hA : A ∈ partTwoS G) (hE : E ∈ collectionIn (partTwoE G) A) (hU : U ∈ fourGroupsPlus E)
    {c : G} (hcE : c ∈ E) (hc1 : c ≠ 1)
    (hV : ⁅inSubgroup (CFSG.pCore 2) (Subgroup.centralizer (U : Set G)) ⊓
      Subgroup.centralizer {c}, E⁆ ≠ ⊥) :
    ∃ c' ∈ E, c' ≠ 1 ∧ ∃ L ∈ lZeroStarAt A c', U ≤ Subgroup.normalizer (L : Set G) ∧
      ⁅L, U⁆ = L ∧
      ⁅inSubgroup (CFSG.pCore 2) (Subgroup.centralizer (U : Set G)) ⊓ Subgroup.centralizer {c'},
        E⁆ ≤ Subgroup.normalizer (L : Set G) ∧
      ⁅L, ⁅inSubgroup (CFSG.pCore 2) (Subgroup.centralizer (U : Set G)) ⊓
        Subgroup.centralizer {c'}, E⁆⁆ = L := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨hEmem, hEA⟩ := hE
  have hAab := hA.1.1
  have hEU : E ≤ Subgroup.centralizer (U : Set G) := (mem_fourGroupsPlus_iff.mp hU).2
  set Q := inSubgroup (CFSG.pCore 2) (Subgroup.centralizer (U : Set G)) with hQ
  set P : Set (G × Subgroup G) := {p | p.1 ∈ E ∧ p.1 ≠ 1 ∧ p.2 ∈ thetaComponentsAt 3 p.1 ∧
    ⁅Q ⊓ Subgroup.centralizer {p.1}, E⁆ ≤ Subgroup.normalizer (p.2 : Set G) ∧
    ¬ ⁅p.2, ⁅Q ⊓ Subgroup.centralizer {p.1}, E⁆⁆ ≤ inSubgroup (aschbacherSolvableCore 3) p.2}
    with hP
  have hPne : P.Nonempty := by
    obtain ⟨L, hL, hVL, hLV⟩ := exists_mem_thetaComponentsAt_moved hG h45 hA ⟨hEmem, hEA⟩ hU.1
      le_rfl hEU hcE (hEU hcE) hc1 hV
    exact ⟨(c, L), hcE, hc1, hL, hVL, hLV⟩
  obtain ⟨⟨c', L⟩, ⟨hc'E, hc'1, hL, hVL, hLV⟩, hmax⟩ := Set.exists_max_image P
    (fun p => Nat.card (p.2 ⧸ aschbacherSolvableCore 3 p.2)) (Set.toFinite P) hPne
  obtain ⟨hV2, hVS, hEV, hVF⟩ := commutator_inf_props (F := E) ⟨hEmem, hEA⟩ hU.1 le_rfl hc'E
  obtain ⟨hLV', hEL, hLE, hL0, hDE⟩ := props_of_moved hG h45 h49 hA ⟨hEmem, hEA⟩ hc'E hc'1 hL hV2
    (hVS.trans inf_le_right) hEV hVF.le hVL hLV
  set C := thetaQuotCentralizer L with hC
  set D := A ⊓ C with hD
  have hc'D : c' ∈ D := ⟨hEA hc'E, mem_thetaQuotCentralizer_of_mem_thetaComponentsAt hL⟩
  have hED : ¬ E ≤ D := by
    intro hED
    apply hLV
    rw [commutator_le_theta_iff hVL, hVF, Subgroup.commutator_le]
    intro v hv e he
    rw [commutatorElement_def]
    exact C.mul_mem (conj_mem_thetaQuotCentralizer (hED he).2 (hVL hv)) (inv_mem (hED he).2)
  have hcardD : Nat.card D = 3 ∨ Nat.card D = 9 := by
    have hdvd := Subgroup.card_dvd_of_le hDE
    rw [hEmem.2.1] at hdvd
    have hne27 : Nat.card D ≠ 27 := fun h27 =>
      hED (Subgroup.eq_of_le_of_card_ge hDE (by rw [hEmem.2.1, h27])).ge
    have hne1 : Nat.card D ≠ 1 := fun h1 => hc'1 (by
      have := (Subgroup.eq_bot_of_card_eq D h1) ▸ hc'D
      exact Subgroup.mem_bot.mp this)
    have : Nat.card D ∈ Nat.divisors 27 := Nat.mem_divisors.mpr ⟨hdvd, by norm_num⟩
    have h27 : Nat.divisors 27 = {1, 3, 9, 27} := by decide
    rw [h27] at this
    simp only [Finset.mem_insert, Finset.mem_singleton] at this
    omega
  rcases hcardD with hD3 | hD9
  ·
    have hDz := le_zpowers_of_card_eq_three hAab inf_le_left hc'D hc'1 hD3
    have hLs := mem_lZeroStarAt_of_inf_le_zpowers h45 hG hA ⟨hEmem, hEA⟩ hc'E hc'1 hL hL0 hDz
    have hUL : U ≤ Subgroup.normalizer (L : Set G) :=
      h68 G hG A hA E ⟨hEmem, hEA⟩ L ⟨mem_thetaComponentFamily_iff.mpr ⟨c', hc'E, hc'1, hL⟩,
        (lZeroStarAt_subset_lZeroStar A c').trans (lZeroStar_subset_lStar A) hLs⟩ U hU
    have hLU := commutator_eq_of_mem_fourGroups hA ⟨hEmem, hEA⟩ hU.1 hc'E hc'1 (hEU hc'E) hL hEL
      hLE hUL hVS hVL hLV
    exact ⟨c', hc'E, hc'1, L, hLs, hUL, hLU, hVL, hLV'⟩
  ·
    exfalso
    have hLA : L ∈ thetaComponentFamily 3 A :=
      mem_thetaComponentFamily_iff.mpr ⟨c', hEA hc'E, hc'1, hL⟩
    obtain ⟨b, hbD, hb1, K, hK, hYK⟩ := (h65 G hG A hA L hLA D
      (Sec5.isElemAbelian_of_le hAab inf_le_left) hD9 le_rfl).1 E
      ⟨hEmem, hEA.trans le_sup_left⟩ hDE
    obtain ⟨hVK, hKV, hlt⟩ := step_of_fourGroupsPlus hG h45 hA ⟨hEmem, hEA⟩ hU.1 hc'E hc'1 hL hVL
      hLV hDE hbD hb1 hK hYK
    have hmem : (b, K) ∈ P := ⟨hDE hbD, hb1, hK, hVK, hKV⟩
    exact absurd (hmax _ hmem) (not_le.mpr hlt)

theorem rank3II_6_12_sec21Used (h45 : Sec4.Item4_5) (h49 : Sec4.Item4_9) (h65 : Item6_5Used)
    (h68 : Item6_8) : Sec21.Item612 := by
  intro G _ _ hG A hA E hE U hU
  have hEmem := hE.1
  have hEab := hEmem.1
  have hE3 : IsPGroup 3 E := Sec5.isPGroup_of_isElemAbelian hEab
  obtain ⟨hU2, hU1⟩ := isPGroup_two_and_ne_bot_of_mem_fourGroups hU
  rcases mem_fourGroupsPlus_or_mem_fourGroupsMinus hE3 hU with hUp | ⟨hUm, -⟩
  · have hEU : E ≤ Subgroup.centralizer (U : Set G) := (mem_fourGroupsPlus_iff.mp hUp).2
    have hB : E ⊓ Subgroup.centralizer (U : Set G) = E := inf_eq_left.mpr hEU
    have hE1 : E ≠ ⊥ := fun h => by
      have := hEmem.2.1
      rw [h, Subgroup.card_bot] at this
      norm_num at this
    obtain ⟨c, hcE, hc1, hV⟩ := exists_commutator_inf_centralizer_ne_bot hG.charTwoType hU2 hU1
      hEab (by rw [hEmem.2.1]; norm_num) hEU le_rfl hE1
    obtain ⟨c', hc'E, hc'1, L, hL, hUL, hLU, hVL, hLV⟩ :=
      exists_pair_of_mem_fourGroupsPlusUsed hG h45 h49 h65 h68 hA hE hUp hcE hc1 hV
    refine ⟨c', ⟨hc'E, hEU hc'E⟩, hc'1, L, hL, hUL, hLU, ?_, ?_⟩
    · rw [Sec21.sixTwelveV, hB]
      exact hVL
    · rw [Sec21.sixTwelveV, hB]
      exact hLV
  · have hB9 := card_inf_centralizer_of_mem_fourGroupsMinus (Late.isE27_of_mem_partTwoE hEmem) hUm
    have hB1 : E ⊓ Subgroup.centralizer (U : Set G) ≠ ⊥ := fun h => by
      rw [h, Subgroup.card_bot] at hB9
      norm_num at hB9
    obtain ⟨c, hcB, hc1, hV⟩ := exists_commutator_inf_centralizer_ne_bot hG.charTwoType hU2 hU1
      (Sec5.isElemAbelian_of_le hEab inf_le_left) hB9.ge inf_le_right le_rfl hB1
    obtain ⟨L, hL, hUL, hLU, hVL, hLV⟩ := exists_pair_of_mem_fourGroupsMinus hG h45 h49 hA hE hUm
      inf_le_left inf_le_right hcB.1 hcB.2 hc1 hV
    exact ⟨c, hcB, hc1, L, hL, hUL, hLU, hVL, hLV⟩

theorem rank3II_6_12Used (h45 : Sec4.Item4_5) (h49 : Sec4.Item4_9) (h65 : Item6_5Used)
    (h68 : Item6_8) : Item6_12 := by
  intro G _ _ hG A hA E hE U hU
  obtain ⟨c, hc, hc1, L, hL, h⟩ := rank3II_6_12_sec21Used h45 h49 h65 h68 G hG A hA E hE U hU
  exact ⟨c, hc.1, hc1, L, hL, h⟩

end CFSG.RankThree.PartTwo.Sec6

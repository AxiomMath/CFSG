module

public import CFSG.RankThree.PartTwo.Sec6.Item612Plus
import CFSG.RankThree.PartTwo.Sec5.Tools
public import CFSG.RankThree.PartTwo.Sec6.Item612Core
public import CFSG.RankThree.PartTwo.Sec6.Statements

public section

namespace CFSG.RankThree.PartTwo.Sec6

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

theorem commutator_eq_of_mem_fourGroups {A E U V : Subgroup G} (hA : A ∈ partTwoS G)
    (hE : E ∈ collectionIn (partTwoE G) A) (hU : U ∈ fourGroups E) {c : G} (hcE : c ∈ E)
    (hc1 : c ≠ 1) (hcU : c ∈ Subgroup.centralizer (U : Set G)) {L : Subgroup G}
    (hL : L ∈ thetaComponentsAt 3 c) (hEL : E ≤ Subgroup.normalizer (L : Set G))
    (hLE : ⁅L, E⁆ = L) (hUL : U ≤ Subgroup.normalizer (L : Set G))
    (hVQ : V ≤ inSubgroup (CFSG.pCore 2) (Subgroup.centralizer (U : Set G)) ⊓
      Subgroup.centralizer {c})
    (hVL : V ≤ Subgroup.normalizer (L : Set G))
    (hLV : ¬ ⁅L, V⁆ ≤ inSubgroup (aschbacherSolvableCore 3) L) : ⁅L, U⁆ = L := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hEmem, hEA⟩ := hE
  have hLp := isPerfect_of_mem_thetaComponentsAt hL
  have hLq := isQuasisimple_of_mem_thetaComponentsAt hL
  obtain ⟨hEU, hUab, hU4⟩ := mem_fourGroups_iff.mp hU
  have hU2 : IsPGroup 2 U := IsPGroup.of_card (n := 2) (by rw [hU4]; norm_num)
  have hUUab : ⁅U, U⁆ = ⊥ := by
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
    intro u hu
    exact Subgroup.mem_centralizer_iff.mpr fun v hv =>
      congrArg Subtype.val (hUab.1.is_comm.comm ⟨v, hv⟩ ⟨u, hu⟩)
  have hEθ : ∀ T : Subgroup G, T ≤ inSubgroup (aschbacherSolvableCore 3) L → IsPGroup 2 T →
      E ≤ Subgroup.normalizer (T : Set G) → ⁅T, E⁆ = ⊥ := by
    intro T hT hT2 hET
    refine commutator_eq_bot_of_mem_partTwoS hA (hEA hcE) hc1 hEA (hT.trans ?_) hT2 hET
    rw [theta_eq_inf_of_mem_thetaComponentsAt hL]
    exact inf_le_right
  set Q := inSubgroup (CFSG.pCore 2) (Subgroup.centralizer (U : Set G)) with hQ
  have hQ2 : IsPGroup 2 (Q ⊓ Subgroup.centralizer ({c} : Set G) : Subgroup G) :=
    (CFSG.pCore_isPGroup.map _).to_le inf_le_left
  have hQN : Subgroup.centralizer (U : Set G) ⊓ Subgroup.centralizer {c} ≤
      Subgroup.normalizer ((Q ⊓ Subgroup.centralizer {c} : Subgroup G) : Set G) := by
    refine (inf_le_inf (Subgroup.le_normalizer.trans
      (CFSG.LieType.BorelTits.normalizer_le_normalizer_map_of_characteristic
        (CFSG.pCore 2 (Subgroup.centralizer (U : Set G))))) Subgroup.le_normalizer).trans
      Subgroup.inf_normalizer_le_normalizer_inf
  have hUc : U ≤ Subgroup.centralizer ({c} : Set G) := fun u hu =>
    Subgroup.mem_centralizer_singleton_iff.mpr (Subgroup.mem_centralizer_iff.mp hcU u hu)
  refine commutator_eq_of_not_le_theta hLp hLq hUL fun hUθ => hLV ?_
  exact commutator_le_theta_of_le_thetaQuotCentralizer_abelian hLp hLq
    (Sec5.isPGroup_of_isElemAbelian hEmem.1) hEL hLE hEθ hU2 hUUab hUL
    ((commutator_le_theta_iff hUL).mp hUθ) hEU hVL hVQ hQ2 hQN
    (le_centralizer_of_mem_thetaComponentsAt hL) hUc

theorem mem_thetaQuotCentralizer_of_mem_thetaComponentsAt {c : G} {L : Subgroup G}
    (hL : L ∈ thetaComponentsAt 3 c) : c ∈ thetaQuotCentralizer L := by
  have hLc := le_centralizer_of_mem_thetaComponentsAt hL
  have hcC : c ∈ Subgroup.centralizer (L : Set G) :=
    Subgroup.mem_centralizer_iff.mpr fun l hl => Subgroup.mem_centralizer_singleton_iff.mp (hLc hl)
  refine mem_thetaQuotCentralizer_iff.mpr ⟨Subgroup.centralizer_le_normalizer _ hcC,
    fun l hl => ?_⟩
  have h1 : l * c = c * l := Subgroup.mem_centralizer_iff.mp hcC l hl
  rw [show l⁻¹ * (c * l * c⁻¹) = 1 by rw [← h1]; group]
  exact one_mem _

theorem mem_lZeroStarAt_of_inf_le_zpowers (h45 : Sec4.Item4_5) (hG : PartTwoStanding G)
    {A E L : Subgroup G} (hA : A ∈ partTwoS G) (hE : E ∈ collectionIn (partTwoE G) A) {c : G}
    (hcE : c ∈ E) (hc1 : c ≠ 1) (hL : L ∈ thetaComponentsAt 3 c) (hL0 : L ∈ lZero E)
    (hD : A ⊓ thetaQuotCentralizer L ≤ Subgroup.zpowers c) : L ∈ lZeroStarAt A c := by
  obtain ⟨hEmem, hEA⟩ := hE
  have hAab := hA.1.1
  have hAL := le_normalizer_of_mem_thetaComponentsAt h45 hG.toTheoremFourHyp hAab (hEA hcE) hc1
  exact ⟨hL, lZero_subset_lZeroUnion hEmem hEA hL0,
    mem_lStar_of_inf_le_zpowers hAab (hEA hcE) hc1 hL (hAL L hL) hD⟩

theorem le_zpowers_of_card_eq_three {A D : Subgroup G} (hA : CFSG.Assembly.IsElemAbelian 3 A)
    (hDA : D ≤ A) {c : G} (hcD : c ∈ D) (hc1 : c ≠ 1) (hD3 : Nat.card D = 3) :
    D ≤ Subgroup.zpowers c := by
  have hc3 : orderOf c = 3 := orderOf_eq_prime (hA.2 c (hDA hcD)) hc1
  exact (Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hcD)
    (by rw [hD3, Nat.card_zpowers, hc3])).ge


theorem exists_pair_of_mem_fourGroupsMinus (hG : PartTwoStanding G) (h45 : Sec4.Item4_5)
    (h49 : Sec4.Item4_9) {A E U F : Subgroup G} (hA : A ∈ partTwoS G)
    (hE : E ∈ collectionIn (partTwoE G) A) (hU : U ∈ fourGroupsMinus E) (hFE : F ≤ E)
    (hFU : F ≤ Subgroup.centralizer (U : Set G)) {c : G} (hcE : c ∈ E)
    (hcU : c ∈ Subgroup.centralizer (U : Set G)) (hc1 : c ≠ 1)
    (hV : ⁅inSubgroup (CFSG.pCore 2) (Subgroup.centralizer (U : Set G)) ⊓
      Subgroup.centralizer {c}, F⁆ ≠ ⊥) :
    ∃ L ∈ lZeroStarAt A c, U ≤ Subgroup.normalizer (L : Set G) ∧ ⁅L, U⁆ = L ∧
      ⁅inSubgroup (CFSG.pCore 2) (Subgroup.centralizer (U : Set G)) ⊓ Subgroup.centralizer {c},
        F⁆ ≤ Subgroup.normalizer (L : Set G) ∧
      ⁅L, ⁅inSubgroup (CFSG.pCore 2) (Subgroup.centralizer (U : Set G)) ⊓
        Subgroup.centralizer {c}, F⁆⁆ = L := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨hEmem, hEA⟩ := hE
  have hAab := hA.1.1
  have hE3 : IsPGroup 3 E := Sec5.isPGroup_of_isElemAbelian hEmem.1
  set Q := inSubgroup (CFSG.pCore 2) (Subgroup.centralizer (U : Set G)) with hQ
  set V := ⁅Q ⊓ Subgroup.centralizer {c}, F⁆ with hVdef
  have hirr : ∀ X : Subgroup G, X ≤ U → E ≤ Subgroup.normalizer (X : Set G) → X = ⊥ ∨ X = U := by
    rcases mem_fourGroupsPlus_or_mem_fourGroupsMinus hE3 hU.1 with hp | ⟨-, hirr⟩
    · exact absurd hU (Set.disjoint_left.mp (disjoint_fourGroupsPlus_fourGroupsMinus E) hp)
    · exact hirr
  obtain ⟨L, hL, hVL, hLV⟩ :=
    exists_mem_thetaComponentsAt_moved hG h45 hA ⟨hEmem, hEA⟩ hU.1 hFE hFU hcE hcU hc1 hV
  obtain ⟨hV2, hVS, hEV, hVF⟩ := commutator_inf_props ⟨hEmem, hEA⟩ hU.1 hFE hcE
  have hVE : V ≤ ⁅V, E⁆ := by
    calc V = ⁅V, F⁆ := hVF
      _ ≤ ⁅V, E⁆ := Subgroup.commutator_mono le_rfl hFE
  obtain ⟨hLV', hEL, hLE, hL0, hDE⟩ := props_of_moved hG h45 h49 hA ⟨hEmem, hEA⟩ hcE hc1 hL hV2
    (hVS.trans inf_le_right) hEV hVE hVL hLV
  have hAL := le_normalizer_of_mem_thetaComponentsAt h45 hG.toTheoremFourHyp hAab (hEA hcE) hc1
  have hUc : U ≤ Subgroup.centralizer ({c} : Set G) := fun u hu =>
    Subgroup.mem_centralizer_singleton_iff.mpr (Subgroup.mem_centralizer_iff.mp hcU u hu)
  have hUL : U ≤ Subgroup.normalizer (L : Set G) := by
    rw [hU.2]
    exact commutator_le_normalizer_of_mem_thetaComponentsAt hUc
      (fun L' hL' => hEA.trans (hAL L' hL')) hL
  have hLU := commutator_eq_of_mem_fourGroups hA ⟨hEmem, hEA⟩ hU.1 hcE hc1 hcU hL hEL hLE hUL hVS
    hVL hLV
  set C := thetaQuotCentralizer L with hC
  set D := A ⊓ C with hD
  have hCN := normalizer_le_normalizer_thetaQuotCentralizer L
  have hUC : U ⊓ C = ⊥ := by
    rcases hirr (U ⊓ C) inf_le_left
      ((le_inf (mem_fourGroups_iff.mp hU.1).1 (hEL.trans hCN)).trans
        Subgroup.inf_normalizer_le_normalizer_inf) with h | h
    · exact h
    · exfalso
      have hUC' : U ≤ C := h ▸ inf_le_right
      have := (commutator_le_theta_iff hUL).mpr hUC'
      rw [hLU] at this
      exact theta_ne_of_mem_thetaComponentsAt hL (le_antisymm (theta_le L) this)
  have hDU : D ≤ Subgroup.centralizer (U : Set G) := by
    intro d hd
    rw [Subgroup.mem_centralizer_iff]
    intro u hu
    have hdE : d ∈ E := hDE hd
    have h1 : ⁅d, u⁆ ∈ U := by
      rw [commutatorElement_def]
      exact U.mul_mem ((Subgroup.mem_normalizer_iff.mp
        ((mem_fourGroups_iff.mp hU.1).1 hdE) u).mp hu) (inv_mem hu)
    have h2 : ⁅d, u⁆ ∈ C := by
      rw [commutatorElement_def, show d * u * d⁻¹ * u⁻¹ = d * (u * d⁻¹ * u⁻¹) by group]
      exact C.mul_mem hd.2 (conj_mem_thetaQuotCentralizer (inv_mem hd.2) (hUL hu))
    have h3 : ⁅d, u⁆ = 1 := by
      have : ⁅d, u⁆ ∈ U ⊓ C := ⟨h1, h2⟩
      rwa [hUC, Subgroup.mem_bot] at this
    rw [commutatorElement_eq_one_iff_mul_comm] at h3
    exact h3.symm
  have hFD : ¬ F ≤ D := by
    intro hFD
    apply hLV
    rw [commutator_le_theta_iff hVL, hVF, Subgroup.commutator_le]
    intro v hv f hf
    rw [commutatorElement_def]
    exact C.mul_mem (conj_mem_thetaQuotCentralizer (hFD hf).2 (hVL hv)) (inv_mem (hFD hf).2)
  have hcD : c ∈ D := ⟨hEA hcE, mem_thetaQuotCentralizer_of_mem_thetaComponentsAt hL⟩
  have hB9 := card_inf_centralizer_of_mem_fourGroupsMinus (Late.isE27_of_mem_partTwoE hEmem) hU
  have hDB : D ≤ E ⊓ Subgroup.centralizer (U : Set G) := le_inf hDE hDU
  have hD3 : Nat.card D = 3 := by
    have hdvd := Subgroup.card_dvd_of_le hDB
    rw [hB9] at hdvd
    have hne9 : Nat.card D ≠ 9 := fun h9 =>
      hFD ((le_inf hFE hFU).trans (Subgroup.eq_of_le_of_card_ge hDB (by rw [hB9, h9])).ge)
    have hne1 : Nat.card D ≠ 1 := fun h1 => hc1 (by
      have := (Subgroup.eq_bot_of_card_eq D h1) ▸ hcD
      exact Subgroup.mem_bot.mp this)
    have : Nat.card D ∈ Nat.divisors 9 := Nat.mem_divisors.mpr ⟨hdvd, by norm_num⟩
    have h9 : Nat.divisors 9 = {1, 3, 9} := by decide
    rw [h9] at this
    simp only [Finset.mem_insert, Finset.mem_singleton] at this
    omega
  have hDz := le_zpowers_of_card_eq_three hAab inf_le_left hcD hc1 hD3
  exact ⟨L, mem_lZeroStarAt_of_inf_le_zpowers h45 hG hA ⟨hEmem, hEA⟩ hcE hc1 hL hL0 hDz, hUL, hLU,
    hVL, hLV'⟩


theorem exists_pair_of_mem_fourGroupsPlus (hG : PartTwoStanding G) (h45 : Sec4.Item4_5)
    (h49 : Sec4.Item4_9) (h65 : Item6_5) (h68 : Item6_8) {A E U : Subgroup G}
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
    obtain ⟨b, hbD, hb1, K, hK, hYK, -⟩ := (h65 G hG A hA L hLA D
      (Sec5.isElemAbelian_of_le hAab inf_le_left) hD9 le_rfl).1 E
      ⟨hEmem, hEA.trans le_sup_left⟩ hDE
    obtain ⟨hVK, hKV, hlt⟩ := step_of_fourGroupsPlus hG h45 hA ⟨hEmem, hEA⟩ hU.1 hc'E hc'1 hL hVL
      hLV hDE hbD hb1 hK hYK
    have hmem : (b, K) ∈ P := ⟨hDE hbD, hb1, hK, hVK, hKV⟩
    exact absurd (hmax _ hmem) (not_le.mpr hlt)


theorem isPGroup_two_and_ne_bot_of_mem_fourGroups {E U : Subgroup G} (hU : U ∈ fourGroups E) :
    IsPGroup 2 U ∧ U ≠ ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, -, hU4⟩ := mem_fourGroups_iff.mp hU
  refine ⟨IsPGroup.of_card (n := 2) (by rw [hU4]; norm_num), fun h => ?_⟩
  rw [h, Subgroup.card_bot] at hU4
  norm_num at hU4

theorem rank3II_6_12_sec21 (h45 : Sec4.Item4_5) (h49 : Sec4.Item4_9) (h65 : Item6_5)
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
      exists_pair_of_mem_fourGroupsPlus hG h45 h49 h65 h68 hA hE hUp hcE hc1 hV
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

theorem rank3II_6_12 (h45 : Sec4.Item4_5) (h49 : Sec4.Item4_9) (h65 : Item6_5)
    (h68 : Item6_8) : Item6_12 := by
  intro G _ _ hG A hA E hE U hU
  obtain ⟨c, hc, hc1, L, hL, h⟩ := rank3II_6_12_sec21 h45 h49 h65 h68 G hG A hA E hE U hU
  exact ⟨c, hc.1, hc1, L, hL, h⟩

end CFSG.RankThree.PartTwo.Sec6

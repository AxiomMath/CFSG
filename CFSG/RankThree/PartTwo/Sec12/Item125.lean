module

public import CFSG.RankThree.PartTwo.Sec12.Item125Act
import CFSG.RankThree.PartTwo.Sec6.Item612Local

public section

namespace CFSG.RankThree.PartTwo.Sec12

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.ABGLocalTools (IsSylowOf)

@[expose] def Gap125NonCentral : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec12Std G A c L → ∀ E : Subgroup G, Late.IsE27 E → E ≤ lcBar c L → c ∈ E →
      Nat.card (E ⊓ Sec4.thetaQuotCentralizer L : Subgroup G) = 9 →
      Nat.card (E ⊓ L : Subgroup G) = 9 →
      ¬ Subgroup.normalizer (E : Set G) ≤ Subgroup.normalizer (Subgroup.zpowers c : Set G) →
      ∃ P : Subgroup G, IsSylowOf 3 P
          (Subgroup.normalizer (E : Set G) ⊓ Subgroup.normalizer (Subgroup.zpowers c : Set G)) ∧
        ¬ E ⊓ Sec4.thetaQuotCentralizer L ≤ (Subgroup.center P).map P.subtype

@[expose] def Gap125CaseA : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec12Std G A c L → ∀ E : Subgroup G, Late.IsE27 E → E ≤ lcBar c L → c ∈ E →
      Nat.card (E ⊓ Sec4.thetaQuotCentralizer L : Subgroup G) = 3 →
      Subgroup.normalizer (E : Set G) ≤ Subgroup.normalizer (Subgroup.zpowers c : Set G)

variable {G : Type} [Group G] [Finite G]

theorem sup_eq_of_card_inf_nine {L E : Subgroup G} (hE : Late.IsE27 E)
    (hZ : Nat.card (Subgroup.center (L ⧸ aschbacherSolvableCore 3 L)) = 3)
    (hB9 : Nat.card (E ⊓ Sec4.thetaQuotCentralizer L : Subgroup G) = 9)
    (hEL9 : Nat.card (E ⊓ L : Subgroup G) = 9) :
    (E ⊓ Sec4.thetaQuotCentralizer L) ⊔ (E ⊓ L) = E := by
  have hexpE : ∀ x ∈ E, x ^ 3 = 1 := hE.1.2
  have hB3 : IsPGroup 3 (E ⊓ Sec4.thetaQuotCentralizer L : Subgroup G) := fun x =>
    ⟨1, Subtype.ext (by simpa using hexpE x x.2.1)⟩
  obtain ⟨x, hxEL, hxC⟩ : ∃ x ∈ E ⊓ L, x ∉ Sec4.thetaQuotCentralizer L := by
    by_contra hcon
    push Not at hcon
    have hle : E ⊓ L ≤ E ⊓ Sec4.thetaQuotCentralizer L ⊓ L := fun y hy =>
      ⟨⟨hy.1, hcon y hy⟩, hy.2⟩
    have h1 := (Subgroup.card_le_of_le hle).trans
      (card_inf_le_card_center_of_le_thetaQuotCentralizer hB3 inf_le_right)
    rw [hEL9, hZ] at h1
    norm_num at h1
  exact eq_of_card_nine_lt hE.2 (sup_le inf_le_left inf_le_left) le_sup_left hB9
    (Subgroup.mem_sup_right hxEL) fun h => hxC h.2

theorem item125_of_gaps (h122 : Item122) (h45 : Sec4.Item4_5)
    (hK2 : KFacts.KS12NormalizerMoves) (hK9 : KFacts.KS12OrderNine)
    (hG1 : Gap125NonCentral) (hG2 : Gap125CaseA) : Item125 := by
  intro G _ _ A c L h E hE hEL hcE
  have hty := h122 G A c L h
  have hL := h.mem_thetaComponentsAt
  have hZ : Nat.card (Subgroup.center (L ⧸ aschbacherSolvableCore 3 L)) = 3 :=
    card_center_thetaQuot_eq_three_of_item122 h122 h
  have hperf : commutator (L ⧸ aschbacherSolvableCore 3 L) = ⊤ := by
    have h1 := (isQuasisimple_thetaQuot_of_mem hL).1
    rwa [Group.isPerfect_def] at h1
  have hev := KFacts.two_dvd_card_of_item122_type hty
  have hLc : L ≤ Subgroup.centralizer ({c} : Set G) :=
    Sec6.le_centralizer_of_mem_thetaComponentsAt hL
  have hcC : c ∈ E ⊓ Sec4.thetaQuotCentralizer L :=
    ⟨hcE, mem_thetaQuotCentralizer_of_central h.mem_L hLc⟩
  have hcEL : c ∈ E ⊓ L := ⟨hcE, h.mem_L⟩
  have hdvd : ∀ S : Subgroup G, S ≤ E → Nat.card S ∣ 3 ^ 3 := fun S hS => by
    rw [show (3 : ℕ) ^ 3 = 27 by norm_num, ← hE.2]
    exact Subgroup.card_dvd_of_le hS
  obtain ⟨k, hk3, hk⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp (hdvd _ inf_le_left)
  interval_cases k
  ·
    rw [pow_zero, Subgroup.card_eq_one] at hk
    exact absurd (hk ▸ hcC) (by simpa using h.ne_one)
  ·
    exact hG2 G A c L h E hE hEL hcE (by rw [hk, pow_one])
  ·
    have hB9 : Nat.card (E ⊓ Sec4.thetaQuotCentralizer L : Subgroup G) = 9 := by
      rw [hk]
      norm_num
    obtain ⟨j, hj3, hj⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp (hdvd (E ⊓ L) inf_le_left)
    interval_cases j
    · rw [pow_zero, Subgroup.card_eq_one] at hj
      exact absurd (hj ▸ hcEL) (by simpa using h.ne_one)
    · exact (false_of_card_inf_L_eq_three hK9 h.partTwoF_eq hL h.mem_L h.ne_one hty hE hEL hcE
        hB9 (by rw [hj, pow_one])).elim
    ·
      have hEL9 : Nat.card (E ⊓ L : Subgroup G) = 9 := by
        rw [hj]
        norm_num
      by_contra hU
      obtain ⟨P, hP, hPB⟩ := hG1 G A c L h E hE hEL hcE hB9 hEL9 hU
      have hbar : Sec12StdBar G E c L :=
        { toPartTwoStanding := h.toPartTwoStanding
          partTwoF_eq := h.partTwoF_eq
          isE27 := hE
          mem_A := hcE
          ne_one := h.ne_one
          mem_thetaComponentsAt := hL
          mem_L := h.mem_L
          card_B := hB9
          sup_eq := sup_eq_of_card_inf_nine hE hZ hB9 hEL9
          exists_sylow := ⟨P, hP, hPB⟩ }
      exact hU (normalizer_le_of_sec12StdBar_of_list h45 hK2 hbar hty)
    ·
      exfalso
      have hEL' : E ⊓ L = E := Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [hj, hE.2]; norm_num)
      have hB3 : IsPGroup 3 (E ⊓ Sec4.thetaQuotCentralizer L : Subgroup G) := fun x =>
        ⟨1, Subtype.ext (by simpa using hE.1.2 x x.2.1)⟩
      have h1 := card_inf_le_card_center_of_le_thetaQuotCentralizer hB3 inf_le_right (L := L)
      have h2 : E ⊓ Sec4.thetaQuotCentralizer L ⊓ L = E ⊓ Sec4.thetaQuotCentralizer L :=
        inf_eq_left.mpr (inf_le_left.trans (hEL' ▸ inf_le_right))
      rw [h2, hB9, hZ] at h1
      norm_num at h1
  ·
    exfalso
    have hEC : E ⊓ Sec4.thetaQuotCentralizer L = E :=
      Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [hk, hE.2]; norm_num)
    exact false_of_E27_le_thetaQuotCentralizer h.partTwoF_eq hperf hZ hev hE.1 hE.2
      (hEC ▸ inf_le_right)

theorem item125_of_inputs (h41 : Sec4.Item4_1) (h43 : Sec4.Item4_3) (h45 : Sec4.Item4_5)
    (hcov : Sec4.Census.CoverInputs46) (hK1 : KFacts.KS12CoverExclusion)
    (hK2 : KFacts.KS12NormalizerMoves) (hK9 : KFacts.KS12OrderNine)
    (hG1 : Gap125NonCentral) (hG2 : Gap125CaseA) : Item125 :=
  item125_of_gaps (item122_of h41 h43 hcov hK1) h45 hK2 hK9 hG1 hG2

end CFSG.RankThree.PartTwo.Sec12

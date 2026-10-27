module

public import CFSG.RankThree.PartTwo.Sec4.Item426A6
public import CFSG.RankThree.PartTwo.Sec4.Item426RestOuterAlt
public import CFSG.RankThree.PartTwo.Sec4.Item426RestNumerics
import CFSG.RankThree.PartTwo.KFacts.K426McL
import CFSG.RankThree.PartTwo.KFacts.K426J3
import CFSG.RankThree.PartTwo.KFacts.K412TripleCover
import CFSG.RankThree.PartTwo.KFacts.K72SLPiElems
import CFSG.RankThree.PartTwo.Sec4.Item426A6Proof
import CFSG.RankThree.PartTwo.Sec13.Item138NMod9

public section

namespace CFSG.RankThree.PartTwo.Sec4.Item426Rest

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.KFacts
open CFSG.LocalAnalysis.ComponentInitial

theorem card_center_eq_of_mulEquiv {Y Y' : Type*} [Group Y] [Group Y'] (e : Y ≃* Y') :
    Nat.card (Subgroup.center Y) = Nat.card (Subgroup.center Y') := by
  rw [← Subgroup.map_center_eq e, Subgroup.card_map_of_injective e.injective]

theorem card_secQ_of_mulEquiv {X : Type} [Group X] {P : Subgroup X} {Y : Type*} [Group Y]
    (e : Y ≃* P ⧸ aschbacherSolvableCore 3 P) :
    Nat.card (secQ P) = Nat.card (Y ⧸ Subgroup.center Y) :=
  (Nat.card_congr (QuotientGroup.congr _ _ e (Subgroup.map_center_eq e)).toEquiv).symm

theorem card_of_isTripleCover {Y S : Type*} [Group Y] [Group S] (h : IsTripleCover Y S) :
    Nat.card Y = 3 * Nat.card S := by
  obtain ⟨h3, ⟨e⟩⟩ := h
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center Y), h3,
    Nat.card_congr e.toEquiv, mul_comm]

theorem isSLThreePi_of_mulEquiv {Y Y' : Type} [Group Y] [Group Y'] (e : Y' ≃* Y)
    (h : IsSLThreePi Y) : IsSLThreePi Y' := by
  obtain ⟨q, K, _, _, hK⟩ := h
  refine ⟨q, K, inferInstance, inferInstance, ?_⟩
  rcases hK with ⟨a, b, ⟨e₁⟩⟩ | ⟨a, b, ⟨e₁⟩⟩
  · exact Or.inl ⟨a, b, ⟨e.trans e₁⟩⟩
  · exact Or.inr ⟨a, b, ⟨e.trans e₁⟩⟩

theorem restNumerics_of_isSLThreePi {Y : Type} [Group Y] [Finite Y] (hY : IsSLThreePi Y)
    (hYq : IsQuasisimple Y) : RestNumerics (Nat.card (Y ⧸ Subgroup.center Y)) := by
  have hT : IsSLThreePi (⊤ : Subgroup Y) := isSLThreePi_of_mulEquiv Subgroup.topEquiv hY
  have hTq : IsQuasisimple (⊤ : Subgroup Y) :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv Subgroup.topEquiv.symm hYq
  obtain ⟨π, p, f, K, _, hK, hq, hq2, ⟨e⟩⟩ := exists_slPi_model hT hTq
  set e' : Y ≃* slPi π 3 (p ^ f) K := Subgroup.topEquiv.symm.trans e
  have hcard : Nat.card Y = (p ^ f) ^ 3 * ((p ^ f) ^ 2 - 1) *
      cond π ((p ^ f) ^ 3 - 1) ((p ^ f) ^ 3 + 1) := by
    rw [Nat.card_congr e'.toEquiv, Sec13.card_slPi_three hK]
  have hZ : Nat.card (Subgroup.center Y) = 3 := by
    rw [card_center_eq_of_mulEquiv e', KFacts.card_center_slPi hK hq]
  refine restNumerics_of_card hq2 hq ?_
  rw [← hcard, ← hZ]
  exact (Subgroup.card_eq_card_quotient_mul_card_subgroup _).symm

section Main


theorem rest_dichotomy (h46 : Item4_6) (h47 : Item4_7W) (hON : K426Rest.ONThreeCentralizer)
    {G : Type} [Group G] [Finite G] (hG : SectionFourHyp G) {L : Subgroup G}
    (hL : L ∈ thetaComponents 3 G) {c : G} (hc : orderOf c = 3) {K : Subgroup G}
    (hK : K ∈ thetaComponentsIn (L ⊓ Subgroup.centralizer {c}))
    (hZne : inSubgroup (CFSG.pCore 3) (K ⊓ Subgroup.centralizer (K : Set G)) ≠ ⊥)
    (hZc : inSubgroup (CFSG.pCore 3) (K ⊓ Subgroup.centralizer (K : Set G)) ≤
      Subgroup.center G)
    (hnum : ∀ P : Subgroup (L ⧸ aschbacherSolvableCore 3 L),
      Nonempty (K ⧸ aschbacherSolvableCore 3 K ≃* P ⧸ aschbacherSolvableCore 3 P) →
        RestNumerics (Nat.card (secQ P))) :
    L = K ⊔ inSubgroup (aschbacherSolvableCore 3) L ∨
      ∃ P : Subgroup (L ⧸ aschbacherSolvableCore 3 L),
        Nonempty (K ⧸ aschbacherSolvableCore 3 K ≃* P ⧸ aschbacherSolvableCore 3 P) ∧
        ∃ j : ℕ, 1 ≤ j ∧
          ((2 ^ (3 * j) % 3 = 1 ∧ OuterFieldSL (L ⧸ aschbacherSolvableCore 3 L) P j) ∨
            (2 ^ (3 * j) % 3 = 2 ∧ 2 ≤ j ∧
              OuterFieldSU (L ⧸ aschbacherSolvableCore 3 L) P j)) := by
  obtain ⟨h3G, hKL, hcN, hcfg⟩ := configRest_of hL hc hK hZne hZc
  obtain ⟨eKP⟩ := Item426.nonempty_quotTheta_map_equiv L hKL
  have hn := hnum _ ⟨eKP⟩
  by_cases hout : InducesOuterTheta c L
  · right
    obtain ⟨_, hni⟩ := id hout
    exact ⟨_, ⟨eKP⟩, hcfg.outer_of_alt47W hcN hni (h47 G hG h3G L hL c hc hout)
      ⟨_, hn.big, card_secQ_dvd⟩⟩
  · have hin : IsInnerAut (Item426.thetaAut L hcN) := by
      by_contra hni
      exact hout ⟨hcN, hni⟩
    obtain ⟨y, hy⟩ := hin
    by_cases hyZ : y ∈ Subgroup.center (L ⧸ aschbacherSolvableCore 3 L)
    · left
      apply Item426.eq_sup_of_map_eq_top L hKL
      apply hcfg.eq_top_of_eq_one
      rw [← hy]
      ext x
      rw [MulAut.conj_apply, MulAut.one_apply, (Subgroup.mem_center_iff.mp hyZ x).symm,
        mul_inv_cancel_right]
    · exact (hcfg.false_of_inner hON (h46 G hG h3G L hL) hn hy.symm hyZ).elim

theorem rest_tripleCover (h46 : Item4_6) (h47 : Item4_7W) (hON : K426Rest.ONThreeCentralizer)
    {G : Type} [Group G] [Finite G] (hG : SectionFourHyp G) {L : Subgroup G}
    (hL : L ∈ thetaComponents 3 G) {c : G} (hc : orderOf c = 3) {K : Subgroup G}
    (hK : K ∈ thetaComponentsIn (L ⊓ Subgroup.centralizer {c}))
    {S : Type*} [Group S] (hS : IsTripleCover (K ⧸ aschbacherSolvableCore 3 K) S)
    (hSc : Nat.card S = 2520 ∨ Nat.card S = 443520)
    (hZne : inSubgroup (CFSG.pCore 3) (K ⊓ Subgroup.centralizer (K : Set G)) ≠ ⊥)
    (hZc : inSubgroup (CFSG.pCore 3) (K ⊓ Subgroup.centralizer (K : Set G)) ≤
      Subgroup.center G) :
    L = K ⊔ inSubgroup (aschbacherSolvableCore 3) L := by
  have hQS : Nat.card ((K ⧸ aschbacherSolvableCore 3 K) ⧸
      Subgroup.center (K ⧸ aschbacherSolvableCore 3 K)) = Nat.card S :=
    Nat.card_congr hS.2.some.toEquiv
  have hKc : Nat.card (K ⧸ aschbacherSolvableCore 3 K) = 3 * Nat.card S :=
    card_of_isTripleCover hS
  rcases rest_dichotomy h46 h47 hON hG hL hc hK hZne hZc (fun P ⟨e⟩ => by
      rw [card_secQ_of_mulEquiv e, hQS]
      rcases hSc with h | h <;> rw [h]
      · exact restNumerics_A7
      · exact restNumerics_M22) with h | ⟨P, ⟨e⟩, j, hj, hSL | hSU⟩
  · exact h
  · exfalso
    obtain ⟨-, -, K₀, _, _, hK₀, ⟨eP⟩⟩ := hSL
    have hcard : Nat.card (K ⧸ aschbacherSolvableCore 3 K) =
        (2 ^ j) ^ 3 * ((2 ^ j) ^ 2 - 1) * ((2 ^ j) ^ 3 - 1) := by
      rw [Nat.card_congr (e.trans eP).toEquiv, CFSG.SectionRank.OddCover.card_statedSL_three,
        hK₀]
    rw [hKc] at hcard
    obtain ⟨h1, h2⟩ := card_sl_two_pow_ne hj
    rcases hSc with h | h <;> rw [h] at hcard <;> norm_num at hcard
    · exact h1 hcard.symm
    · exact h2 hcard.symm
  · exfalso
    obtain ⟨-, hj2, -, K₀, _, _, hK₀, ⟨eP⟩⟩ := hSU
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have := Fintype.ofFinite K₀
    have : CharP K₀ 2 := charP_of_card_eq_prime_pow (f := 2 * j)
      (by rw [← Nat.card_eq_fintype_card, hK₀, ← pow_mul, mul_comm])
    have hcard : Nat.card (K ⧸ aschbacherSolvableCore 3 K) =
        (2 ^ j) ^ 3 * ((2 ^ j) ^ 2 - 1) * ((2 ^ j) ^ 3 + 1) := by
      rw [Nat.card_congr (e.trans eP).toEquiv, CFSG.SectionRank.OddCover.card_statedSU_three hK₀]
    rw [hKc] at hcard
    obtain ⟨h1, h2⟩ := card_su_two_pow_ne hj2
    rcases hSc with h | h <;> rw [h] at hcard <;> norm_num at hcard
    · exact h1 hcard.symm
    · exact h2 hcard.symm

theorem rest_SL (h46 : Item4_6) (h47 : Item4_7W) (hON : K426Rest.ONThreeCentralizer)
    {G : Type} [Group G] [Finite G] (hG : SectionFourHyp G) {L : Subgroup G}
    (hL : L ∈ thetaComponents 3 G) {c : G} (hc : orderOf c = 3) {K : Subgroup G}
    (hK : K ∈ thetaComponentsIn (L ⊓ Subgroup.centralizer {c}))
    (hSLK : IsSLThreePi (K ⧸ aschbacherSolvableCore 3 K))
    (hZne : inSubgroup (CFSG.pCore 3) (K ⊓ Subgroup.centralizer (K : Set G)) ≠ ⊥)
    (hZc : inSubgroup (CFSG.pCore 3) (K ⊓ Subgroup.centralizer (K : Set G)) ≤
      Subgroup.center G) :
    L = K ⊔ inSubgroup (aschbacherSolvableCore 3) L ∨
      ∃ n : ℕ, 1 ≤ n ∧ IsSLThreePiAt (L ⧸ aschbacherSolvableCore 3 L) (2 ^ (3 * n)) ∧
        IsSLThreePiAt (K ⧸ aschbacherSolvableCore 3 K) (2 ^ n) := by
  have hKq := Item426.isQuasisimple_of_mem_thetaComponentsIn hK
  rcases rest_dichotomy h46 h47 hON hG hL hc hK hZne hZc (fun P ⟨e⟩ => by
      rw [card_secQ_of_mulEquiv e]
      exact restNumerics_of_isSLThreePi hSLK hKq) with h | ⟨P, ⟨e⟩, j, hj, hSL | hSU⟩
  · exact Or.inl h
  · right
    obtain ⟨hmod, ⟨K₁, _, _, hK₁, ⟨eL⟩⟩, K₀, _, _, hK₀, ⟨eP⟩⟩ := hSL
    have hmod₀ : 2 ^ j % 3 = 1 := by
      have h := modThree_of_cube (π := true) (q₀ := 2 ^ j)
        (by change (2 ^ j) ^ 3 % 3 = 1; rw [← pow_mul, mul_comm]; exact hmod)
      exact h
    exact ⟨j, hj, ⟨K₁, inferInstance, inferInstance, Or.inl ⟨hK₁, hmod, ⟨eL⟩⟩⟩,
      ⟨K₀, inferInstance, inferInstance, Or.inl ⟨hK₀, hmod₀, ⟨e.trans eP⟩⟩⟩⟩
  · right
    obtain ⟨hmod, -, ⟨K₁, _, _, hK₁, ⟨eL⟩⟩, K₀, _, _, hK₀, ⟨eP⟩⟩ := hSU
    have hmod₀ : 2 ^ j % 3 = 2 := by
      have h := modThree_of_cube (π := false) (q₀ := 2 ^ j)
        (by change (2 ^ j) ^ 3 % 3 = 2; rw [← pow_mul, mul_comm]; exact hmod)
      exact h
    exact ⟨j, hj, ⟨K₁, inferInstance, inferInstance, Or.inr ⟨hK₁, hmod, ⟨eL⟩⟩⟩,
      ⟨K₀, inferInstance, inferInstance, Or.inr ⟨hK₀, hmod₀, ⟨e.trans eP⟩⟩⟩⟩

theorem item4_26Theta_of_A6 (hA6 : Item4_26ThetaA6) (h46 : Item4_6) (h47 : Item4_7W)
    (hON : K426Rest.ONThreeCentralizer) : Item4_26Theta := by
  intro G _ _ hG L hL c hc K hK htype hZne hZc
  rcases htype with h6 | h7 | h22 | hSL
  · exact hA6 G hG L hL c hc K hK h6 hZne hZc
  · exact Or.inl (rest_tripleCover h46 h47 hON hG hL hc hK h7
      (Or.inl KFacts.K412.card_alternating_six_seven.2) hZne hZc)
  · exact Or.inl (rest_tripleCover h46 h47 hON hG hL hc hK h22
      (Or.inr Item426.card_M22) hZne hZc)
  · rcases rest_SL h46 h47 hON hG hL hc hK hSL hZne hZc with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)

theorem item4_26Theta_of (h46 : Item4_6) (h47 : Item4_7W) (hON : K426Rest.ONThreeCentralizer) :
    Item4_26Theta :=
  item4_26Theta_of_A6 (Item426.rank3II_4_26_A6_of h46 h47 K426.mclThreeCentralizer
      K426.j3CoverCentralizer) h46 h47 hON

end Main

end CFSG.RankThree.PartTwo.Sec4.Item426Rest

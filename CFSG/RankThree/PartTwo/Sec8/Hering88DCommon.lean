module

public import CFSG.RankThree.PartTwo.Sec8.Hering88DInv
public import CFSG.RankThree.PartTwo.Sec8.Hering88CEng
public import CFSG.RankThree.PartTwo.Sec8.Item83ProofSU3

public section

namespace CFSG.RankThree.PartTwo.Sec8

namespace Hering88D

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.GroupTheory


theorem exists_inner_d_two_local
    (h45 : Sec4.Item4_5) (h84 : Pair84A) (hC : KF88SwapCent) (hF : KF84Field)
    (hAut : Sec4.K419AutThree) (hT : Hering88C.KF89JCentType419)
    {G : Type} [Group G] [Finite G] {A : Subgroup G} {c : G} {L : Subgroup G} {a b : G}
    {X : Subgroup G} {n : ℕ} (h : Sec8Pair G A c L a b X n) {Y : Subgroup G}
    (hY : Y ∈ thetaComponentsAt 3 a) (hIJ : sec8I L a ⊔ sec8J X a ≤ Y) {x : G}
    (hx : x = c ∨ x = b)
    (hxY : KFacts.InducesStdKind Y x .field ∨ KFacts.InducesStdKind Y x .graphField)
    (hOTC : KFacts.OutThreeCyclic (Y ⧸ aschbacherSolvableCore 3 Y)) :
    ∃ d ∈ Subgroup.closure ({c, b} : Set G), d ∉ Subgroup.zpowers x ∧ d ∈ A ∧ d ^ 3 = 1 ∧
      ∃ hdN : d ∈ Subgroup.normalizer (Y : Set G),
        KFacts.IsInnerAut (Sec4.thetaQuotMulAut Y (Sec4.compAction Y ⟨d, hdN⟩)) ∧
        Sec4.thetaQuotMulAut Y (Sec4.compAction Y ⟨d, hdN⟩) ≠ 1 ∧
        ∃ E : Subgroup G, E ≤ A ∧ d ∈ E ∧ InvTwoBarNontrivial E Y := by
  classical
  obtain ⟨d, hdcl, hdx, hdA, hd3, hdN, hin, hne⟩ :=
    Hering88C.exists_inner_d h45 hC hF h hY hIJ hx hxY hOTC
  obtain ⟨S, hSY, hS1, hS2, hES⟩ := exists_invariant_two_ext h45 h84 hAut hT h hIJ h.mem_A
  set E : Subgroup G := Subgroup.zpowers b ⊔ Subgroup.zpowers a ⊔ Subgroup.zpowers c with hE
  obtain ⟨hbA, -, -, -⟩ := Item87Proof.isGammaIndex_cases h.isGammaIndex
  have hEA : E ≤ A :=
    sup_le (sup_le (Subgroup.zpowers_le.mpr hbA) (Subgroup.zpowers_le.mpr h.a_mem))
      (Subgroup.zpowers_le.mpr h.mem_A)
  have hdE : d ∈ E := by
    have hcl : Subgroup.closure ({c, b} : Set G) ≤ E := by
      refine (Subgroup.closure_le E).mpr ?_
      rintro _ (rfl | rfl)
      · exact Subgroup.mem_sup_right (Subgroup.mem_zpowers _)
      · exact Subgroup.mem_sup_left (Subgroup.mem_sup_left (Subgroup.mem_zpowers _))
    exact hcl hdcl
  have hAel := h.mem_partTwoF.1
  have hAN : A ≤ Subgroup.normalizer (Y : Set G) := Hering88C.le_normalizer_of_pair h45 h hY
  have hθ : Odd (Nat.card (aschbacherSolvableCore 3 Y)) := by
    have h1 := odd_card_of_le_normalizer h.toTheoremFourHyp.localRank_three.le hAel h.card_eq
      (X := inSubgroup (aschbacherSolvableCore 3) Y) ?_ (hAN.trans
        (SteinbergBY.normalizer_le_normalizer_inSubgroup_aschbacherSolvableCore 3 Y))
    · rwa [inSubgroup, Subgroup.card_map_of_injective Y.subtype_injective] at h1
    · rw [inSubgroup, Subgroup.card_map_of_injective Y.subtype_injective]
      exact KFacts.not_three_dvd_card_aschbacherSolvableCore Y
  have hInv : InvTwoBarNontrivial E Y :=
    Item83Proof.invTwoBarNontrivial_of_invariant hθ
      ⟨hSY, (isPiSubgroup_piOf_iff Nat.prime_two S).mpr hS2, hES⟩ hS1
  exact ⟨d, hdcl, hdx, hdA, hd3, hdN, hin, hne, E, hEA, hdE, hInv⟩

end Hering88D

end CFSG.RankThree.PartTwo.Sec8

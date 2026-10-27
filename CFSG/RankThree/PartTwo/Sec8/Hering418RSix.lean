module

public import CFSG.RankThree.PartTwo.Sec8.Hering418Odd

public section

namespace CFSG.RankThree.PartTwo.Sec8.Hering418

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.AGLEmbeddingD2.Wilson.Coordinator.KF418
open CFSG.Open (IsElemAbelian)

section Outer


@[expose] def KF418OuterOn (P : ∀ (X : Type) [Group X], Prop) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), L ∈ thetaComponents 3 G →
    P (L ⧸ aschbacherSolvableCore 3 L) →
    ∀ a b : G, a ^ 3 = 1 → b ^ 3 = 1 → a * b = b * a → b ≠ 1 → a ∉ Subgroup.zpowers b →
      a ∈ Subgroup.normalizer (L : Set G) → b ∈ Subgroup.normalizer (L : Set G) →
      b ∉ Sec4.thetaQuotCentralizer L → (∀ j : ℤ, a * b ^ j ∉ Sec4.thetaQuotCentralizer L) →
    ∀ K ∈ thetaComponentsIn (L ⊓ Subgroup.centralizer {b}),
    ∀ n : ℕ, 1 ≤ n → IsType418 (K ⧸ aschbacherSolvableCore 3 K) n →
      KFacts.InducesStdKind K a .field →
      (KFacts.InducesStdKind L b .field ∨ KFacts.InducesStdKind L b .graphField) → False

theorem kF418ModelOn_of_outer {P : ∀ (X : Type) [Group X], Prop}
    (hbound : ∀ (X : Type) [Group X] [Finite X], P X →
      ∀ F : Subgroup (MulAut X), IsElemAbelian 3 F → F ≤ (MulAut.conj : X →* MulAut X).range →
        Nat.card F ≤ 9)
    (hout : ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), L ∈ thetaComponents 3 G →
      P (L ⧸ aschbacherSolvableCore 3 L) → ∀ x : G, x ^ 3 = 1 → Sec4.InducesOuterTheta x L →
        KFacts.InducesStdKind L x .field ∨ KFacts.InducesStdKind L x .graphField)
    (hB : KF418OuterOn P) : KF418ModelOn P := by
  intro G _ _ L hL hl a b ha3 hb3 hab hb1 habz haN hbN hbC haC K hK n hn htype hKa
  by_cases hβ : Sec4.InducesOuterTheta b L
  · exact (hB G L hL hl a b ha3 hb3 hab hb1 habz haN hbN hbC haC K hK n hn htype hKa
      (hout G L hL hl b hb3 hβ)).elim
  · have hbin : ¬ (KFacts.InducesStdKind L b .field ∨ KFacts.InducesStdKind L b .graphField) := by
      rintro (h | h)
      · exact KFacts.not_inducesStdKind_of_not_inducesOuterTheta L hβ (by decide) h
      · exact KFacts.not_inducesStdKind_of_not_inducesOuterTheta L hβ (by decide) h
    refine ⟨?_, hbin⟩
    by_cases hα : Sec4.InducesOuterTheta a L
    · exact hout G L hL hl a ha3 hα
    · exfalso
      have c := Cfg.of_model hK ha3 hb3 hab haN hbN hbC haC hKa
      have hKq := Sec6.isQuasisimple_of_mem_thetaComponentsIn hK
      have hαI : c.alpha ∈ innBar L := by
        by_contra h
        exact hα ⟨haN, h⟩
      have hβI : c.beta ∈ innBar L := by
        by_contra h
        exact hβ ⟨hbN, h⟩
      exact c.false_of_bound hn hKq htype hKa le_rfl hαI hβI
        (fun F hF hFN => hbound _ hl F hF hFN)

end Outer

section G2


@[expose] def IsGTwoSix (X : Type) [Group X] : Prop :=
  ∃ f : ℕ, 3 ∣ f ∧ Blueprint.ChevalleyExceptionalModel X .G2 2 f

theorem kF418ModelOn_G2Six_of_outer (hB : KF418OuterOn (fun X _ => IsGTwoSix X)) :
    KF418ModelOn (fun X _ => IsGTwoSix X) := by
  refine kF418ModelOn_of_outer ?_ ?_ hB
  · rintro X _ _ ⟨f, h3f, hX⟩ F hF hFi
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp (Sec4.isPGroup_of_isElemAbelian hF)
    have hk2 : k ≤ 2 := (Sec4.le_pRank_of_le_inner (MulEquiv.refl _) hF hFi hk).trans
      (Sec21.g2EvenThreeRankTwo X f hX)
    rw [hk]
    calc 3 ^ k ≤ 3 ^ 2 := Nat.pow_le_pow_right (by norm_num) hk2
      _ = 9 := by norm_num
  · intro G _ _ L hL hl x hx3 hout
    obtain ⟨f, h3f, hX⟩ := hl
    obtain ⟨K, _, _, hK, ⟨e⟩⟩ := Sec4.exists_mulEquiv_adjointGroup_G2 hX
    have hf1 : 1 ≤ f := hX.1.2.1
    have hf3 : 3 ≤ f := Nat.le_of_dvd (by omega) h3f
    have hK4 : 4 ≤ Nat.card K := by
      rw [hK]
      calc 4 ≤ 2 ^ 3 := by norm_num
        _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf3
    have : Fintype K := Fintype.ofFinite K
    have hcharP : CharP K 2 := charP_of_card_eq_prime_pow (f := f)
      (by rw [← Nat.card_eq_fintype_card, hK])
    have hK3 : ringChar K ≠ 3 := by
      rw [ringChar.eq K 2]
      norm_num
    exact Or.inl (KFacts.InducesStdKind.g2 K hK3 hK4
      (KFacts.inducesKindG2_field L hK3 hK4 hx3 hout e))

end G2

section SpFour


@[expose] def IsSpFourSix (X : Type) [Group X] : Prop :=
  ∃ k : ℕ, 1 ≤ k ∧ 3 ∣ k ∧ Nonempty (X ≃* CFSG.Assembly.RankThreeEven.projSp 2 (GaloisField 2 k))

theorem kF418ModelOn_SpFourSix_of_outer (hB : KF418OuterOn (fun X _ => IsSpFourSix X)) :
    KF418ModelOn (fun X _ => IsSpFourSix X) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine kF418ModelOn_of_outer ?_ ?_ hB
  · rintro X _ _ ⟨k, hk, h3k, ⟨φ⟩⟩
    have hk3 : 3 ≤ k := Nat.le_of_dvd (by omega) h3k
    have hF : Nat.card (GaloisField 2 k) = 2 ^ k := GaloisField.card 2 k (by omega)
    have hq : 4 ≤ 2 ^ k := by
      calc 4 ≤ 2 ^ 3 := by norm_num
        _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk3
    have hs : IsSimpleGroup (CFSG.Assembly.RankThreeEven.projSp 2 (GaloisField 2 k)) := by
      have := CFSG.ClassicalGroups.Symplectic.isSimpleGroup_statedProj_statedSp
        (GaloisField 2 k) 2 (by norm_num) (Or.inl (Or.inr (by rw [hF]; exact hq)))
      exact (CFSG.RankThree.PartTwo.Census.statedProjEquivProjImage
        (CFSG.Assembly.LowTwoRank.StatedSp 2 (GaloisField 2 k))).symm.isSimpleGroup
    exact bound_inner_of_pRank (Sec4.quotientCenterCongr φ)
      (Sec4.Res417Three.pRank_projSp_two_le (by norm_num) hk hs)
  · intro G _ _ L hL hl x hx3 hout
    obtain ⟨k, hk, h3k, ⟨φ⟩⟩ := hl
    let e : L ⧸ aschbacherSolvableCore 3 L ≃*
        CFSG.Open.StatedProj (CFSG.Open.StatedSp 2 (GaloisField 2 k)) :=
      φ.trans (CFSG.PGLModel.projSpEquivStatedProj 2 (GaloisField 2 k))
    rcases KFacts.inducesKindPSp4Even_diagonal_or_field L hx3 hout e with ⟨hx, hD, hnot⟩ | h
    · exfalso
      obtain ⟨A, hA⟩ := hD
      exact hnot (hA ▸ KFacts.conjAut_mem_inner_of_charTwo A)
    · exact Or.inl (KFacts.InducesStdKind.psp4even (GaloisField 2 k) ⟨e, h⟩)

end SpFour

end CFSG.RankThree.PartTwo.Sec8.Hering418

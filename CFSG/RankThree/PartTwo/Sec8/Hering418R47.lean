module

public import CFSG.RankThree.PartTwo.Sec8.Hering418RFinal
public import CFSG.RankThree.PartTwo.Sec8.Hering418ROne
public import CFSG.RankThree.PartTwo.Sec8.Hering418RSev
public import CFSG.RankThree.PartTwo.Sec8.Hering418RSixSp

public section

namespace CFSG.RankThree.PartTwo.Sec8.Hering418

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo

@[expose] def KF418ModelOn47 (P : ∀ (X : Type) [Group X], Prop) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), L ∈ thetaComponents 3 G →
    P (L ⧸ aschbacherSolvableCore 3 L) →
    (∀ x : G, orderOf x = 3 → Sec4.InducesOuterTheta x L → Sec4.Alt47 L x) →
    ∀ a b : G, a ^ 3 = 1 → b ^ 3 = 1 → a * b = b * a → b ≠ 1 → a ∉ Subgroup.zpowers b →
      a ∈ Subgroup.normalizer (L : Set G) → b ∈ Subgroup.normalizer (L : Set G) →
      b ∉ Sec4.thetaQuotCentralizer L → (∀ j : ℤ, a * b ^ j ∉ Sec4.thetaQuotCentralizer L) →
    ∀ K ∈ thetaComponentsIn (L ⊓ Subgroup.centralizer {b}),
    ∀ n : ℕ, 1 ≤ n → IsType418 (K ⧸ aschbacherSolvableCore 3 K) n →
      KFacts.InducesStdKind K a .field →
      (KFacts.InducesStdKind L a .field ∨ KFacts.InducesStdKind L a .graphField) ∧
        ¬ (KFacts.InducesStdKind L b .field ∨ KFacts.InducesStdKind L b .graphField)

theorem kF418ModelOn47_of_split {P Q : ∀ (X : Type) [Group X], Prop}
    (h1 : KF418ModelOn (fun X _ => P X ∧ ¬ Q X)) (h2 : KF418ModelOn47 Q) : KF418ModelOn47 P := by
  intro G _ _ L hL hP h47
  by_cases hQ : Q (L ⧸ aschbacherSolvableCore 3 L)
  · exact h2 G L hL hQ h47
  · exact h1 G L hL ⟨hP, hQ⟩

theorem kF418Faithful_of_on47 (h46 : Sec4.Item4_6) (h47 : Sec4.Item4_7)
    (hM : KF418ModelOn47 (fun X _ => Sec4.IsList46 X)) : KF418Faithful := by
  intro G _ _ hS4 hZ a b ha3 hb3 hab hb1 habz L hL haN hbN hbC haC K hK n hn htype hKa
  exact hM G L hL (h46 G hS4 hZ L hL) (fun x hx hout => h47 G hS4 hZ L hL x hx hout) a b ha3 hb3
    hab hb1 habz haN hbN hbC haC K hK n hn htype hKa

theorem kF418ModelOn_sixResNotU4_of_families
    (hL3 : KF418ModelOn (fun X _ => IsLThreeSix X))
    (hU3 : KF418ModelOn (fun X _ => IsUThreeSix X))
    (hSp : KF418ModelOn (fun X _ => IsSpFourSix X))
    (hSL : KF418ModelOn (fun X _ => IsSLThreeSix X))
    (hSU : KF418ModelOn (fun X _ => IsSUThreeSix X))
    (hG2 : KF418ModelOn (fun X _ => IsGTwoSix X))
    (hF4 : KF418ModelOn (fun X _ => IsTwistedFFourSix X))
    (hD4 : KF418ModelOn (fun X _ => IsTrialityD4Six X)) :
    KF418ModelOn (fun X _ => IsList46SixRes X ∧ ¬ IsUFourSix X) := by
  intro G _ _ L hL hl
  rcases isList46SixRes_iff.mp hl.1 with h | h | h | h | h | h | h | h | h
  · exact hL3 G L hL h
  · exact hU3 G L hL h
  · exact hSp G L hL h
  · exact absurd h hl.2
  · exact hSL G L hL h
  · exact hSU G L hL h
  · exact hG2 G L hL h
  · exact hF4 G L hL h
  · exact hD4 G L hL h

section NotU4

theorem kF418ModelOn_sixNotU4_of_res
    (hres : KF418ModelOn (fun X _ => IsList46SixRes X ∧ ¬ IsUFourSix X)) :
    KF418ModelOn (fun X _ => Sec4.IsList46Six X ∧ ¬ IsUFourSix X) := by
  intro G _ _ L hL ⟨hl, hnot⟩
  rcases hl with (⟨n, hn, hL2 | hL3 | hU3 | hSp | hU4⟩ |
      ⟨f, hG2 | hD4 | hSz | hF4 | hTits⟩) | ⟨n, hn, K, hKf, hKfin, ⟨hK, hφ⟩ | ⟨hK, hφ⟩⟩
  · by_cases hn1 : n = 1
    · subst hn1
      exact kF418ModelOn_L2TwoOne G L hL hL2
    · exact kF418ModelOn_L2Two G L hL ⟨n, by omega, hL2⟩
  · by_cases h3 : 3 ∣ n
    · exact hres G L hL ⟨Or.inl ⟨n, hn, h3, Or.inl hL3⟩, hnot⟩
    · exact kF418ModelOn_L3Two G L hL (Or.inl ⟨n, hn, h3, hL3⟩)
  · by_cases h3 : 3 ∣ n
    · exact hres G L hL ⟨Or.inl ⟨n, hn, h3, Or.inr (Or.inl hU3)⟩, hnot⟩
    · exact kF418ModelOn_uThree G L hL ⟨n, hn, h3, hU3⟩
  · by_cases h3 : 3 ∣ n
    · exact hres G L hL ⟨Or.inl ⟨n, hn, h3, Or.inr (Or.inr (Or.inl hSp))⟩, hnot⟩
    · exact kF418ModelOn_spFour G L hL ⟨n, hn, h3, hSp⟩
  · by_cases h3 : 3 ∣ n
    · exact absurd ⟨n, hn, h3, hU4⟩ hnot
    · exact kF418ModelOn_uFour G L hL ⟨n, hn, h3, hU4⟩
  · by_cases h3 : 3 ∣ f
    · exact hres G L hL ⟨Or.inr (Or.inr (Or.inl ⟨f, h3, Or.inl hG2⟩)), hnot⟩
    · exact kF418ModelOn_G2Two G L hL ⟨f, h3, hG2⟩
  · exact hres G L hL ⟨Or.inr (Or.inr (Or.inr ⟨f, hD4⟩)), hnot⟩
  · exact kF418ModelOn_suzuki G L hL ⟨f, hSz⟩
  · by_cases h3 : 3 ∣ f
    · exact hres G L hL ⟨Or.inr (Or.inr (Or.inl ⟨f, h3, Or.inr hF4⟩)), hnot⟩
    · exact kF418ModelOn_twistedF4 G L hL ⟨f, h3, hF4⟩
  · exact kF418ModelOn_tits G L hL ⟨f, hTits⟩
  · by_cases h3 : 3 ∣ n
    · exact hres G L hL ⟨Or.inr (Or.inl ⟨n, hn, h3, K, hKf, hKfin, Or.inl ⟨hK, hφ⟩⟩), hnot⟩
    · exact kF418ModelOn_L3Two G L hL (Or.inr ⟨n, hn, h3, K, hKf, hKfin, hK, hφ⟩)
  · by_cases h3 : 3 ∣ n
    · exact hres G L hL ⟨Or.inr (Or.inl ⟨n, hn, h3, K, hKf, hKfin, Or.inr ⟨hK, hφ⟩⟩), hnot⟩
    · exact kF418ModelOn_suThree G L hL ⟨n, hn, h3, K, hKf, hKfin, hK, hφ⟩

theorem kF418ModelOn_list46NotU4
    (hAS : CFSG.AGLEmbeddingD2.Wilson.Coordinator.KF418.KF418ModelAltSpor)
    (hR1 : KF418ModelOn (fun X _ => IsList46OneRes X))
    (hR6 : KF418ModelOn (fun X _ => IsList46SixRes X ∧ ¬ IsUFourSix X))
    (hR78 : KF418ModelOn (fun X _ => IsSevenEightRes X)) :
    KF418ModelOn (fun X _ => Sec4.IsList46 X ∧ ¬ IsUFourSix X) := by
  intro G _ _ L hL ⟨hl, hnot⟩
  rcases (Sec4.isList46_iff _).mp hl with h | h | h | h | h | h | h | h
  · exact kF418ModelOn_one_of_res hR1 G L hL h
  · exact kF418ModelOn_two G L hL h
  · exact kF418ModelOn_three G L hL h
  · exact hAS G L hL (Or.inl h)
  · exact hAS G L hL (Or.inr h)
  · exact kF418ModelOn_sixNotU4_of_res hR6 G L hL ⟨h, hnot⟩
  · exact kF418ModelOn_sevenEight_of_res hR78 G L hL (Or.inl h)
  · exact kF418ModelOn_sevenEight_of_res hR78 G L hL (Or.inr h)

section Full

theorem kF418Faithful_of_families47 (h46 : Sec4.Item4_6) (h47 : Sec4.Item4_7)
    (hAS : CFSG.AGLEmbeddingD2.Wilson.Coordinator.KF418.KF418ModelAltSpor)
    (hL3 : KF418ModelOn (fun X _ => IsLThreeSix X))
    (hU3 : KF418ModelOn (fun X _ => IsUThreeSix X))
    (hSL : KF418ModelOn (fun X _ => IsSLThreeSix X))
    (hSU : KF418ModelOn (fun X _ => IsSUThreeSix X))
    (hD4 : KF418ModelOn (fun X _ => IsTrialityD4Six X))
    (hrank : Sec21.TwistedF4EvenThreeRankTwo)
    (hU4 : KF418ModelOn47 (fun X _ => IsUFourSix X)) : KF418Faithful :=
  kF418Faithful_of_on47 h46 h47 (kF418ModelOn47_of_split
    (kF418ModelOn_list46NotU4 hAS kF418ModelOn_oneRes
      (kF418ModelOn_sixResNotU4_of_families hL3 hU3 kF418ModelOn_SpFourSix hSL hSU
        kF418ModelOn_G2Six (kF418ModelOn_TwistedF4Six_of_rank hrank) hD4)
      kF418ModelOn_sevenEightRes) hU4)

end Full

end NotU4

end CFSG.RankThree.PartTwo.Sec8.Hering418

module

public import CFSG.RankThree.PartTwo.Sec21.Item222ProofStatements
public import CFSG.RankThree.PartTwo.Sec21.Item222ProofParts
public import CFSG.RankThree.PartTwo.KFacts.KS21KOf
public import CFSG.RankThree.PartTwo.Sec21.Item222ProofBarLift
import CFSG.RankThree.PartTwo.Sec6.Item612Local
import CFSG.Sporadic.J2
public import CFSG.RankThree.PartTwo.Sec21.Item222ProofKZero

public section

namespace CFSG.RankThree.PartTwo.Sec21

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Assembly.RankThreeEven (projSL projSU projSp)
open CFSG.Assembly.LowTwoRank (StatedClassicalModel)
open CFSG.Blueprint

namespace Item222Proof

variable {G : Type} [Group G]

theorem star_SL3_three_bar [Finite G] (h211 : Item211)
    (h2131 : Item2131One) {A E U L : Subgroup G} {c : G} (hpair : Sec21Pair G A E U c L)
    (h27 : Nat.card A = 3 ^ 3) {n : ℕ} (hn : 0 < n) (he : Even n) (eB : lBar L ≃* SL3 n) :
    Nonempty (starOf A L ≃* Equiv.Perm (Fin 3)) ∧ IsTypeCOnBarSL A L ∧
      starOf A L = Subgroup.closure ((starOf A L : Set (MulAut A)) ∩ dStar A) ∧
      ((starOf A L : Set (MulAut A)) ∩ dStar A).Nonempty ∧
      ∀ φ ∈ starOf A L, IsReflectionOn φ → ∃ b ∈ A, (∃ x ∈ L, x * b ≠ b * x) ∧
        Even (Nat.card (L ⊓ Subgroup.centralizer ({b} : Set G) : Subgroup G)) ∧
        L ⊓ Subgroup.centralizer (fixedInG A φ : Set G) =
          L ⊓ Subgroup.centralizer ({b} : Set G) := by
  have hpairs := mem_lThreeStarPairs_iff.mp hpair.mem_pair
  have hcA : c ∈ A := hpair.mem_E.2 hpairs.1.1
  have hc1 : c ≠ 1 := hpairs.2.1
  have hAe : CFSG.Assembly.IsElemAbelian 3 A := hpair.mem_S.1.1
  have hLc : L ∈ thetaComponentsAt 3 c := (lZeroStarAt_subset A c) hpairs.2.2.1
  have hLC : L ≤ Subgroup.centralizer ({c} : Set G) :=
    Sec6.le_centralizer_of_mem_thetaComponentsAt hLc
  have hL3 : L ∈ lThreeStar A := ⟨mem_lZeroStar_of_mem_lThreeStarPairs hpair.mem_pair, E,
    hpair.mem_E, U, hpair.mem_U, c, hpair.mem_pair⟩
  obtain ⟨σ₁, h₁, σ₂, h₂, h11, h22, hr₁, hr₂, hcl, hcase⟩ :=
    star_three_cases h211 h2131 hpair hcA h27
  rcases hcase with ⟨hS3, hfix, -, hinfo⟩ | ⟨-, -, -, hinfo⟩
  ·
    have hC : IsTypeCOnBarSL A L := by
      rcases hinfo with heJ | ⟨m, -, -, ⟨⟨eP⟩, -⟩ | ⟨-, hC⟩⟩
      · obtain ⟨eJ⟩ := heJ
        have := CFSG.Sporadic.J2.isSimpleGroup_J2
        exact (false_of_isSimpleGroup_of_mulEquiv_SL3 hn he (eJ.symm.trans eB)).elim
      · have := isSimpleGroup_projSL_three (GaloisField 2 m)
        exact (false_of_isSimpleGroup_of_mulEquiv_SL3 hn he (eP.symm.trans eB)).elim
      · exact hC
    refine ⟨hS3, hC, eq_closure_inter h₁ h₂ ⟨hr₁, L, hL3, h₁⟩ ⟨hr₂, L, hL3, h₂⟩ hcl,
      ⟨σ₁, h₁, hr₁, L, hL3, h₁⟩, fun φ hφL hφ => ?_⟩
    exact exists_mem_eq_inf_centralizer_singleton hAe h27 hcA hc1 hLC
      ((starOf A L).mul_mem h₁ h₂) hfix hφL hφ
  ·
    exfalso
    rcases hinfo with ((⟨m, hm, hme, heS | heS⟩) | heS) | hX | hX
    · obtain ⟨eS⟩ := heS
      have hm2 : 2 ≤ m := by obtain ⟨k, hk⟩ := hme; omega
      have := isSimpleGroup_projSp_two hm2
      exact false_of_isSimpleGroup_of_mulEquiv_SL3 hn he (eS.symm.trans eB)
    · obtain ⟨eS⟩ := heS
      have := isSimpleGroup_projSU (m := 4) (n := m) le_rfl hm
      exact false_of_isSimpleGroup_of_mulEquiv_SL3 hn he (eS.symm.trans eB)
    · obtain ⟨eS⟩ := heS
      have := isSimpleGroup_projSU (m := 5) (n := 2) (by norm_num) (by norm_num)
      exact false_of_isSimpleGroup_of_mulEquiv_SL3 hn he (eS.symm.trans eB)
    · exact false_of_statedClassicalModel_PSL_of_mulEquiv_SL3 hX hn he eB
    · exact false_of_statedClassicalModel_PSL_of_mulEquiv_SL3 hX hn he eB

end Item222Proof

open Item222Proof

variable {G : Type} [Group G]

theorem item222_of_bar
    (h211 : Item211) (h221 : Item221) (h2131 : Item2131One)
    (h45 : Sec4.Item4_5) (hSp4 : KS222Sp4) (hU4 : KS222U4Even) (hU5 : KS222U5)
    (hSL3 : KS222SL3) (hU4o : KS222U4Odd) : Item222 := by
  intro G _ _ A E U c L hpair
  have hpairs := mem_lThreeStarPairs_iff.mp hpair.mem_pair
  have hcA : c ∈ A := hpair.mem_E.2 hpairs.1.1
  have hc1 : c ≠ 1 := hpairs.2.1
  have hAF : A ∈ partTwoF G := hpair.mem_S.1
  have hAe : CFSG.Assembly.IsElemAbelian 3 A := hAF.1
  have hLc : L ∈ thetaComponentsAt 3 c := (lZeroStarAt_subset A c) hpairs.2.2.1
  have hLC : L ≤ Subgroup.centralizer ({c} : Set G) :=
    Sec6.le_centralizer_of_mem_thetaComponentsAt hLc
  have hLp : Group.IsPerfect L := Sec6.isPerfect_of_mem_thetaComponentsAt hLc
  have hL3 : L ∈ lThreeStar A := ⟨mem_lZeroStar_of_mem_lThreeStarPairs hpair.mem_pair, E,
    hpair.mem_E, U, hpair.mem_U, c, hpair.mem_pair⟩
  have hKW : KOfWellDefined A := KFacts.KS21.kOfWellDefined_of_sec21Std hpair.toSec21Std
  have hK : ∀ φ ∈ starOf A L, φ ∈ dStar A → ∀ {m : ℕ}, 2 ≤ m →
      Nonempty (inSubgroup perfectResidual (L ⊓ Subgroup.centralizer (fixedInG A φ : Set G)) ≃*
        projSL 2 (GaloisField 2 m)) → Nonempty (kOf A φ ≃* projSL 2 (GaloisField 2 m)) :=
    fun φ hφL hφD _ hm he => he.elim fun e =>
      nonempty_kOf_mulEquiv_projSL hAF hcA hLc hφL hφD.1.1 hm e
  rcases h221 G A E U c L hpair with ⟨h81, n, hn1, hno, ⟨eL⟩⟩ | ⟨h27, hcase⟩
  ·
    have := isSimpleGroup_projSU (m := 4) (n := n) le_rfl (by omega)
    have : IsSimpleGroup L := eL.isSimpleGroup
    have hcL := not_mem_of_isSimpleGroup (exists_not_commute_of_isPerfect hLp) hc1 hLC
    obtain ⟨eS⟩ := star_four h211 hpair h81 hn1 eL
    have h27 := card_inf_eq_of_star_four hAe h81 hcA hcL hLc eS
    obtain ⟨hgen, hKL⟩ := hU4o G L A c n hn1 hno ⟨eL⟩ hAe h81 hcA hcL hLC h27
    have hcl : starOf A L = Subgroup.closure ((starOf A L : Set (MulAut A)) ∩ dStar A) := by
      apply le_antisymm
      · calc starOf A L = Subgroup.closure ((starOf A L : Set (MulAut A)) ∩
              {φ | IsReflectionOn φ}) := hgen
          _ ≤ Subgroup.closure ((starOf A L : Set (MulAut A)) ∩ dStar A) :=
            Subgroup.closure_mono fun φ hφ => ⟨hφ.1, hφ.2, L, hL3, hφ.1⟩
      · rw [Subgroup.closure_le]
        exact Set.inter_subset_left
    refine ⟨hcl, ?_, fun φ hφL hφD => ?_⟩
    · by_contra hemp
      rw [Set.not_nonempty_iff_eq_empty] at hemp
      rw [hemp, Subgroup.closure_empty] at hcl
      have h1 : Nat.card (starOf A L) = 1 := by rw [hcl, Subgroup.card_bot]
      rw [Nat.card_congr eS.toEquiv, Nat.card_perm, Nat.card_fin] at h1
      norm_num at h1
    · exact Or.inr (Or.inr (Or.inr (Or.inr
        ⟨h81, n, hn1, hno, ⟨eL⟩, hK φ hφL hφD (by omega) (hKL φ hφL hφD.1), ⟨eS⟩⟩)))
  ·
    have hsimple : ∀ [IsSimpleGroup L], (∀ φ ∈ starOf A L, φ ∈ dStar A →
        ∀ ℓ : Subgroup G, ℓ ≤ L → Nat.card ℓ = 3 →
          L ⊓ Subgroup.centralizer (fixedInG A φ : Set G) =
            L ⊓ Subgroup.centralizer (ℓ : Set G) →
          Nonempty (starOf A L ≃* DihedralGroup 4) → Case222 A L (kOf A φ)) →
        starOf A L = Subgroup.closure ((starOf A L : Set (MulAut A)) ∩ dStar A) ∧
          ((starOf A L : Set (MulAut A)) ∩ dStar A).Nonempty ∧
          ∀ φ ∈ starOf A L, φ ∈ dStar A → Case222 A L (kOf A φ) := by
      intro _ hcase'
      obtain ⟨hD8, hcl, hne, hstr⟩ := star_simple_three h211 h2131 hpair h27
      refine ⟨hcl, hne, fun φ hφL hφD => ?_⟩
      obtain ⟨ℓ, hℓL, hℓ3, heq⟩ := hstr φ hφL hφD.1
      exact hcase' φ hφL hφD ℓ hℓL hℓ3 heq hD8
    rcases hcase with ⟨n, hn, he, heL | heL | heL⟩ | heL | ⟨hSL, hCL⟩
    ·
      obtain ⟨eL⟩ := heL
      have hn2 : 2 ≤ n := by obtain ⟨k, hk⟩ := he; omega
      have := isSimpleGroup_projSp_two hn2
      have : IsSimpleGroup L := eL.isSimpleGroup
      refine hsimple fun φ hφL hφD ℓ hℓL hℓ3 heq hD8 => ?_
      have e := hSp4 G L ℓ n hn he ⟨eL⟩ hℓL hℓ3
      rw [← heq] at e
      exact Or.inr (Or.inl ⟨h27, n, hn, he, ⟨eL⟩, hK φ hφL hφD hn2 e, hD8⟩)
    ·
      obtain ⟨eL⟩ := heL
      have hn2 : 2 ≤ n := by obtain ⟨k, hk⟩ := he; omega
      have := isSimpleGroup_projSU (m := 4) (n := n) le_rfl hn
      have : IsSimpleGroup L := eL.isSimpleGroup
      refine hsimple fun φ hφL hφD ℓ hℓL hℓ3 heq hD8 => ?_
      rcases hU4 G L ℓ n hn he ⟨eL⟩ hℓL hℓ3 with e | e
      · rw [← heq] at e
        exact Or.inr (Or.inr (Or.inl ⟨h27, n, hn, he, ⟨eL⟩,
          Or.inl (hK φ hφL hφD hn2 e), hD8⟩))
      · rw [← heq] at e
        exact Or.inr (Or.inr (Or.inl ⟨h27, n, hn, he, ⟨eL⟩,
          Or.inr (hK φ hφL hφD (by omega) e), hD8⟩))
    ·
      obtain ⟨eL⟩ := heL
      obtain ⟨hS3, hC, hcl, hne, hstr⟩ := star_SL3_three h211 h2131 hpair h27 hn he eL
      have hAL : A ≤ Subgroup.normalizer (L : Set G) :=
        Sec6.le_normalizer_of_mem_thetaComponentsAt h45 hpair.standing.toTheoremFourHyp hAe hcA
          hc1 L hLc
      refine ⟨hcl, hne, fun φ hφL hφD => ?_⟩
      obtain ⟨b, hbA, hbx, hev, heq⟩ := hstr φ hφL hφD.1
      have e := hSL3 G L A n hn he ⟨eL⟩ hAe hAL hC b hbA hbx hev
      rw [← heq] at e
      have hn2 : 2 ≤ n := by obtain ⟨k, hk⟩ := he; omega
      exact Or.inl ⟨h27, n, hn, he, nonempty_lBar_mulEquiv_SL3 hn he eL,
        hK φ hφL hφD hn2 e, hS3⟩
    ·
      obtain ⟨eL⟩ := heL
      have := isSimpleGroup_projSU (m := 5) (n := 2) (by norm_num) (by norm_num)
      have : IsSimpleGroup L := eL.isSimpleGroup
      refine hsimple fun φ hφL hφD ℓ hℓL hℓ3 heq hD8 => ?_
      rcases hU5 G L ℓ ⟨eL⟩ hℓL hℓ3 with e | hU
      · rw [← heq] at e
        exact Or.inr (Or.inr (Or.inr (Or.inl ⟨h27, ⟨eL⟩,
          Or.inr (hK φ hφL hφD (by norm_num) e), hD8⟩)))
      · rw [← heq] at hU
        exact Or.inr (Or.inr (Or.inr (Or.inl ⟨h27, ⟨eL⟩,
          Or.inl (nonempty_kOf_mulEquiv_of_U34 hAF hKW hcA hLc hφL hφD hU), hD8⟩)))
    ·
      obtain ⟨eB⟩ := hSL
      obtain ⟨hS3, hC, hcl, hne, hstr⟩ :=
        star_SL3_three_bar h211 h2131 hpair h27 (by norm_num) even_two eB
      have hAL : A ≤ Subgroup.normalizer (L : Set G) :=
        Sec6.le_normalizer_of_mem_thetaComponentsAt h45 hpair.standing.toTheoremFourHyp hAe hcA
          hc1 L hLc
      refine ⟨hcl, hne, fun φ hφL hφD => ?_⟩
      obtain ⟨b, hbA, ⟨x, hxL, hxb⟩, -, heq⟩ := hstr φ hφL hφD.1
      have hbc : b ∉ Subgroup.zpowers c := by
        intro h
        apply hxb
        obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp h
        exact (Commute.zpow_right (Subgroup.mem_centralizer_singleton_iff.mp (hLC hxL)) k).eq
      have hne' := inSubgroup_perfectResidual_ne_bot_of_lBar hAe hAL hLp (by norm_num)
        even_two eB hC hφL hφD.1.1 hbA heq
      have e := hCL b hbA hbc hne'
      rw [← heq] at e
      exact Or.inl ⟨h27, 2, by norm_num, even_two, ⟨eB⟩, hK φ hφL hφD le_rfl e, hS3⟩

end CFSG.RankThree.PartTwo.Sec21

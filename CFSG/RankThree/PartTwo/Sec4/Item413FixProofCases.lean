module

public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.RankThree.PartTwo.KFacts.KP7Suzuki
public import CFSG.RankThree.PartTwo.Sec4.Item413Cases
public import CFSG.RankThree.PartTwo.Sec4.Item47WStatement
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.RankThree.PartTwo.Sec4

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.KFacts
open CFSG.Assembly.RankThreeEven (projSL projSU projSp)

structure Inputs413Ranks : Prop where
  rankAutL2 : ∀ (p f : ℕ) [Fact p.Prime], p ≠ 3 → 1 ≤ f →
    CFSG.pRank 3 (MulAut (projSL 2 (GaloisField p f))) ≤ 3
  rankAutL3 : ∀ (p f : ℕ) [Fact p.Prime], p ≠ 3 → 1 ≤ f →
    CFSG.pRank 3 (MulAut (projSL 3 (GaloisField p f))) ≤ 3
  rankAutU3 : ∀ (p f : ℕ) [Fact p.Prime], p ≠ 3 → 1 ≤ f → 2 < p ^ f →
    CFSG.pRank 3 (MulAut (projSU 3 p f)) ≤ 3
  rankAutSL3 : ∀ (p f : ℕ) [Fact p.Prime] (K : Type) [Field K] [Finite K], p ≠ 3 →
    Nat.card K = p ^ f → CFSG.pRank 3 (MulAut (CFSG.Assembly.LowTwoRank.StatedSL 3 K)) ≤ 3
  rankAutSU3 : ∀ (p f : ℕ) [Fact p.Prime] (K : Type) [Field K] [Finite K], p ≠ 3 →
    Nat.card K = (p ^ f) ^ 2 → 2 < p ^ f →
      CFSG.pRank 3 (MulAut (CFSG.Assembly.LowTwoRank.StatedSU 3 (p ^ f) K)) ≤ 3
  rankAutSp4 : ∀ n : ℕ, 1 ≤ n → CFSG.pRank 3 (MulAut (projSp 2 (GaloisField 2 n))) ≤ 3
  rankAutG2 : ∀ (X : Type) [Group X] (n : ℕ), Blueprint.ChevalleyExceptionalModel X .G2 2 n →
    CFSG.pRank 3 (MulAut X) ≤ 3
  rankAutF4 : ∀ (X : Type) [Group X] (n : ℕ), Blueprint.ReeTitsModel X .twistedF4 2 n →
    CFSG.pRank 3 (MulAut X) ≤ 3
  rankAutD4 : ∀ (X : Type) [Group X] (n : ℕ),
    Blueprint.ChevalleyExceptionalModel X .trialityD4 2 n → CFSG.pRank 3 (MulAut X) ≤ 3
  rankG2 : ∀ (X : Type) [Group X] (p : ℕ) [Fact p.Prime], 3 < p →
    Blueprint.ChevalleyExceptionalModel X .G2 p 1 → CFSG.pRank 3 (X ⧸ Subgroup.center X) ≤ 3
  rankSp4 : ∀ (p : ℕ) [Fact p.Prime], 3 < p →
    CFSG.pRank 3 (projSp 2 (GaloisField p 1) ⧸ Subgroup.center (projSp 2 (GaloisField p 1))) ≤ 3
  rankU4 : ∀ (p : ℕ) [Fact p.Prime], 3 < p → p % 3 = 1 →
    CFSG.pRank 3 (projSU 4 p 1 ⧸ Subgroup.center (projSU 4 p 1)) ≤ 3
  rankL4 : ∀ (p : ℕ) [Fact p.Prime], 3 < p → p % 3 = 2 →
    CFSG.pRank 3 (projSL 4 (GaloisField p 1) ⧸ Subgroup.center (projSL 4 (GaloisField p 1))) ≤ 3
  rankU4Even : ∀ n : ℕ, 1 ≤ n →
    CFSG.pRank 3 (projSU 4 2 n ⧸ Subgroup.center (projSU 4 2 n)) ≤ 3
  rankA9 : CFSG.pRank 3 (alternatingGroup (Fin 9) ⧸ Subgroup.center (alternatingGroup (Fin 9))) ≤ 3
  rankSporadic : ∀ s ∈ sporadics46, s ≠ .McL →
    CFSG.pRank 3 (Blueprint.NativeSporadic.Carrier s ⧸
      Subgroup.center (Blueprint.NativeSporadic.Carrier s)) ≤ 3
  rankSeven : CFSG.pRank 3 (projSL 5 (GaloisField 2 1) ⧸
      Subgroup.center (projSL 5 (GaloisField 2 1))) ≤ 3 ∧
    CFSG.pRank 3 (projSp 3 (GaloisField 2 1) ⧸ Subgroup.center (projSp 3 (GaloisField 2 1))) ≤ 3 ∧
    CFSG.pRank 3 (projSU 5 2 2 ⧸ Subgroup.center (projSU 5 2 2)) ≤ 3
  rankEight : CFSG.pRank 3 (projSL 3 (GaloisField 3 1) ⧸
      Subgroup.center (projSL 3 (GaloisField 3 1))) ≤ 3 ∧
    CFSG.pRank 3 (projSU 3 3 1 ⧸ Subgroup.center (projSU 3 3 1)) ≤ 3
  rankTits : ∀ (X : Type) [Group X] (f : ℕ), Blueprint.ReeTitsModel X .Tits 2 f →
    CFSG.pRank 3 (X ⧸ Subgroup.center X) ≤ 3
  multiplier : ∀ (X : Type) [Group X] [Finite X], CFSG.IsQuasisimple X →
    Nat.Coprime (Nat.card (Subgroup.center X)) 6 →
    (Blueprint.ChevalleyExceptionalModel (X ⧸ Subgroup.center X) .G2 3 1 ∨
      Nonempty (X ⧸ Subgroup.center X ≃* Blueprint.NativeSporadic.McL) ∨
      Nonempty (X ⧸ Subgroup.center X ≃* projSL 4 (GaloisField 3 1)) ∨
      Nonempty (X ⧸ Subgroup.center X ≃* projSU 4 3 1)) →
    Subgroup.center X = ⊥

namespace Res413Fix

theorem exists_psl2_three_of_alt47W
    {H : Type} [Group H] [Finite H] (hin : Inputs413Ranks)
    {L : Subgroup H} {a : H} (hq : CFSG.IsQuasisimple (L ⧸ aschbacherSolvableCore 3 L))
    (h : Alt47W L a) {B : Subgroup (MulAut (L ⧸ aschbacherSolvableCore 3 L))}
    (hB : CFSG.Assembly.IsElemAbelian 3 B) {k : ℕ} (hk : Nat.card B = 3 ^ k) (hk4 : 4 ≤ k) :
    ∃ e : ℕ, 1 ≤ e ∧ Nonempty (L ⧸ aschbacherSolvableCore 3 L ≃* projSL 2 (GaloisField 3 e)) := by
  have h2 : 2 ^ 2 = 4 := by norm_num
  rcases h with ⟨p, e, _, -, he, ⟨e₁⟩, -⟩ | ⟨p, e, _, hp3, he1, -, hX, -⟩ | ⟨hX, -⟩ |
      ⟨n, hn, hX, -⟩ | ⟨n, hn, hD4⟩
  ·
    by_cases hp3 : p = 3
    · subst hp3
      exact ⟨3 * e, by omega, ⟨e₁⟩⟩
    · exact (false_of_rankAut e₁ hB hk hk4 (hin.rankAutL2 p (3 * e) hp3 (by omega))).elim
  ·
    exfalso
    have hq2 : 2 < p ^ e := lt_of_lt_of_le (by omega) (Nat.le_self_pow (by omega) p)
    rcases hX with ⟨K, _, _, ⟨hK, -, ⟨e₁⟩⟩ | ⟨hK, -, ⟨e₁⟩⟩⟩ | ⟨-, ⟨e₁⟩⟩ | ⟨-, ⟨e₁⟩⟩
    · exact false_of_rankAut e₁ hB hk hk4 (hin.rankAutSL3 p e K (by omega) hK)
    · exact false_of_rankAut e₁ hB hk hk4 (hin.rankAutSU3 p e K (by omega) hK hq2)
    · exact false_of_rankAut e₁ hB hk hk4 (hin.rankAutL3 p e (by omega) he1)
    · exact false_of_rankAut e₁ hB hk hk4 (hin.rankAutU3 p e (by omega) he1 hq2)
  ·
    exfalso
    rcases hX with ⟨m, hm, ⟨⟨e₁⟩⟩ | ⟨K, _, _, hK, ⟨e₁⟩⟩ | ⟨⟨e₁⟩⟩ | ⟨K, _, _, hK, ⟨e₁⟩⟩⟩ |
        ⟨n, hn, hSz | ⟨⟨e₁⟩⟩ | ⟨⟨e₁⟩⟩ | hG2 | hF4⟩
    · exact false_of_rankAut e₁ hB hk hk4 (hin.rankAutL2 2 m (by norm_num) hm)
    · rcases Nat.lt_or_ge m 2 with hm1 | hm2
      · obtain rfl : m = 1 := by omega
        exact false_of_mulEquiv_statedSU_three_two hq hK e₁
      · exact false_of_rankAut e₁ hB hk hk4 (hin.rankAutSU3 2 m K (by norm_num) hK
          (lt_of_lt_of_le (by norm_num) (Nat.pow_le_pow_right (by norm_num) hm2)))
    · rcases Nat.lt_or_ge m 2 with hm1 | hm2
      · obtain rfl : m = 1 := by omega
        exact false_of_mulEquiv_projSU_three_two hq e₁
      · exact false_of_rankAut e₁ hB hk hk4 (hin.rankAutU3 2 m (by norm_num) hm
          (lt_of_lt_of_le (by norm_num) (Nat.pow_le_pow_right (by norm_num) hm2)))
    · exact false_of_rankAut e₁ hB hk hk4 (hin.rankAutSL3 2 (2 * m) K (by norm_num) hK)
    · have := CFSG.RankThree.PartTwo.KFacts.KP7.pRank_three_mulAut_le_one hSz
      exact false_of_rankAut (MulEquiv.refl _) hB hk hk4 (this.trans (by norm_num))
    · exact false_of_rankAut e₁ hB hk hk4 (hin.rankAutL3 2 n (by norm_num) hn.pos)
    · exact false_of_rankAut e₁ hB hk hk4 (hin.rankAutSp4 n hn.pos)
    · exact false_of_rankAut (MulEquiv.refl _) hB hk hk4 (hin.rankAutG2 _ n hG2)
    · exact false_of_rankAut (MulEquiv.refl _) hB hk hk4 (hin.rankAutF4 _ n hF4)
  ·
    exfalso
    rcases hX with ⟨K, _, _, ⟨hK, -, ⟨e₁⟩⟩ | ⟨hK, -, ⟨e₁⟩⟩⟩ | ⟨-, ⟨e₁⟩⟩ | ⟨-, ⟨e₁⟩⟩
    · exact false_of_rankAut e₁ hB hk hk4 (hin.rankAutSL3 2 n K (by norm_num) hK)
    · rcases Nat.lt_or_ge n 2 with hn1 | hn2
      · obtain rfl : n = 1 := by omega
        exact false_of_mulEquiv_statedSU_three_two hq hK e₁
      · exact false_of_rankAut e₁ hB hk hk4 (hin.rankAutSU3 2 n K (by norm_num) hK
          (lt_of_lt_of_le (by norm_num) (Nat.pow_le_pow_right (by norm_num) hn2)))
    · exact false_of_rankAut e₁ hB hk hk4 (hin.rankAutL3 2 n (by norm_num) hn)
    · rcases Nat.lt_or_ge n 2 with hn1 | hn2
      · obtain rfl : n = 1 := by omega
        exact false_of_mulEquiv_projSU_three_two hq e₁
      · exact false_of_rankAut e₁ hB hk hk4 (hin.rankAutU3 2 n (by norm_num) hn
          (lt_of_lt_of_le (by norm_num) (Nat.pow_le_pow_right (by norm_num) hn2)))
  ·
    exact (false_of_rankAut (MulEquiv.refl _) hB hk hk4 (hin.rankAutD4 _ n hD4)).elim

theorem isSpecial413_of_le_inner {X : Type} [Group X] [Finite X]
    (hin : Inputs413Ranks)
    (hZspor : ∀ s ∈ sporadicCovers46,
      Subgroup.center (Blueprint.NativeSporadic.Carrier s) = ⊥)
    (hX : IsList46 X) (hq : CFSG.IsQuasisimple X) (hZodd : Odd (Nat.card (Subgroup.center X)))
    {B : Subgroup (MulAut X)} (hB : CFSG.Assembly.IsElemAbelian 3 B)
    (hBi : B ≤ (MulAut.conj : X →* MulAut X).range) {k : ℕ} (hk : Nat.card B = 3 ^ k)
    (hk4 : 4 ≤ k) : IsSpecial413 X := by
  have hZ13 : Nat.card (Subgroup.center X) ≤ 3 → Nat.card (Subgroup.center X) = 1 ∨
      Nat.card (Subgroup.center X) = 3 := fun h => by
    obtain ⟨t, ht⟩ := hZodd
    omega
  rcases hX with ⟨p, e, _, -, he, ⟨e₁⟩⟩ | ⟨p, e, _, hp3, he1, -, hSL | ⟨⟨e₁⟩⟩ | ⟨⟨e₁⟩⟩⟩ |
      ⟨p, _, hp3, hG2 | ⟨⟨e₁⟩⟩ | ⟨hp1, ⟨e₁⟩⟩ | ⟨hp2, ⟨e₁⟩⟩⟩ |
      (⟨n, hn, ⟨e₁⟩⟩ | hA6 | hA7) | (⟨s, hs, ⟨e₁⟩⟩ | ⟨s, hs, hext⟩) |
      (hchev | ⟨n, hn, hSL⟩) | (⟨⟨e₁⟩⟩ | ⟨⟨e₁⟩⟩ | ⟨⟨e₁⟩⟩) |
      ((⟨e, he1, he2, ⟨⟨e₁⟩⟩ | ⟨⟨e₁⟩⟩⟩) | ⟨⟨e₁⟩⟩ | ⟨hZ3, hG23 | ⟨⟨e₁⟩⟩⟩)
  ·
    by_cases hp3 : p = 3
    · subst hp3
      exact Or.inl ⟨e, he, ⟨e₁⟩⟩
    · exact (false_of_rankAut e₁ hB hk hk4 (hin.rankAutL2 p e hp3 he)).elim
  ·
    exfalso
    have hq2 : 2 < p ^ e := lt_of_lt_of_le (by omega) (Nat.le_self_pow (by omega) p)
    obtain ⟨K, _, _, ⟨hK, ⟨e₁⟩⟩ | ⟨hK, ⟨e₁⟩⟩⟩ := hSL
    · exact false_of_rankAut e₁ hB hk hk4 (hin.rankAutSL3 p e K (by omega) hK)
    · exact false_of_rankAut e₁ hB hk hk4 (hin.rankAutSU3 p e K (by omega) hK hq2)
  ·
    exact (false_of_rankAut e₁ hB hk hk4 (hin.rankAutL3 p e (by omega) he1)).elim
  ·
    have hq2 : 2 < p ^ e := lt_of_lt_of_le (by omega) (Nat.le_self_pow (by omega) p)
    exact (false_of_rankAut e₁ hB hk hk4 (hin.rankAutU3 p e (by omega) he1 hq2)).elim
  ·
    exact (false_of_rankInner (MulEquiv.refl _) hB hBi hk hk4 (hin.rankG2 X p hp3 hG2)).elim
  ·
    exact (false_of_rankInnerModel e₁ hB hBi hk hk4 (hin.rankSp4 p hp3)).elim
  ·
    exact (false_of_rankInnerModel e₁ hB hBi hk hk4 (hin.rankU4 p hp3 hp1)).elim
  ·
    exact (false_of_rankInnerModel e₁ hB hBi hk hk4 (hin.rankL4 p hp3 hp2)).elim
  ·
    exfalso
    rcases Nat.lt_or_ge n 9 with hn8 | hn9
    · exact false_of_rankInnerModel e₁ hB hBi hk hk4
        (pRank_three_le_of_not_dvd (not_dvd_card_alternatingGroup (by omega)))
    · obtain rfl : n = 9 := by omega
      exact false_of_rankInnerModel e₁ hB hBi hk hk4 hin.rankA9
  ·
    refine (false_of_isExtOf_card hq hA6 ?_ hB hBi hk hk4).elim
    intro h
    have := h.trans (card_alternatingGroup_dvd 6)
    revert this
    decide
  ·
    refine (false_of_isExtOf_card hq hA7 ?_ hB hBi hk hk4).elim
    intro h
    have := h.trans (card_alternatingGroup_dvd 7)
    revert this
    decide
  ·
    by_cases hsM : s = .McL
    · subst hsM
      have hZ : Subgroup.center X = ⊥ :=
        center_eq_bot_of_mulEquiv e₁ (hZspor .McL (by simp [sporadicCovers46]))
      exact Or.inr (Or.inr (Or.inr (Or.inr ⟨hZ, Or.inr (Or.inl ⟨e₁⟩)⟩)))
    · exact (false_of_rankInnerModel e₁ hB hBi hk hk4 (hin.rankSporadic s hs hsM)).elim
  ·
    have hs' := hs
    simp only [sporadicCovers46, List.mem_cons, List.not_mem_nil, or_false] at hs'
    rcases hs' with rfl | rfl | rfl | rfl
    · obtain ⟨-, ⟨eQ⟩⟩ := (isTripleCover_iff_isExtOf hq (hZspor _ hs)).mpr hext
      exact (false_of_rankInner (eQ.trans (quotientCenterEquivOfBot (hZspor _ hs)).symm) hB hBi
        hk hk4 (hin.rankSporadic .M22 (by simp [sporadics46]) (by decide))).elim
    · obtain ⟨-, ⟨eQ⟩⟩ := (isTripleCover_iff_isExtOf hq (hZspor _ hs)).mpr hext
      exact (false_of_rankInner (eQ.trans (quotientCenterEquivOfBot (hZspor _ hs)).symm) hB hBi
        hk hk4 (hin.rankSporadic .J3 (by simp [sporadics46]) (by decide))).elim
    · exact Or.inr (Or.inr (Or.inl (Or.inr hext)))
    · exact Or.inr (Or.inr (Or.inr (Or.inl (Or.inr hext))))
  ·
    exfalso
    rcases hchev with ⟨n, hn, ⟨⟨e₁⟩⟩ | ⟨⟨e₁⟩⟩ | ⟨⟨e₁⟩⟩ | ⟨⟨e₁⟩⟩ | ⟨⟨e₁⟩⟩⟩ |
        ⟨f, hG2 | hD4 | hSz | hF4 | hTits⟩
    · exact false_of_rankAut e₁ hB hk hk4 (hin.rankAutL2 2 n (by norm_num) hn)
    · exact false_of_rankAut e₁ hB hk hk4 (hin.rankAutL3 2 n (by norm_num) hn)
    · rcases Nat.lt_or_ge n 2 with hn1 | hn2
      · obtain rfl : n = 1 := by omega
        exact false_of_mulEquiv_projSU_three_two hq e₁
      · exact false_of_rankAut e₁ hB hk hk4 (hin.rankAutU3 2 n (by norm_num) hn
          (lt_of_lt_of_le (by norm_num) (Nat.pow_le_pow_right (by norm_num) hn2)))
    · exact false_of_rankAut e₁ hB hk hk4 (hin.rankAutSp4 n hn)
    · exact false_of_rankInnerModel e₁ hB hBi hk hk4 (hin.rankU4Even n hn)
    · exact false_of_rankAut (MulEquiv.refl _) hB hk hk4 (hin.rankAutG2 _ f hG2)
    · exact false_of_rankAut (MulEquiv.refl _) hB hk hk4 (hin.rankAutD4 _ f hD4)
    · have := CFSG.RankThree.PartTwo.KFacts.KP7.pRank_three_mulAut_le_one hSz
      exact false_of_rankAut (MulEquiv.refl _) hB hk hk4 (this.trans (by norm_num))
    · exact false_of_rankAut (MulEquiv.refl _) hB hk hk4 (hin.rankAutF4 _ f hF4)
    · exact false_of_rankInner (MulEquiv.refl _) hB hBi hk hk4 (hin.rankTits _ f hTits)
  ·
    exfalso
    obtain ⟨K, _, _, ⟨hK, ⟨e₁⟩⟩ | ⟨hK, ⟨e₁⟩⟩⟩ := hSL
    · exact false_of_rankAut e₁ hB hk hk4 (hin.rankAutSL3 2 n K (by norm_num) hK)
    · rcases Nat.lt_or_ge n 2 with hn1 | hn2
      · obtain rfl : n = 1 := by omega
        exact false_of_mulEquiv_statedSU_three_two hq hK e₁
      · exact false_of_rankAut e₁ hB hk hk4 (hin.rankAutSU3 2 n K (by norm_num) hK
          (lt_of_lt_of_le (by norm_num) (Nat.pow_le_pow_right (by norm_num) hn2)))
  ·
    exact (false_of_rankInnerModel e₁ hB hBi hk hk4 hin.rankSeven.1).elim
  · exact (false_of_rankInnerModel e₁ hB hBi hk hk4 hin.rankSeven.2.1).elim
  · exact (false_of_rankInnerModel e₁ hB hBi hk hk4 hin.rankSeven.2.2).elim
  ·
    rcases (show e = 1 ∨ e = 2 by omega) with rfl | rfl
    · exact (false_of_rankInnerModel e₁ hB hBi hk hk4 hin.rankEight.1).elim
    · exact Or.inr (Or.inl (Or.inl ⟨e₁⟩))
  ·
    rcases (show e = 1 ∨ e = 2 by omega) with rfl | rfl
    · exact (false_of_rankInnerModel e₁ hB hBi hk hk4 hin.rankEight.2).elim
    · exact Or.inr (Or.inl (Or.inr ⟨e₁⟩))
  ·
    have := (CFSG.LinearGroups.linear_projective_simple (K := GaloisField 3 1) (n := 4)
      (by norm_num) (Or.inl (by norm_num))).2.1
    exact Or.inr (Or.inr (Or.inr (Or.inr ⟨center_eq_bot_of_mulEquiv_isSimpleGroup hq
      (e₁.trans (projSLEquivPSLn 4 _)), Or.inr (Or.inr (Or.inl ⟨e₁⟩))⟩)))
  ·
    rcases hZ13 hZ3 with h1 | h3
    · have hZ : Subgroup.center X = ⊥ := Subgroup.eq_bot_of_card_eq _ h1
      exact Or.inr (Or.inr (Or.inr (Or.inr ⟨hZ, Or.inl
        (CFSG.SectionRank.chevalleyExceptionalModel_of_mulEquiv
          (quotientCenterEquivOfBot hZ).symm hG23)⟩)))
    · exact Or.inr (Or.inr (Or.inr (Or.inl (Or.inl ⟨h3, hG23⟩))))
  ·
    rcases hZ13 hZ3 with h1 | h3
    · have hZ : Subgroup.center X = ⊥ := Subgroup.eq_bot_of_card_eq _ h1
      exact Or.inr (Or.inr (Or.inr (Or.inr ⟨hZ, Or.inr (Or.inr (Or.inr
        ⟨(quotientCenterEquivOfBot hZ).symm.trans e₁⟩))⟩)))
    · exact Or.inr (Or.inr (Or.inl (Or.inl ⟨h3, ⟨e₁⟩⟩)))

theorem alt413_three
    {G : Type} [Group G] [Finite G] (hin : Inputs413Ranks) {L A E : Subgroup G} {c : G}
    (hL : IsComponent L) (hAmax : Maximal (fun B : Subgroup G => CFSG.Assembly.IsElemAbelian 3 B) A)
    (hAc : A ⊓ Subgroup.centralizer (L : Set G) = Subgroup.zpowers c)
    (hAN : A ≤ Subgroup.normalizer (L : Set G)) (hout : ∀ a ∈ A, ¬ InducesOuterTheta a L)
    (hZL : Odd (Nat.card (Subgroup.center L)))
    (hZ : Subgroup.center (L ⧸ aschbacherSolvableCore 3 L) = ⊥)
    (h5 : Blueprint.ChevalleyExceptionalModel (L ⧸ aschbacherSolvableCore 3 L) .G2 3 1 ∨
      Nonempty (L ⧸ aschbacherSolvableCore 3 L ≃* Blueprint.NativeSporadic.McL) ∨
      Nonempty (L ⧸ aschbacherSolvableCore 3 L ≃* projSL 4 (GaloisField 3 1)) ∨
      Nonempty (L ⧸ aschbacherSolvableCore 3 L ≃* projSU 4 3 1)) :
    Alt413 L A E c := by
  have hθZ := aschbacherSolvableCore_le_center hL.1
  have hZθ : Subgroup.center L = aschbacherSolvableCore 3 L := by
    refine le_antisymm (fun z hz => ?_) hθZ
    have h1 : (z : L ⧸ aschbacherSolvableCore 3 L) ∈
        Subgroup.center (L ⧸ aschbacherSolvableCore 3 L) := by
      rw [(CFSG.LocalCores.quasisimple_central_quotient hL.1 _ hθZ).2.2]
      exact Subgroup.mem_map_of_mem _ hz
    rw [hZ, Subgroup.mem_bot] at h1
    exact (QuotientGroup.eq_one_iff z).mp h1
  have hcop : Nat.Coprime (Nat.card (Subgroup.center L)) 6 := by
    have h2 : ¬ 2 ∣ Nat.card (Subgroup.center L) := fun h => by
      obtain ⟨u, hu⟩ := hZL
      omega
    have h3 : ¬ 3 ∣ Nat.card (Subgroup.center L) := by
      rw [hZθ]
      exact (solvable_prime_complement_core_characterization Nat.prime_three).2.2.1
    rw [show (6 : ℕ) = 2 * 3 by norm_num]
    exact Nat.Coprime.mul_right ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr h2).symm
      ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr h3).symm
  set eZ : L ⧸ Subgroup.center L ≃* L ⧸ aschbacherSolvableCore 3 L :=
    QuotientGroup.quotientMulEquivOfEq hZθ
  have hZL1 : Subgroup.center L = ⊥ := by
    refine hin.multiplier L hL.1 hcop ?_
    rcases h5 with h | ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩
    · exact Or.inl (CFSG.SectionRank.chevalleyExceptionalModel_of_mulEquiv eZ h)
    · exact Or.inr (Or.inl ⟨eZ.trans e⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨eZ.trans e⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨eZ.trans e⟩))
  set eL : L ≃* L ⧸ aschbacherSolvableCore 3 L := (quotientCenterEquivOfBot hZL1).symm.trans eZ
  obtain ⟨hdec, hinf⟩ := eq_sup_of_forall_inner hZL1 hAmax hAc fun a ha =>
    exists_inner_of_not_inducesOuterTheta hL.1 (hAN ha) (hout a ha)
  refine Or.inr (Or.inr ⟨hdec, hinf, ?_⟩)
  rcases h5 with h | ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩
  · exact Or.inl (CFSG.SectionRank.chevalleyExceptionalModel_of_mulEquiv eL h)
  · exact Or.inr (Or.inl ⟨eL.trans e⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨eL.trans e⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨eL.trans e⟩))

end Res413Fix

end CFSG.RankThree.PartTwo.Sec4

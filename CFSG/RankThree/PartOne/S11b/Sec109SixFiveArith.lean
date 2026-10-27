module

public import CFSG.RankThree.PartOne.S11b.Sec109Setup
import CFSG.RankThree.PartOne.S9.Planes.Basic
import CFSG.LocalAnalysis.ComponentInitial.LinearFlagOrder
import CFSG.LocalAnalysis.ComponentInitial.LinearCoverModel
public import CFSG.LocalAnalysis.ComponentInitial.LinearFlagElation

public section

namespace CFSG.RankThree.PartOne

open Subgroup CFSG CFSG.Assembly CFSG.Assembly.RankThreeEven CFSG.RankThree
  CFSG.RankThree.LocalRank CFSG.RankThree.GroupTheory CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.Assembly.LowTwoRank (StatedClassicalModel projectiveSpecialLinearGroupEquivStatedProj)

namespace Sec109

theorem exists_elementary_abelian_of_le_localRank {G : Type*} [Group G] [Finite G] {p : ℕ}
    (hp : p.Prime) {k : ℕ} (hk : 1 ≤ k) (hle : k ≤ localRank p G) :
    ∃ U : Subgroup G, IsPGroup 2 U ∧ U ≠ ⊥ ∧ ∃ E : Subgroup G,
      E ≤ Subgroup.normalizer (U : Set G) ∧ IsElementaryAbelian p E ∧ Nat.card E = p ^ k := by
  by_contra hno
  push Not at hno
  have hlt : localRank p G ≤ k - 1 := by
    refine csSup_le' ?_
    rintro m ⟨H', ⟨S, hS0, hS2, rfl⟩, rfl⟩
    by_contra hm
    push Not at hm
    obtain ⟨E, hEN, hE, hEc⟩ := (Planes.le_pRank_iff hp
      (Subgroup.normalizer (S : Set G)) k).1 (by omega)
    exact hno S hS2 hS0 E hEN hE hEc
  omega

@[expose] def LnTwoEvenRankFour : Prop :=
  ∀ (L : Type) [Group L] [Finite L] (n : ℕ), StatedClassicalModel L .PSL n 2 1 → 8 ≤ n →
    4 ≤ evenRank L

theorem card_projectiveSL_two {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2) {n : ℕ}
    (hn : 2 ≤ n) :
    Nat.card (projectiveSL n K) =
      2 ^ (n * (n - 1) / 2) * ∏ j ∈ Finset.Icc 2 n, (2 ^ j - 1) := by
  have hZ : Nat.card (scalars n K) = 1 := by
    have h := card_scalars_dvd (K := K) (n := n) (by omega)
    rw [hK] at h
    exact Nat.dvd_one.mp h
  rw [card_projectiveSL, hZ, Nat.div_one, card_SL_eq (by omega), hK]

theorem eq_seven_of_sq_dvd {n p : ℕ} (hn3 : 3 ≤ n) (hn7 : n ≤ 7) (hp : p.Prime) (hp5 : 5 ≤ p)
    (hdvd : p ^ 2 ∣ 2 ^ (n * (n - 1) / 2) * ∏ j ∈ Finset.Icc 2 n, (2 ^ j - 1)) :
    p = 7 ∧ (n = 6 ∨ n = 7) := by
  have hp127 : p ≤ 127 := by
    have h1 : p ∣ 2 ^ (n * (n - 1) / 2) * ∏ j ∈ Finset.Icc 2 n, (2 ^ j - 1) :=
      (dvd_pow_self p two_ne_zero).trans hdvd
    rcases (Nat.Prime.dvd_mul hp).mp h1 with h2 | h2
    · have := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow h2)
      omega
    · obtain ⟨j, hj, hpj⟩ := (Prime.dvd_finsetProd_iff hp.prime _).mp h2
      have hj7 : j ≤ 7 := (Finset.mem_Icc.mp hj).2.trans hn7
      have hle : p ≤ 2 ^ j - 1 :=
        Nat.le_of_dvd (Nat.sub_pos_of_lt (Nat.one_lt_two_pow (by
          have := (Finset.mem_Icc.mp hj).1; omega))) hpj
      have h128 : 2 ^ j ≤ 2 ^ 7 := Nat.pow_le_pow_right (by norm_num) hj7
      omega
  have key : ∀ n ∈ Finset.Icc 3 7, ∀ p ∈ Finset.Icc 5 127, p.Prime →
      p ^ 2 ∣ 2 ^ (n * (n - 1) / 2) * ∏ j ∈ Finset.Icc 2 n, (2 ^ j - 1) →
        p = 7 ∧ (n = 6 ∨ n = 7) := by
    decide +kernel
  exact key n (Finset.mem_Icc.mpr ⟨hn3, hn7⟩) p (Finset.mem_Icc.mpr ⟨hp5, hp127⟩) hp hdvd

theorem eq_seven_of_le_seven {L : Type} [Group L] [Finite L] {n p : ℕ}
    (hmodel : StatedClassicalModel L .PSL n 2 1) (hn7 : n ≤ 7) (hp : p.Prime) (hp5 : 5 ≤ p)
    (h2 : 2 ≤ localRank p L) : p = 7 ∧ (n = 6 ∨ n = 7) := by
  obtain ⟨⟨-, -, hn, h22, -⟩, K, _, _, hK, ⟨e⟩⟩ := hmodel
  have hn3 : 3 ≤ n := by
    by_contra h
    have h2' : n = 2 := by omega
    subst h2'
    exact h22 (by simp)
  have hK2 : Nat.card K = 2 := by simpa using hK
  let e' : L ≃* projectiveSL n K :=
    e.trans ((projectiveSpecialLinearGroupEquivStatedProj n K).symm.trans
      (LinearCover.projectiveSpecialLinearEquivProjectiveSL n K))
  obtain ⟨U, -, -, E, -, hE, hEc⟩ :=
    exists_elementary_abelian_of_le_localRank hp (by norm_num : 1 ≤ 2) h2
  have hdvd : p ^ 2 ∣ Nat.card L := hEc ▸ Subgroup.card_subgroup_dvd_card E
  rw [Nat.card_congr e'.toEquiv, card_projectiveSL_two hK2 (by omega)] at hdvd
  exact eq_seven_of_sq_dvd hn3 hn7 hp hp5 hdvd

theorem sec65LnTwo_of_evenRank (h : LnTwoEvenRankFour) : Sec65LnTwo := by
  intro L _ _ n p hmodel hp hp5 hev h2
  have hn7 : n ≤ 7 := by
    by_contra hn
    have := h L n hmodel (by omega)
    omega
  exact eq_seven_of_le_seven hmodel hn7 hp hp5 h2

end Sec109

end CFSG.RankThree.PartOne

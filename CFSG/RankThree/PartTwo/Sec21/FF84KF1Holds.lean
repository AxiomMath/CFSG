module

public import CFSG.RankThree.PartTwo.Sec21.FF84S23KFacts
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.SmallRank.Lemma121
public import Certificates.Data.ExceptionalSL3

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF84

open CFSG
open CFSG.Assembly (InCatalog)
open CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.SmallRank

theorem isElemAbelian_of_card_nine {K : Type} [Group K] {P : Subgroup K} (h9 : Nat.card P = 9)
    (hncyc : ¬ IsCyclic P) : CFSG.Open.IsElemAbelian 3 P := by
  haveI : Finite P := Nat.finite_of_card_ne_zero (by rw [h9]; norm_num)
  refine ⟨IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := 3) (by simpa using h9), ?_⟩
  intro x hx
  have hdvd : orderOf (⟨x, hx⟩ : P) ∣ 9 := h9 ▸ orderOf_dvd_natCard _
  have h9' : orderOf (⟨x, hx⟩ : P) ≠ 9 := fun h =>
    hncyc (isCyclic_of_orderOf_eq_card _ (h.trans h9.symm))
  have h3 : orderOf (⟨x, hx⟩ : P) ∣ 3 := by
    have : orderOf (⟨x, hx⟩ : P) ∈ Nat.divisors 9 := by simpa using hdvd
    have hdiv : Nat.divisors 9 = {1, 3, 9} := by decide
    rw [hdiv] at this
    simp only [Finset.mem_insert, Finset.mem_singleton] at this
    rcases this with h | h | h
    · rw [h]; exact one_dvd _
    · rw [h]
    · exact absurd h h9'
  have h := congrArg Subtype.val (orderOf_dvd_iff_pow_eq_one.1 h3)
  simpa [Subgroup.coe_pow] using h


theorem ff84KF1_holds : FF84KF1 := by
  intro K _ _ hs hnab hcat P hP9 hncyc P₁ hP₁ hP₁3 hle
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hel := isElemAbelian_of_card_nine hP9 hncyc
  haveI hcomm : IsMulCommutative (P : Subgroup K) := hel.1
  have hrank : 2 ≤ CFSG.Open.pRank 3 (P : Subgroup K) :=
    CFSG.SectionRank.le_pRank (k := 2) (by norm_num) le_rfl hel (by rw [hP9]; norm_num)
  obtain ⟨g, hgL, hgne⟩ := kFactWeakClosureInner_holds 3 Nat.prime_three (by norm_num) K hs hnab
    hcat P hcomm hrank P₁ hP₁ hP₁3
  exact hgne (map_conj_eq_of_normalizer_le P hP₁ hgL hle)

end CFSG.RankThree.PartTwo.Sec21.FF84

module

import CFSG.RankThree.LocalRank.InvariantPrimeComplementOdd
public import CFSG.RankThree.PartTwo.Setup

public section

namespace CFSG.RankThree.PartTwo.Sec6

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Assembly.RankThreeEven (localRank)

variable {G : Type*} [Group G] [Finite G]

theorem four_le_pRank_of_mem_partTwoF_diff {A : Subgroup G}
    (hA : A ∈ partTwoF G \ partTwoE G) : 4 ≤ CFSG.Assembly.pRank 3 A := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨⟨hAab, -, E, hEmem, hEA⟩, hAE⟩ := hA
  have hApg : IsPGroup 3 A := fun g => ⟨1, Subtype.ext (by simpa using hAab.2 g g.2)⟩
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hApg
  have hEcard : Nat.card E = 27 := hEmem.2.1
  have hk4 : 4 ≤ k := by
    have hdvd : 3 ^ 3 ∣ 3 ^ k := by
      rw [← hk, show (3 : ℕ) ^ 3 = 27 by norm_num, ← hEcard]
      exact Subgroup.card_dvd_of_le hEA
    have hk3 : 3 ≤ k := (Nat.pow_dvd_pow_iff_le_right (by norm_num)).mp hdvd
    by_contra hlt
    have hkeq : k = 3 := by omega
    apply hAE
    have hEA' : E = A := Subgroup.eq_of_le_of_card_ge hEA (by rw [hk, hkeq, hEcard]; norm_num)
    exact hEA' ▸ hEmem
  exact hk4.trans (le_csSup (CFSG.RankThreeEvenClassification.Helpers.pRank_bddAbove 3
    Nat.prime_three A) ⟨A, le_rfl, hAab, hk⟩)

omit [Finite G] in
theorem le_normalizer_map_subtype {H : Subgroup G} (K : Subgroup H) [K.Normal] :
    H ≤ Subgroup.normalizer ((K.map H.subtype : Subgroup G) : Set G) := by
  have h := Subgroup.le_normalizer_map (H := K) H.subtype
  rwa [Subgroup.normalizer_eq_top, Subgroup.map_top, Subgroup.range_subtype] at h

theorem rank3II_6_3_of_localRank_le (h3 : localRank 3 G ≤ 3) {A : Subgroup G}
    (hA : A ∈ partTwoF G \ partTwoE G) {a : G} (ha : a ∈ A) :
    Odd (Nat.card (inSubgroup (CFSG.pPrimeCore 3) (Subgroup.centralizer {a}))) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hAab := hA.1.1
  have hApg : IsPGroup 3 A := fun g => ⟨1, Subtype.ext (by simpa using hAab.2 g g.2)⟩
  have hrank : localRank 3 G < CFSG.Assembly.pRank 3 A := by
    have := four_le_pRank_of_mem_partTwoF_diff hA
    omega
  have hAC : A ≤ Subgroup.centralizer {a} := fun x hx =>
    Subgroup.mem_centralizer_singleton_iff.mpr
      (congrArg Subtype.val (hAab.1.is_comm.comm ⟨x, hx⟩ ⟨a, ha⟩))
  have hAX : A ≤ Subgroup.normalizer
      (inSubgroup (CFSG.pPrimeCore 3) (Subgroup.centralizer {a}) : Set G) :=
    hAC.trans (le_normalizer_map_subtype _)
  have hX : ¬ 3 ∣ Nat.card (inSubgroup (CFSG.pPrimeCore 3) (Subgroup.centralizer {a})) := by
    rw [inSubgroup, Subgroup.card_map_of_injective (Subgroup.subtype_injective _)]
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp CFSG.pPrimeCore_coprime_card
  exact above_two_local_rank_invariant_prime_complement_odd Nat.prime_three hApg hrank hAX hX

theorem rank3II_6_3 :
    ∀ (G : Type) [Group G] [Finite G], PartTwoStanding G → ∀ A ∈ partTwoF G \ partTwoE G,
      ∀ a ∈ A, a ≠ 1 →
        Odd (Nat.card (inSubgroup (CFSG.pPrimeCore 3) (Subgroup.centralizer {a}))) :=
  fun _ _ _ h _ hA _ ha _ =>
  rank3II_6_3_of_localRank_le h.localRank_three.le hA ha

end CFSG.RankThree.PartTwo.Sec6

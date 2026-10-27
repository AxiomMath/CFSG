module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.RankThreeEvenDefs
import CFSG.RankThree.LocalRank.PrimeComplementCentralizesNormal
import CFSG.RankThree.PartTwo.Sec11.Coprime

public section

namespace CFSG.RankThree.PartTwo.Sec11

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open scoped commutatorElement

namespace Item1130Proof

section General

variable {G : Type*} [Group G]

theorem eq_of_le_of_ne [Finite G] {T C R : Subgroup G} (hTC : T ≤ C) (hCR : C ≤ R) (hne : C ≠ R)
    (hcard : Nat.card R = 3 * Nat.card T) : C = T := by
  have hT0 : 0 < Nat.card T := Nat.card_pos
  obtain ⟨m, hm⟩ := Subgroup.card_dvd_of_le hTC
  obtain ⟨n, hn⟩ := Subgroup.card_dvd_of_le hCR
  have hmn : m * n = 3 := by
    apply Nat.eq_of_mul_eq_mul_left hT0
    rw [← mul_assoc, ← hm, ← hn, hcard, mul_comm]
  have hn1 : n ≠ 1 := by
    rintro rfl
    rw [mul_one] at hn
    exact hne (Subgroup.eq_of_le_of_card_ge hCR hn.le)
  have hm1 : m = 1 := by
    have hn3 : n ∣ 3 := ⟨m, by rw [← hmn, mul_comm]⟩
    rcases (Nat.dvd_prime Nat.prime_three).mp hn3 with h1 | h3
    · exact absurd h1 hn1
    · subst h3
      omega
  refine (Subgroup.eq_of_le_of_card_ge hTC ?_).symm
  rw [hm, hm1, mul_one]

theorem card_sup_zpowers_eq {R : Subgroup G} {g : G} (hgN : g ∈ Subgroup.normalizer (R : Set G))
    (hgR : g ∉ R) (hg3 : g ^ 3 ∈ R) :
    Nat.card (R ⊔ Subgroup.zpowers g : Subgroup G) = 3 * Nat.card R := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hLE : Subgroup.zpowers g ≤ Subgroup.normalizer (R : Set G) := Subgroup.zpowers_le.mpr hgN
  have := Subgroup.normal_subgroupOf_of_le_normalizer hLE
  have := Subgroup.normal_subgroupOf_sup_of_le_normalizer hLE
  set q : Subgroup.zpowers g ⧸ R.subgroupOf (Subgroup.zpowers g) :=
    ((⟨g, Subgroup.mem_zpowers g⟩ : Subgroup.zpowers g) : _ ⧸ R.subgroupOf (Subgroup.zpowers g))
    with hq
  have hq3 : q ^ 3 = 1 := by
    rw [hq, ← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
    simpa using hg3
  have hq1 : q ≠ 1 := by
    rw [hq, Ne, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
    exact hgR
  have hgen : ∀ y : Subgroup.zpowers g ⧸ R.subgroupOf (Subgroup.zpowers g),
      y ∈ Subgroup.zpowers q := by
    intro y
    induction y using QuotientGroup.induction_on with
    | H z =>
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp z.2
      refine Subgroup.mem_zpowers_iff.mpr ⟨k, ?_⟩
      rw [hq, ← QuotientGroup.mk_zpow]
      congr 1
      exact Subtype.ext (by simpa using hk)
  have hcard : Nat.card (Subgroup.zpowers g ⧸ R.subgroupOf (Subgroup.zpowers g)) = 3 := by
    rw [← orderOf_eq_card_of_forall_mem_zpowers hgen]
    exact orderOf_eq_prime hq3 hq1
  have e := QuotientGroup.quotientInfEquivProdNormalizerQuotient (Subgroup.zpowers g) R hLE
  have hcard' : Nat.card ((Subgroup.zpowers g ⊔ R : Subgroup G) ⧸
      R.subgroupOf (Subgroup.zpowers g ⊔ R)) = 3 := by
    rw [← Nat.card_congr e.toEquiv, hcard]
  have hR : Nat.card (R.subgroupOf (Subgroup.zpowers g ⊔ R)) = Nat.card R :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe le_sup_right).toEquiv
  have hsup : R ⊔ Subgroup.zpowers g = Subgroup.zpowers g ⊔ R := sup_comm _ _
  rw [hsup, Subgroup.card_eq_card_quotient_mul_card_subgroup (R.subgroupOf _), hcard', hR]

end General

end Item1130Proof

end CFSG.RankThree.PartTwo.Sec11

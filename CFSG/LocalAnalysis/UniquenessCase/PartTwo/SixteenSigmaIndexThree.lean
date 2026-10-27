module

public import CFSG.GroupTheory.PRankZeroOfPrimeNotDvd
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.MbarSigmaRank
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC23Unique
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.Quasithin.EmptyFaithful.T1515C4Mod

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

theorem sig_eq_three_of_mbar_card_two_pow_mul_three_pow
    (D : Data G) (hx : DataExt D) (h61 : UC6.R6_1 D) (h127 : R127 D)
    {V₀ V : Subgroup G} (h16 : Hyp16 D V₀ V) (hV : IsElemAbelian 2 V)
    {a b : ℕ}
    (hcard : Nat.card ↥(Mbar D.M V₀ V hV) = 2 ^ a * 3 ^ b) :
    D.sig = {3} := by
  have hcard4 : Nat.card V₀ ≤ 4 := c23_card_v0_le_four D h16
  have hmem : ∀ q ∈ D.sig, q = 3 := by
    intro q hq
    by_contra hq3
    have hqprime : q.Prime := (D.sig_prime q hq).1
    have hq2 : q ≠ 2 := (D.sig_prime q hq).2
    have hrank : 2 ≤ CFSG.Open.pRank q (Mbar D.M V₀ V hV) :=
      S17.two_le_pRank_mbar_of_mem_sig h16.hyp125 hx h61 h127 hcard4 hq
    have hnotdvd : ¬ q ∣ Nat.card ↥(Mbar D.M V₀ V hV) := by
      intro hdvd
      rw [hcard] at hdvd
      rcases (Nat.Prime.dvd_mul hqprime).1 hdvd with hq2pow | hq3pow
      · exact hq2 ((Nat.prime_dvd_prime_iff_eq hqprime Nat.prime_two).1
          (hqprime.dvd_of_dvd_pow hq2pow))
      · exact hq3 ((Nat.prime_dvd_prime_iff_eq hqprime Nat.prime_three).1
          (hqprime.dvd_of_dvd_pow hq3pow))
    have hzero : CFSG.Open.pRank q (⊤ : Subgroup ↥(Mbar D.M V₀ V hV)) = 0 :=
      CFSG.pRank_eq_zero_of_not_dvd_card hqprime hnotdvd
    have hEq : CFSG.Open.pRank q (Mbar D.M V₀ V hV) =
        CFSG.Open.pRank q (⊤ : Subgroup ↥(Mbar D.M V₀ V hV)) :=
      CFSG.SectionRank.pRank_eq_pRank_top_subgroup (p := q) (Mbar D.M V₀ V hV)
    rw [hEq, hzero] at hrank
    omega
  refine Set.eq_singleton_iff_unique_mem.2 ⟨?_, hmem⟩
  obtain ⟨q, hq⟩ := hx.sig_nonempty
  rw [hmem q hq] at hq
  exact hq

end CFSG.LocalAnalysis.UniquenessCase.PartTwo

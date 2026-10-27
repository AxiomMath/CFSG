module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S2112E3
public import CFSG.LocalAnalysis.UniquenessCase.UC22R847E3NNOut
public import CFSG.LocalAnalysis.UniquenessCase.UC22S215SetupThree
public import CFSG.LocalAnalysis.UniquenessCase.UC22S21rTorus
public import CFSG.LocalAnalysis.UniquenessCase.UC22S21r899E3
import CFSG.LocalAnalysis.UniquenessCase.UC22S2112L2Meet
import CFSG.LocalAnalysis.UniquenessCase.UC22S13xe
import CFSG.LocalAnalysis.UniquenessCase.UC22S21rU4PC
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.ProofsEightCaseTwo
import CFSG.Quasithin.Vol2.KGFact838
public import CFSG.LocalAnalysis.UniquenessCase.UC22P21a

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)
open CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7 (StronglyEmbeddedFive
  StronglyEmbeddedFiveZ StronglyEmbeddedSolvableQ StronglyEmbeddedThree)
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Three (dataOfSetup)

variable {G : Type} [Group G] [Finite G]

theorem uc22s2112e3_inf_eq_bot_of_not_normal {D : Data G} {Ch : Choice2011 G}
    (hSg : UC6S846.SigmaStd D) (h847 : R847E3ThinNNOut D) (hH : H1930 D) (c : Ctx21 D Ch)
    (hev : Even c.n) {L : Subgroup G} (hL : L ∈ calC D.M) (hLN : ¬ (L.subgroupOf D.M).Normal)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hLp : IsL2Odd (Bar2 L) p) :
    c.B ⊓ L = ⊥ := by
  by_contra hne
  have hodd : Odd (Nat.card ↥(c.B ⊓ L)) :=
    Odd.of_dvd_nat (uc22s13xe_odd_card_B c) (Subgroup.card_dvd_of_le inf_le_left)
  have h1 : Nat.card ↥(c.B ⊓ L) ≠ 1 := fun h => hne (Subgroup.eq_bot_of_card_eq _ h)
  obtain ⟨r, hr, hrd⟩ := Nat.exists_prime_and_dvd h1
  have : Fact r.Prime := ⟨hr⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' r hrd
  have hr2 : r ≠ 2 := by
    rintro rfl
    exact (Nat.not_even_iff_odd.2 hodd) (even_iff_two_dvd.2 hrd)
  have hxBL := Subgroup.mem_inf.1 x.2
  have hXB : Subgroup.zpowers (x : G) ≤ c.B := Subgroup.zpowers_le.2 hxBL.1
  have hXL : Subgroup.zpowers (x : G) ≤ L := Subgroup.zpowers_le.2 hxBL.2
  have hXcard : Nat.card ↥(Subgroup.zpowers (x : G)) = r := by
    rw [Nat.card_zpowers, Subgroup.orderOf_coe, hx]
  obtain ⟨q, hq⟩ := hSg.nonempty
  obtain ⟨hqP, hq2⟩ := D.sig_prime q hq
  have hq3 : q ≠ 3 := by
    rintro rfl
    exact Nat.not_odd_iff_even.2 hev
      (u4p_odd_n D Ch hH c (UC6S846.sp_of_mem_sig hSg (UC6S846.not_solvable_of_mem_calC hL) hq))
  have hout : ¬ q ∣ Nat.card (Outer (Bar2 L)) := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 (CFSG.Quasithin.H13.KG838.isPGroup_outer_psl_two_prime
      (CFSG.Blueprint.LieModel.statedClassicalModel hLp (by decide)))
    rw [hk]
    intro hqO
    exact hq2 ((Nat.prime_dvd_prime_iff_eq hqP Nat.prime_two).1 (hqP.dvd_of_dvd_pow hqO))
  exact s21_2 D Ch hH c _ hXB (h847 L hL hLN (thin8_of_isL2Odd_bar2 hp hp2 hLp) _ hXL r hr hr2
    hXcard q hq (hqP.five_le_of_ne_two_of_ne_three hq2 hq3) hout)

theorem s21_12R3_of_s21_12aF {D : Data G} {Ch : Choice2011 G} (h5 : S21_5 D Ch)
    (hSg : UC6S846.SigmaStd D) (h847 : R847E3ThinNNOut D) (ha : S21_12aF D Ch) :
    S21_12R3 D Ch := fun hH c L hL p hp hp2 hch =>
  ⟨ha hH c L hL p hp hp2 hch, fun hLN hev hLp => by
    have hBN : c.B ≤ normalizer (L : Set G) := h5 hH c L hL
    exact uc22s2112e3_commutator_le c hL hp hp2 hLp hBN (uc22s2112_le_normalizer_inf c hBN
      (uc22s2112e3_inf_eq_bot_of_not_normal hSg h847 hH c hev hL hLN hp hp2 hLp))⟩

section Certified


theorem s21_12R3_dataOfSetup_of_s21_12aF (hSQ : StronglyEmbeddedSolvableQ)
    (hSE : StronglyEmbeddedFive) (hSEZ : StronglyEmbeddedFiveZ) (hK3 : StronglyEmbeddedThree)
    (hKThin : KThinSimple) (hThin : PartTwo.ThinList13) (hS : Standing G)
    (hUC : rankThreeUC G) (S : Setup G) {Ch : Choice2011 G}
    (h82 : F08.R82 (dataOfSetup hS S)) (h211 : S21_1 (dataOfSetup hS S) Ch)
    (ha : S21_12aF (dataOfSetup hS S) Ch) : S21_12R3 (dataOfSetup hS S) Ch := by
  have hSg := UC6S846.sigmaStd_dataOfSetup hS S
  exact s21_12R3_of_s21_12aF
    (s21_5_dataOfSetup hSQ hSE hK3 hKThin hS S h82
      (s21_15Two_of_certificate113 _ Ch h211 hSg (uc22r899e3_dataOfSetup hS hUC S)))
    hSg (r847E3ThinNNOut_dataOfSetup hSE hSEZ hThin hS S) ha

end Certified

end CFSG.LocalAnalysis.UniquenessCase.UC22

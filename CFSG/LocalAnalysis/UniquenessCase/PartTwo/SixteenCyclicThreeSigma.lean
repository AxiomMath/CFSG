module

public import CFSG.LinearAlgebra.OmegaSemilinearCard
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenCyclicThreeCoordinates
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15R1526P0a
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15RankChevOrth
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.MbarSigmaRank
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightS1Red

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.LinearAlgebra CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear

variable {G : Type} [Group G] [Finite G]

theorem sig_eq_three_of_mbar_card_dvd_362880
    (D : Data G) (hx : DataExt D) (h61 : UC6.R6_1 D) (h127 : R127 D)
    {V₀ V : Subgroup G} (h16 : Hyp16 D V₀ V) (hV : IsElemAbelian 2 V)
    (hcard : Nat.card ↥(Mbar D.M V₀ V hV) ∣ 362880) :
    D.sig = {3} := by
  haveI : Finite (MulAut (Vtil V₀ V hV)) :=
    Finite.of_injective
      (fun f : MulAut (Vtil V₀ V hV) => (f : Vtil V₀ V hV → Vtil V₀ V hV))
      (fun _ _ h => MulEquiv.ext (congrFun h))
  have hcard4 : Nat.card V₀ ≤ 4 := c23_card_v0_le_four D h16
  have hmem : ∀ q ∈ D.sig, q = 3 := by
    intro q hq
    by_contra hq3
    have hqprime : q.Prime := (D.sig_prime q hq).1
    have hq2 : q ≠ 2 := (D.sig_prime q hq).2
    have hrank : 2 ≤ CFSG.Open.pRank q (Mbar D.M V₀ V hV) :=
      S17.two_le_pRank_mbar_of_mem_sig h16.hyp125 hx h61 h127 hcard4 hq
    have hnotsq : ¬ q ^ 2 ∣ Nat.card ↥(Mbar D.M V₀ V hV) := by
      intro hdvd
      have hsq : q ^ 2 ∣ 362880 := hdvd.trans hcard
      have hfac : 362880 = 2 ^ 7 * 3 ^ 4 * 5 * 7 := by norm_num
      rw [hfac] at hsq
      have hqdvd : q ∣ 2 ^ 7 * 3 ^ 4 * 5 * 7 :=
        (show q ∣ q ^ 2 from ⟨q, by ring⟩).trans hsq
      have hcases : q = 2 ∨ q = 3 ∨ q = 5 ∨ q = 7 := by
        rcases (Nat.Prime.dvd_mul hqprime).1 hqdvd with h | h
        · rcases (Nat.Prime.dvd_mul hqprime).1 h with h | h
          · rcases (Nat.Prime.dvd_mul hqprime).1 h with h | h
            · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hqprime Nat.prime_two).1
                (hqprime.dvd_of_dvd_pow h))
            · exact Or.inr (Or.inl ((Nat.prime_dvd_prime_iff_eq hqprime Nat.prime_three).1
                (hqprime.dvd_of_dvd_pow h)))
          · exact Or.inr (Or.inr (Or.inl ((Nat.prime_dvd_prime_iff_eq hqprime
              (by norm_num : Nat.Prime 5)).1 h)))
        · exact Or.inr (Or.inr (Or.inr ((Nat.prime_dvd_prime_iff_eq hqprime
            (by norm_num : Nat.Prime 7)).1 h)))
      rcases hcases with rfl | rfl | rfl | rfl
      · exact hq2 rfl
      · exact hq3 rfl
      · norm_num at hsq
      · norm_num at hsq
    have hle : CFSG.Open.pRank q (Mbar D.M V₀ V hV) ≤ 1 :=
      CFSG.LocalAnalysis.RankThreeUC.S15.pRank_le_one_of_not_sq_dvd hqprime hnotsq
    omega
  refine Set.eq_singleton_iff_unique_mem.2 ⟨?_, hmem⟩
  obtain ⟨q, hq⟩ := hx.sig_nonempty
  rw [hmem q hq] at hq
  exact hq

theorem mbar_normal_index_ne_three_of_card_dvd_362880
    (D : Data G) (hx : DataExt D) (h61 : UC6.R6_1 D) (h127 : R127 D)
    (h638 : UC6.R6_38 D)
    {V₀ V : Subgroup G} (h16 : Hyp16 D V₀ V) (hV : IsElemAbelian 2 V)
    (hcard : Nat.card ↥(Mbar D.M V₀ V hV) ∣ 362880)
    (N : Subgroup ↥(Mbar D.M V₀ V hV)) [N.Normal] :
    N.index ≠ 3 := by
  have hsig : D.sig = {3} :=
    sig_eq_three_of_mbar_card_dvd_362880 D hx h61 h127 h16 hV hcard
  have h3 : 3 ∈ D.sig := by
    rw [hsig]
    exact Set.mem_singleton 3
  exact s16e_mbar_index_ne_three D h638 h3 h16 hV N

theorem mbar_card_dvd_362880
    (D : Data G) {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (hc : Conc4_136 D V₀ V hV L)
    (hs : s15 D.M V₀ V hV L = 1)
    (hcyc : IsCyclicOrd ↥(lBar V₀ V hV L) 3)
    (hrk : rk ↥(wTil V₀ V hV L) = 6) :
    Nat.card ↥(Mbar D.M V₀ V hV) ∣ 362880 := by
  obtain ⟨z, e, ρ, -, -, -, -, hρinj, -, -⟩ :=
    exists_cyclic_three_rank_six_s1_coordinate_action D hc hs hcyc hrk
  calc Nat.card ↥(Mbar D.M V₀ V hV)
      = Nat.card ρ.range := Nat.card_congr (MonoidHom.ofInjective hρinj).toEquiv
    _ ∣ Nat.card (coordinateSemilinearGroup 3 OmegaField) := by
        simpa using Subgroup.card_dvd_of_le (le_top : ρ.range ≤ ⊤)
    _ = 362880 := CFSG.LinearAlgebra.natCard_coordinateSemilinearGroup_three_OmegaField

theorem cyclic_three_rank_six_s1_sigma_and_pRank
    (D : Data G) (hx : DataExt D) (h61 : UC6.R6_1 D) (h127 : R127 D)
    {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (h16 : Hyp16 D V₀ V)
    (hc : Conc4_136 D V₀ V hV L)
    (hs : s15 D.M V₀ V hV L = 1)
    (hcyc : IsCyclicOrd ↥(lBar V₀ V hV L) 3)
    (hrk : rk ↥(wTil V₀ V hV L) = 6) :
    D.sig = {3} ∧ 2 ≤ CFSG.Open.pRank 3 (Mbar D.M V₀ V hV) ∧
      ∀ (J : Subgroup ↥(Mbar D.M V₀ V hV)) [J.Normal], J.index = 2 →
        2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup ↥J) := by
  have hcard : Nat.card ↥(Mbar D.M V₀ V hV) ∣ 362880 :=
    mbar_card_dvd_362880 D hc hs hcyc hrk
  have hsig : D.sig = {3} :=
    sig_eq_three_of_mbar_card_dvd_362880 D hx h61 h127 h16 hV hcard
  have h3 : 3 ∈ D.sig := by
    rw [hsig]
    exact Set.mem_singleton 3
  have hrank : 2 ≤ CFSG.Open.pRank 3 (Mbar D.M V₀ V hV) :=
    S17.two_le_pRank_mbar_of_mem_sig h16.hyp125 hx h61 h127
      (c23_card_v0_le_four D h16) h3
  refine ⟨hsig, hrank, ?_⟩
  intro J _ hJ
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hidx := CFSG.LocalAnalysis.RankThreeUC.S15.RankChevProof.pRank_top_eq_of_index_two
    (r := 3) (by norm_num) J hJ
  have htop := (CFSG.SectionRank.pRank_eq_pRank_top_subgroup (p := 3)
    (Mbar D.M V₀ V hV)).symm
  rw [hidx, htop]
  exact hrank

theorem cyclic_three_rank_six_s1_no_index_three
    (D : Data G) (hx : DataExt D) (h61 : UC6.R6_1 D) (h127 : R127 D)
    (h638 : UC6.R6_38 D)
    {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (h16 : Hyp16 D V₀ V)
    (hc : Conc4_136 D V₀ V hV L)
    (hs : s15 D.M V₀ V hV L = 1)
    (hcyc : IsCyclicOrd ↥(lBar V₀ V hV L) 3)
    (hrk : rk ↥(wTil V₀ V hV L) = 6)
    (N : Subgroup ↥(Mbar D.M V₀ V hV)) [N.Normal] :
    N.index ≠ 3 :=
  mbar_normal_index_ne_three_of_card_dvd_362880 D hx h61 h127 h638 h16 hV
    (mbar_card_dvd_362880 D hc hs hcyc hrk) N

end CFSG.LocalAnalysis.UniquenessCase.PartTwo

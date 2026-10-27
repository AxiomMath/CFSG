module

public import CFSG.LocalAnalysis.UniquenessCase.UCFront09Shape92A5
import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55BTL2Bor
import CFSG.GroupTheory.CommuteOfSqEqOne
import CFSG.HardMathSupport.Timmesfeld.LinearRank.ProjRank
import CFSG.LocalAnalysis.EvenBN.GMSK.U3Perfect
import CFSG.LocalAnalysis.UniquenessCase.UC22Bar2A5
import CFSG.Quasithin.Vol2.F134J1
import CFSG.Quasithin.Vol2.KGFactInspE16Base
import CFSG.Quasithin.EmptyFaithful.S1422Basic

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.F09

open CFSG.Open Subgroup
open CFSG.Blueprint (LieModel)

theorem not_five_dvd_card_of_lieModel_psl3_two {L : Type} [Group L] {f : ℕ}
    (hq : 2 ^ f % 3 = 2) (h : LieModel L .PSL 3 2 f) : ¬ 5 ∣ Nat.card L := by
  have hf : Odd f := by
    rcases Nat.even_or_odd f with ⟨k, rfl⟩ | hf
    · rw [← two_mul, pow_mul, Nat.pow_mod] at hq
      norm_num at hq
    · exact hf
  exact CFSG.Quasithin.H13.KGInsp4316.not_five_dvd_card_psl3_of_odd hf
    (h.statedClassicalModel_of_ne_zero (by norm_num))

theorem not_isAlt_five_of_perfect_eq_bot {S : Type} [Group S] [Finite S] {N K : Subgroup S}
    (hKN : K ≤ N) (hN : ∀ P : Subgroup S, ⁅P, P⁆ = P → P ≤ N → P = ⊥) :
    ¬ IsAlt (Bar2 K) 5 := by
  intro hA5
  obtain ⟨P, hPK, hPP, -, -, hA5P, -⟩ := exists_perfect_core_of_isAlt_five hA5
  have h60 := card_eq_sixty_mul_of_isAlt_five hA5P
  have h1 : Nat.card P = 1 := by
    rw [hN P hPP (hPK.trans hKN)]
    exact Subgroup.card_bot
  omega

theorem kFactShape92NoFaithfulA5_holds : KFactShape92NoFaithfulA5 := by
  intro S _ _ hS Q K _ hQ2 hKQ hA5 hC
  have hcomm : IsMulCommutative Q := ⟨⟨fun a b => Subtype.ext
    (CFSG.commute_of_sq_eq_one (hQ2 a a.2) (hQ2 b b.2) (hQ2 _ (Q.mul_mem a.2 b.2)))⟩⟩
  have hE : IsElemAbelian 2 Q := ⟨hcomm, hQ2⟩
  haveI : CFSG.IsElementaryAbelian 2 Q :=
    { toIsMulCommutative := hcomm
      exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one fun a =>
        Subtype.ext (hQ2 a a.2) }
  have hQp : IsPGroup 2 Q := CFSG.IsElementaryAbelian.isPGroup 2 Q
  have h16 : 16 ≤ Nat.card Q := sixteen_le_card_of_isAlt_five hQp hKQ hA5 hC
  have hQ1 : Q ≠ ⊥ := fun h => by
    rw [h, Subgroup.card_bot] at h16
    omega
  have hrank : ¬ CFSG.Open.pRank 2 (⊤ : Subgroup S) ≤ 2 := fun h => by
    have h4 : Nat.card Q ≤ 4 :=
      (CFSG.HardMathSupport.Timmesfeld.LinearRank.card_le_of_pRank_le Nat.prime_two h Q
        hE).trans_eq (by norm_num)
    omega
  rcases hS with ⟨-, h3⟩ | hJ1 | ⟨p, f, hL⟩ | ⟨p, f, hq, hL⟩ | ⟨p, f, -, hL⟩
  ·
    haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    exact hQ1 (disjoint_self.mp
      (IsPGroup.disjoint_of_ne 2 3 (by norm_num) Q Q hQp (h3.to_subgroup Q)))
  ·
    obtain ⟨e⟩ : Nonempty (S ≃* CFSG.Blueprint.NativeSporadic.Carrier .J1) := hJ1
    have hS : Nat.card S = 175560 :=
      (Nat.card_congr e.toEquiv).trans CFSG.Quasithin.F134.card_carrier_J1
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hQp
    have hdvd : 2 ^ k ∣ 175560 := by
      rw [← hk, ← hS]
      exact Subgroup.card_subgroup_dvd_card Q
    have hk3 : k ≤ 3 := by
      by_contra! h
      have h4 : 4 ≤ k := h
      exact absurd ((Nat.pow_dvd_pow 2 h4).trans hdvd) (by norm_num)
    have h8 : 2 ^ k ≤ 8 := Nat.pow_le_pow_right (by norm_num) hk3
    omega
  ·
    rcases eq_or_ne p 2 with rfl | hp2
    · exact not_isAlt_five_of_perfect_eq_bot hKQ (fun P hPP hPN =>
        CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.BT.L2V.perfect_eq_bot_of_le_normalizer
          Nat.prime_two hL hQ1 hQp hPP hPN) hA5
    · obtain ⟨⟨hp, -, -⟩, F, _, _, hF, ⟨e⟩⟩ := hL.statedClassicalModel_of_ne_zero (by norm_num)
      have hodd : Odd (Nat.card F) := by
        rw [hF]
        exact (hp.odd_of_ne_two hp2).pow
      have h4 := CFSG.ComponentClassification.UnbalancingLocal.card_le_four_of_odd_psl_two
        hodd e Q
      omega
  ·
    rcases eq_or_ne p 2 with rfl | hp2
    · exact not_five_dvd_card_of_lieModel_psl3_two hq hL ((show 5 ∣ 60 by norm_num).trans
        ((sixty_dvd_card_of_isAlt_five hA5).trans (Subgroup.card_subgroup_dvd_card K)))
    · have hm := hL.statedClassicalModel_of_ne_zero (by norm_num)
      exact hrank (CFSG.Quasithin.H13.KGInsp4316.pRank_two_le_two_of_psl3_odd
        hL.admissible.1 hp2 hm)
  ·
    rcases eq_or_ne p 2 with rfl | hp2
    · exact not_isAlt_five_of_perfect_eq_bot hKQ (fun P hPP hPN =>
        CFSG.LocalAnalysis.EvenBN.GMSK.eq_bot_of_isPerfect_of_le_normalizer_of_lieModel_PSU3
          hL hQp hQ1 (Subgroup.isPerfect_iff.mpr hPP) hPN) hA5
    · have hm := hL.statedClassicalModel_of_ne_zero (by norm_num)
      exact hrank (CFSG.Quasithin.H13.KGInsp4316.pRank_two_le_two_of_psu3_odd
        hL.admissible.1 hp2 hm)

end CFSG.LocalAnalysis.UniquenessCase.UC22.F09

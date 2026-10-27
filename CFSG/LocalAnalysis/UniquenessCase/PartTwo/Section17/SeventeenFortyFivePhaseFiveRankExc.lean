module

import CFSG.RankThree.PartOne.KLC.EigE6
import CFSG.RankThree.PartOne.KLC.EigE7
import CFSG.RankThree.PartOne.KLC.EigE8
import CFSG.RankThree.PartOne.KLC.EigF4
import CFSG.RankThree.PartOne.KLC.EigTwE6
import CFSG.LieType.Chevalley.G2TorusRank
import CFSG.LieType.SeitzGeneration.InnerOrthogonal
import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongOFRCTriPhi1
import CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.FamExceptional
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Blueprint.Chevalley
public import CFSG.LocalAnalysis.SectionRank.PRank
public import CFSG.LocalAnalysis.SectionRank.SQT
import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKD291OuterLieDefs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17.SzFive

open CFSG.TauCetiBridge (chevalleyBridges untwistedModel_of_bridge twistedModel_of_bridge)

open CFSG.Blueprint.Chevalley (TwistTag)

open CFSG.RankThree.Chevalley (exhaustionPhi exists_mulEquiv_adjointGroup_of_untwisted
  exists_mulEquiv_graphFixedRootGroup_of_twisted_prime)

open CFSG.RankThree.PartOne.KLC
open CFSG.SectionRank (pRank_top_eq_of_mulEquiv pRank_eq_open_pRank_top)

open CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross (five_dvd_cases)

open CFSG.LieType.SeitzGeneration (not_dvd_pow_of_ne)

open CFSG.LieType.Chevalley (two_le_pRank_G2_of_dvd)

open CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KD291OL (two_le_pRank_triality_phi1_general)


private theorem five_dvd_thirtyOne_pow_sub_one_int (f : ℕ) :
    (5 : ℤ) ∣ ((31 ^ f : ℕ) : ℤ) - 1 := by
  push_cast
  exact (show (5 : ℤ) ∣ 31 - 1 by norm_num).trans (by simpa using sub_dvd_pow_sub_pow (31 : ℤ) 1 f)

private theorem five_dvd_exhaustionPhi_one_two_four {n : ℕ} (hn : 1 ≤ n) (h5 : ¬ 5 ∣ n) :
    (5 : ℤ) ∣ (exhaustionPhi 1).eval (n : ℤ) ∨
      (5 : ℤ) ∣ (exhaustionPhi 2).eval (n : ℤ) ∨
        (5 : ℤ) ∣ (exhaustionPhi 4).eval (n : ℤ) := by
  rcases five_dvd_cases hn h5 with h | h | h
  · left
    have h' : (5 : ℤ) ∣ ((n - 1 : ℕ) : ℤ) := Int.natCast_dvd_natCast.mpr h
    have hcast : ((n - 1 : ℕ) : ℤ) = (n : ℤ) - 1 := by rw [Nat.cast_sub hn, Nat.cast_one]
    rw [hcast] at h'
    simpa [exhaustionPhi] using h'
  · right; left
    have h' : (5 : ℤ) ∣ ((n + 1 : ℕ) : ℤ) := Int.natCast_dvd_natCast.mpr h
    have hcast : ((n + 1 : ℕ) : ℤ) = (n : ℤ) + 1 := by rw [Nat.cast_add, Nat.cast_one]
    rw [hcast] at h'
    simpa [exhaustionPhi] using h'
  · right; right
    have h' : (5 : ℤ) ∣ ((n ^ 2 + 1 : ℕ) : ℤ) := Int.natCast_dvd_natCast.mpr h
    have h'' : ((n ^ 2 + 1 : ℕ) : ℤ) = (n : ℤ) ^ 2 + 1 := by push_cast; ring
    rw [h''] at h'
    simpa [exhaustionPhi] using h'


variable {K : Type} [Group K] [Finite K]

theorem two_le_pRank_five_E6 (q : TauCeti.PrimePower) (hv : (TauCeti.LieTypeIndex.E6 q).Valid)
    (e : K ≃* (TauCeti.CFSGIndex.lie ⟨.E6 q, hv⟩).Group) (hq2 : q.p ≠ 2) (hq5 : q.p ≠ 5) :
    2 ≤ CFSG.Open.pRank 5 (⊤ : Subgroup K) := by
  obtain ⟨F, _, _, hFcard, ⟨eF⟩⟩ := exists_mulEquiv_adjointGroup_of_untwisted
    (untwistedModel_of_bridge chevalleyBridges.e6 q hv hq2 e)
  have h5q : ¬ 5 ∣ q.p ^ q.exponent := not_dvd_pow_of_ne Nat.prime_five q.prime_p hq5.symm
  have hpK1 : 1 ≤ Nat.card F := by
    rw [hFcard]; exact Nat.one_le_pow _ _ q.prime_p.pos
  have hpK : ¬ 5 ∣ Nat.card F := by rw [hFcard]; exact h5q
  rw [← pRank_top_eq_of_mulEquiv (p := 5) (by norm_num : 1 < 5) eF, ← pRank_eq_open_pRank_top]
  rcases five_dvd_exhaustionPhi_one_two_four hpK1 hpK with h | h | h <;>
    exact two_le_pRank_E6_of_sector Nat.prime_five (by norm_num) hpK (by norm_num) h

theorem two_le_pRank_five_E7 (q : TauCeti.PrimePower) (hv : (TauCeti.LieTypeIndex.E7 q).Valid)
    (e : K ≃* (TauCeti.CFSGIndex.lie ⟨.E7 q, hv⟩).Group) (hq2 : q.p ≠ 2) (hq5 : q.p ≠ 5) :
    2 ≤ CFSG.Open.pRank 5 (⊤ : Subgroup K) := by
  obtain ⟨F, _, _, hFcard, ⟨eF⟩⟩ := exists_mulEquiv_adjointGroup_of_untwisted
    (untwistedModel_of_bridge chevalleyBridges.e7 q hv hq2 e)
  have h5q : ¬ 5 ∣ q.p ^ q.exponent := not_dvd_pow_of_ne Nat.prime_five q.prime_p hq5.symm
  have hpK1 : 1 ≤ Nat.card F := by
    rw [hFcard]; exact Nat.one_le_pow _ _ q.prime_p.pos
  have hpK : ¬ 5 ∣ Nat.card F := by rw [hFcard]; exact h5q
  rw [← pRank_top_eq_of_mulEquiv (p := 5) (by norm_num : 1 < 5) eF, ← pRank_eq_open_pRank_top]
  rcases five_dvd_exhaustionPhi_one_two_four hpK1 hpK with h | h | h <;>
    exact two_le_pRank_E7_of_sector Nat.prime_five (by norm_num) hpK (by norm_num) h

theorem two_le_pRank_five_E8 (q : TauCeti.PrimePower) (hv : (TauCeti.LieTypeIndex.E8 q).Valid)
    (e : K ≃* (TauCeti.CFSGIndex.lie ⟨.E8 q, hv⟩).Group) (hq2 : q.p ≠ 2) (hq5 : q.p ≠ 5) :
    2 ≤ CFSG.Open.pRank 5 (⊤ : Subgroup K) := by
  obtain ⟨F, _, _, hFcard, ⟨eF⟩⟩ := exists_mulEquiv_adjointGroup_of_untwisted
    (untwistedModel_of_bridge chevalleyBridges.e8 q hv hq2 e)
  have h5q : ¬ 5 ∣ q.p ^ q.exponent := not_dvd_pow_of_ne Nat.prime_five q.prime_p hq5.symm
  have hpK1 : 1 ≤ Nat.card F := by
    rw [hFcard]; exact Nat.one_le_pow _ _ q.prime_p.pos
  have hpK : ¬ 5 ∣ Nat.card F := by rw [hFcard]; exact h5q
  rw [← pRank_top_eq_of_mulEquiv (p := 5) (by norm_num : 1 < 5) eF, ← pRank_eq_open_pRank_top]
  rcases five_dvd_exhaustionPhi_one_two_four hpK1 hpK with h | h | h <;>
    exact two_le_pRank_E8_of_sector Nat.prime_five (by norm_num) hpK (by norm_num) h

theorem two_le_pRank_five_twistedE6 (q : TauCeti.PrimePower)
    (hv : (TauCeti.LieTypeIndex.twistedE6 q).Valid)
    (e : K ≃* (TauCeti.CFSGIndex.lie ⟨.twistedE6 q, hv⟩).Group) (hq2 : q.p ≠ 2) (hq5 : q.p ≠ 5) :
    2 ≤ CFSG.Open.pRank 5 (⊤ : Subgroup K) := by
  obtain ⟨F, _, _, σ, hFcard, hσ, ⟨eF⟩⟩ :=
    exists_mulEquiv_graphFixedRootGroup_of_twisted_prime q.prime_p q.exponent_pos
      (twistedModel_of_bridge chevalleyBridges.twistedE6 q hv hq2 (by decide) e)
  have hq1 : 1 ≤ q.p ^ q.exponent := Nat.one_le_pow _ _ q.prime_p.pos
  have h5q : ¬ 5 ∣ q.p ^ q.exponent := not_dvd_pow_of_ne Nat.prime_five q.prime_p hq5.symm
  have hFcard2 : Nat.card F = (q.p ^ q.exponent) ^ 2 := by
    rw [hFcard, show TwistTag.E6.order = 2 from rfl]
  have hbij : Function.Bijective σ := ⟨σ.injective, Finite.surjective_of_injective σ.injective⟩
  rw [← pRank_top_eq_of_mulEquiv (p := 5) (by norm_num : 1 < 5) eF, ← pRank_eq_open_pRank_top]
  rcases five_dvd_exhaustionPhi_one_two_four hq1 h5q with h | h | h <;>
    exact two_le_pRank_twistedE6_of_sector q.prime_p q.exponent_pos F hFcard2
      (RingEquiv.ofBijective σ hbij) hσ Nat.prime_five (by norm_num) hq5.symm (by norm_num) h

theorem two_le_pRank_five_G2 (q : TauCeti.PrimePower) (hv : (TauCeti.LieTypeIndex.G2 q).Valid)
    (e : K ≃* (TauCeti.CFSGIndex.lie ⟨.G2 q, hv⟩).Group) (h31 : q.p = 31) :
    2 ≤ CFSG.Open.pRank 5 (⊤ : Subgroup K) := by
  obtain ⟨F, _, _, hFcard, ⟨eF⟩⟩ := exists_mulEquiv_adjointGroup_of_untwisted
    (untwistedModel_of_bridge chevalleyBridges.g2 q hv (by rw [h31]; norm_num) e)
  have hdvd : 5 ∣ Nat.card F - 1 := hFcard ▸ h31 ▸
    (show 5 ∣ 31 - 1 by norm_num).trans (by simpa using Nat.sub_dvd_pow_sub_pow 31 1 q.exponent)
  rw [← pRank_top_eq_of_mulEquiv (p := 5) (by norm_num : 1 < 5) eF]
  exact two_le_pRank_G2_of_dvd Nat.prime_five hdvd

theorem two_le_pRank_five_F4 (q : TauCeti.PrimePower) (hv : (TauCeti.LieTypeIndex.F4 q).Valid)
    (e : K ≃* (TauCeti.CFSGIndex.lie ⟨.F4 q, hv⟩).Group) (h31 : q.p = 31) :
    2 ≤ CFSG.Open.pRank 5 (⊤ : Subgroup K) := by
  obtain ⟨F, _, _, hFcard, ⟨eF⟩⟩ := exists_mulEquiv_adjointGroup_of_untwisted
    (untwistedModel_of_bridge chevalleyBridges.f4 q hv (by rw [h31]; norm_num) e)
  have h5q : ¬ 5 ∣ q.p ^ q.exponent :=
    not_dvd_pow_of_ne Nat.prime_five q.prime_p (by rw [h31]; norm_num)
  have hpK : ¬ 5 ∣ Nat.card F := by rw [hFcard]; exact h5q
  have hphi : (5 : ℤ) ∣ (exhaustionPhi 1).eval (Nat.card F : ℤ) := by
    rw [hFcard, h31]
    simpa [exhaustionPhi] using five_dvd_thirtyOne_pow_sub_one_int q.exponent
  rw [← pRank_top_eq_of_mulEquiv (p := 5) (by norm_num : 1 < 5) eF, ← pRank_eq_open_pRank_top]
  exact two_le_pRank_F4_of_sector Nat.prime_five (by norm_num) hpK (e := 1) (by norm_num) hphi

theorem two_le_pRank_five_trialityD4 (q : TauCeti.PrimePower)
    (hv : (TauCeti.LieTypeIndex.trialityD4 q).Valid)
    (e : K ≃* (TauCeti.CFSGIndex.lie ⟨.trialityD4 q, hv⟩).Group) (h31 : q.p = 31) :
    2 ≤ CFSG.Open.pRank 5 (⊤ : Subgroup K) := by
  have : Fact q.p.Prime := ⟨q.prime_p⟩
  obtain ⟨F, _, _, σ, hFcard, hσ, ⟨eF⟩⟩ :=
    exists_mulEquiv_graphFixedRootGroup_of_twisted_prime q.prime_p q.exponent_pos
      (twistedModel_of_bridge chevalleyBridges.trialityD4 q hv (by rw [h31]; norm_num)
        (by decide) e)
  have hFcard3 : Nat.card F = (q.p ^ q.exponent) ^ 3 := by
    rw [hFcard, show TwistTag.D4.order = 3 from rfl]
  have hbij : Function.Bijective σ := ⟨σ.injective, Finite.surjective_of_injective σ.injective⟩
  have hres := two_le_pRank_triality_phi1_general (ℓ := q.p) (f := q.exponent) q.exponent_pos
    (K := F) hFcard3 (RingEquiv.ofBijective σ hbij) hσ Nat.prime_five (by norm_num)
    (by rw [h31]; exact five_dvd_thirtyOne_pow_sub_one_int q.exponent)
  rw [← pRank_top_eq_of_mulEquiv (p := 5) (by norm_num : 1 < 5) eF, ← pRank_eq_open_pRank_top]
  exact hres

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17.SzFive

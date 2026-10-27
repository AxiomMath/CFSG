module

import CFSG.Adapters.StatedClassicalRankFormula
import CFSG.Adapters.TauCetiLieModels
import CFSG.Adapters.LieModelTorusRank
import CFSG.Models.Blueprint
import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.I1434Exc
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Blueprint.Catalog

public section


attribute [-instance] CFSG.RankThree.Native.fact_prime_five
namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17.SzFive

open CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.I1434Exc (orderOf_five_cases
  not_five_dvd_pow)

variable {K : Type} [Group K] [Finite K]

private lemma orderOf_five_pow_cases {q : TauCeti.PrimePower} (hq5 : q.p ≠ 5) :
    orderOf ((q.p ^ q.exponent : ℕ) : ZMod 5) = 1 ∨
      orderOf ((q.p ^ q.exponent : ℕ) : ZMod 5) = 2 ∨
      orderOf ((q.p ^ q.exponent : ℕ) : ZMod 5) = 4 :=
  orderOf_five_cases (not_five_dvd_pow q.prime_p hq5)

private lemma natCast_thirtyOne_pow (f : ℕ) : ((31 ^ f : ℕ) : ZMod 5) = 1 := by
  have h : ((31 ^ f : ℕ) : ZMod 5) = ((1 : ℕ) : ZMod 5) :=
    (ZMod.natCast_eq_natCast_iff' (31 ^ f) 1 5).2 (by rw [Nat.pow_mod]; norm_num)
  simpa using h

private lemma five_le_of_orderOf_ne_one {r : ℕ} {q : TauCeti.PrimePower}
    (h : 5 ≤ r ∨ q.p = 31) (hne : orderOf ((q.p ^ q.exponent : ℕ) : ZMod 5) ≠ 1) : 5 ≤ r := by
  rcases h with h5 | h31
  · exact h5
  · exact absurd (by rw [h31, natCast_thirtyOne_pow, orderOf_one]) hne

private lemma two_le_div_odd (r o : ℕ) (hr : 2 ≤ r) (ho : o = 1 ∨ o = 2 ∨ o = 4)
    (h51 : o ≠ 1 → 5 ≤ r) : 2 ≤ (if Even o then 2 * r else r) / o := by
  rcases ho with rfl | rfl | rfl
  · simp
    omega
  · simp
    omega
  · have h5 := h51 (by norm_num)
    rw [if_pos (by norm_num : Even 4)]
    omega

private lemma two_le_div_minus (r o : ℕ) (hr : 4 ≤ r) (ho : o = 1 ∨ o = 2 ∨ o = 4)
    (h51 : o ≠ 1 → 5 ≤ r) : 2 ≤ (if Even o then 2 * (r - 1) else r - 1) / o := by
  rcases ho with rfl | rfl | rfl
  · simp
    omega
  · simp
    omega
  · have h5 := h51 (by norm_num)
    rw [if_pos (by norm_num : Even 4)]
    omega

theorem two_le_pRank_five_A (r : ℕ) (q : TauCeti.PrimePower)
    (hv : (TauCeti.LieTypeIndex.A r q).Valid)
    (e : K ≃* (TauCeti.CFSGIndex.lie ⟨.A r q, hv⟩).Group) (h31 : q.p = 31) (hr : r ≠ 1) :
    2 ≤ CFSG.Open.pRank 5 (⊤ : Subgroup K) := by
  have hL : CFSG.Models.LieModel K .PSL (r + 1) q.p q.exponent :=
    CFSG.Models.lieModel_A r q hv e
  have hr2 : 2 ≤ r := by
    have := hL.admissible.2.2.1
    omega
  have hdvd : 5 ∣ q.p ^ q.exponent - 1 := h31 ▸
    (show 5 ∣ 31 - 1 by norm_num).trans (by simpa using Nat.sub_dvd_pow_sub_pow 31 1 q.exponent)
  refine CFSG.Blueprint.LieModel.le_pRank_psl_of_dvd
    (CFSG.Models.LieModel.toBlueprint (by simp [CFSG.Blueprint.classicalTags]) hL)
    (m := 2) (r := 5)
    (by norm_num) hdvd (by omega) ?_
  rcases Nat.lt_or_ge 2 r with h3 | h3
  · exact Or.inl (by omega)
  · exact Or.inr (by rw [show r = 2 by omega]; norm_num)

theorem two_le_pRank_five_twistedA (r : ℕ) (q : TauCeti.PrimePower)
    (hv : (TauCeti.LieTypeIndex.twistedA r q).Valid)
    (e : K ≃* (TauCeti.CFSGIndex.lie ⟨.twistedA r q, hv⟩).Group) (h31 : q.p = 31) (hr : r ≠ 2) :
    2 ≤ CFSG.Open.pRank 5 (⊤ : Subgroup K) := by
  have hL : CFSG.Models.LieModel K .PSU (r + 1) q.p q.exponent := by
    have h := CFSG.Models.lieModel_twistedA r q hv e
    rwa [show TauCeti.ValidLieTypeIndex.characteristic ⟨.twistedA r q, hv⟩ = q.p from
        TauCeti.LieTypeIndex.characteristic_twistedA r q,
      show TauCeti.ValidLieTypeIndex.fieldExponent ⟨.twistedA r q, hv⟩ = q.exponent from
        TauCeti.LieTypeIndex.fieldExponent_twistedA r q] at h
  have hr3 : 3 ≤ r := by
    have := hL.admissible.2.2.1
    omega
  have hSC : CFSG.Open.StatedClassicalModel K .PSU (r + 1) 31 q.exponent := by
    have h := hL.statedClassicalModel_of_ne_zero (by omega)
    rwa [h31] at h
  have h5 : ¬ 5 ∣ 31 ^ q.exponent + 1 := by
    intro h
    have hmod : 31 ^ q.exponent % 5 = 1 := by rw [Nat.pow_mod]; norm_num
    have h0 := Nat.mod_eq_zero_of_dvd h
    rw [Nat.add_mod, hmod] at h0
    norm_num at h0
  have hdiv : ¬ 5 ∣ Nat.gcd (r + 1) (31 ^ q.exponent + 1) := fun h =>
    h5 (h.trans (Nat.gcd_dvd_right _ _))
  have hneg : orderOf (-((31 ^ q.exponent : ℕ) : ZMod 5)) = 2 := by
    have : Nontrivial (ZMod 5) := ZMod.nontrivial_iff.mpr (by norm_num)
    rw [natCast_thirtyOne_pow, orderOf_neg_one, ZMod.ringChar_zmod_n]
    norm_num
  rw [CFSG.Open.StatedClassicalModel.pRank_psu_eq (X := K) (n := r + 1) (p := 31)
    (f := q.exponent) (r := 5) hSC (by norm_num) (by norm_num) (by norm_num) hdiv,
    if_neg h5, hneg]
  omega

theorem two_le_pRank_five_B (r : ℕ) (q : TauCeti.PrimePower)
    (hv : (TauCeti.LieTypeIndex.B r q).Valid)
    (e : K ≃* (TauCeti.CFSGIndex.lie ⟨.B r q, hv⟩).Group) (hq5 : q.p ≠ 5)
    (h : 5 ≤ r ∨ q.p = 31) :
    2 ≤ CFSG.Open.pRank 5 (⊤ : Subgroup K) := by
  have hcases := orderOf_five_pow_cases (q := q) hq5
  have h51 := five_le_of_orderOf_ne_one (q := q) h
  rcases CFSG.Models.lieModel_B r q hv e with hL | hL
  · have hr2 : 2 ≤ r := by
      have := hL.admissible.2.2.1
      omega
    have hm : CFSG.Open.StatedClassicalModel K .PSp r q.p q.exponent :=
      hL.statedClassicalModel_of_ne_zero (by omega)
    rw [CFSG.Open.StatedClassicalModel.pRank_psp_eq (X := K) (n := r) (p := q.p)
      (f := q.exponent) (r := 5) hm (by norm_num) (by norm_num) (Ne.symm hq5)]
    exact two_le_div_odd r _ hr2 hcases h51
  · have hr3 : 3 ≤ r := by
      have := hL.admissible.2.2.1
      omega
    have hm : CFSG.Open.StatedClassicalModel K .POmegaOdd r q.p q.exponent :=
      hL.statedClassicalModel_of_ne_zero (by omega)
    rw [CFSG.Open.StatedClassicalModel.pRank_pomegaOdd_eq (X := K) (n := r) (p := q.p)
      (f := q.exponent) (r := 5) hm (by norm_num) (by norm_num) (Ne.symm hq5)]
    exact two_le_div_odd r _ (by omega) hcases h51

theorem two_le_pRank_five_C (r : ℕ) (q : TauCeti.PrimePower)
    (hv : (TauCeti.LieTypeIndex.C r q).Valid)
    (e : K ≃* (TauCeti.CFSGIndex.lie ⟨.C r q, hv⟩).Group) (hq5 : q.p ≠ 5)
    (h : 5 ≤ r ∨ q.p = 31) :
    2 ≤ CFSG.Open.pRank 5 (⊤ : Subgroup K) := by
  have hcases := orderOf_five_pow_cases (q := q) hq5
  have h51 := five_le_of_orderOf_ne_one (q := q) h
  have hL : CFSG.Models.LieModel K .PSp r q.p q.exponent :=
    CFSG.Models.lieModel_C r q hv e
  have hr2 : 2 ≤ r := by
    have := hL.admissible.2.2.1
    omega
  have hm : CFSG.Open.StatedClassicalModel K .PSp r q.p q.exponent :=
    hL.statedClassicalModel_of_ne_zero (by omega)
  rw [CFSG.Open.StatedClassicalModel.pRank_psp_eq (X := K) (n := r) (p := q.p)
    (f := q.exponent) (r := 5) hm (by norm_num) (by norm_num) (Ne.symm hq5)]
  exact two_le_div_odd r _ hr2 hcases h51

theorem two_le_pRank_five_D (r : ℕ) (q : TauCeti.PrimePower)
    (hv : (TauCeti.LieTypeIndex.D r q).Valid)
    (e : K ≃* (TauCeti.CFSGIndex.lie ⟨.D r q, hv⟩).Group) (hq5 : q.p ≠ 5)
    (h : 5 ≤ r ∨ q.p = 31) :
    2 ≤ CFSG.Open.pRank 5 (⊤ : Subgroup K) := by
  have hcases := orderOf_five_pow_cases (q := q) hq5
  have h51 := five_le_of_orderOf_ne_one (q := q) h
  have hL : CFSG.Models.LieModel K .POmegaPlus r q.p q.exponent :=
    CFSG.Models.lieModel_D r q hv e
  have hr4 : 4 ≤ r := hL.admissible.2.2
  have hm : CFSG.Open.StatedClassicalModel K .POmegaPlus r q.p q.exponent :=
    hL.statedClassicalModel_of_ne_zero (by omega)
  rw [CFSG.Open.StatedClassicalModel.pRank_pomegaPlus_eq (X := K) (n := r) (p := q.p)
    (f := q.exponent) (r := 5) hm (by norm_num) (by norm_num) (Ne.symm hq5)]
  by_cases hA : ((5 : ℕ) : ℤ) ∣ ((q.p ^ q.exponent : ℕ) : ℤ) ^ r + 1
  · rw [if_pos hA]
    exact two_le_div_minus r _ hr4 hcases h51
  · rw [if_neg hA]
    exact two_le_div_odd r _ (by omega) hcases h51

theorem two_le_pRank_five_twistedD (r : ℕ) (q : TauCeti.PrimePower)
    (hv : (TauCeti.LieTypeIndex.twistedD r q).Valid)
    (e : K ≃* (TauCeti.CFSGIndex.lie ⟨.twistedD r q, hv⟩).Group) (hq5 : q.p ≠ 5)
    (h : 5 ≤ r ∨ q.p = 31) :
    2 ≤ CFSG.Open.pRank 5 (⊤ : Subgroup K) := by
  have hcases := orderOf_five_pow_cases (q := q) hq5
  have h51 := five_le_of_orderOf_ne_one (q := q) h
  have hL : CFSG.Models.LieModel K .POmegaMinus r q.p q.exponent :=
    CFSG.Models.lieModel_twistedD r q hv e
  have hr4 : 4 ≤ r := hL.admissible.2.2
  have hm : CFSG.Open.StatedClassicalModel K .POmegaMinus r q.p q.exponent :=
    hL.statedClassicalModel_of_ne_zero (by omega)
  rw [CFSG.Open.StatedClassicalModel.pRank_pomegaMinus_eq (X := K) (n := r) (p := q.p)
    (f := q.exponent) (r := 5) hm (by norm_num) (by norm_num) (Ne.symm hq5)]
  by_cases hA : ((5 : ℕ) : ℤ) ∣ ((q.p ^ q.exponent : ℕ) : ℤ) ^ r - 1
  · rw [if_pos hA]
    exact two_le_div_minus r _ hr4 hcases h51
  · rw [if_neg hA]
    exact two_le_div_odd r _ (by omega) hcases h51

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17.SzFive

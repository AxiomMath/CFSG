module

public import CFSG.RankThree.PartOne.S11c.Sec66ClassCommon
public import CFSG.RankThree.PartOne.S11c.Sec66Conj
public import CFSG.RankThree.PartOne.S11c.Sec66Torus
public import CFSG.RankThree.SteinbergR3ELinearFieldDescent
public import CFSG.RankThree.PartOne.KC.LinearPrimeSubfieldFixedGroup
public import CFSG.RankThree.PartOne.KC.LinearNonsplitSubfieldFixedGroup
public import CFSG.RankThree.PartOne.S11d.OutClassicalTwo
public import CFSG.RankThree.PartOne.S11d.OutLinear

public section

namespace CFSG.RankThree.PartOne.Sec66T

open CFSG CFSG.Blueprint
open CFSG.Assembly.LowTwoRank
  (StatedLieAdmissible StatedClassicalModel projectiveSpecialLinearGroupEquivStatedProj)
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.GroupTheory.SteinbergBK (semilinearFixedSubfield)

@[expose] def PSLTwoK1 : Prop :=
  ∀ (T : Type) [Group T] [Finite T] (p : ℕ), p.Prime → 5 ≤ p →
    (∃ f : ℕ, StatedLieAdmissible .PSL 2 2 f ∧ LieModel T .PSL 2 2 f) → LocalRankLeTwo p T →
    ∀ (α : MulAut T) (q : T) (U : Subgroup T), orderOf α = p → α ∉ innerAut T → q ≠ 1 →
      q ^ p = 1 → α q = q → U ≠ ⊥ → IsPGroup 2 ↥U → (∀ u ∈ U, α u ∈ U) →
      (∀ u ∈ U, q * u * q⁻¹ ∈ U) → (∃ u ∈ U, α u ≠ u ∨ q * u * q⁻¹ ≠ u) → FieldAutT p α

theorem sec66T_K2_PSL (hT : PSLTorusRank) : Sec66T_K2 .PSL := by
  intro T _ _ p hp hp5 hmodel hrank E hE hcard hEinn _hra
  obtain ⟨n, f, hadm, hM⟩ := hmodel
  have hC : StatedClassicalModel T .PSL n 2 f := (lieModel_classical_iff (by decide)).mp hM
  have hn : 2 ≤ n := hadm.2.2.1
  have hp2 : p ≠ 2 := by omega
  by_cases hn3 : 3 ≤ n
  · by_cases hdiag : p ∣ Nat.gcd n (2 ^ f - 1)
    · exact hT T n f p hp hp5 (hdiag.trans (Nat.gcd_dvd_left _ _))
        (hdiag.trans (Nat.gcd_dvd_right _ _)) hC hrank
    · exact no_plane_of_outPNice hp (OutStructure.outPNice_PSL_ge_three hp hp2 hn3 hC hdiag) E hE
        hcard hEinn
  · have hn2 : n = 2 := by omega
    subst hn2
    exact no_plane_of_outPNice hp (OutStructure.outPNice_PSL_two hp hC) E hE hcard hEinn

theorem sec66T_K1_PSL (h2 : PSLTwoK1) (hT : PSLTorusRank) : Sec66T_K1 .PSL := by
  intro T _ _ p hp hp5 hmodel hrank α q U hord hαinn hq1 hqp hαq hU1 hU2 hαU hqU hmv _hra
  obtain ⟨n, f, hadm, hM⟩ := hmodel
  have hC : StatedClassicalModel T .PSL n 2 f := (lieModel_classical_iff (by decide)).mp hM
  have hf : 1 ≤ f := hadm.2.1
  have hn : 2 ≤ n := hadm.2.2.1
  have hp2 : p ≠ 2 := by omega
  by_cases hn3 : 3 ≤ n
  · have hdiag : ¬ p ∣ Nat.gcd n (2 ^ f - 1) := fun hd =>
      hT T n f p hp hp5 (hd.trans (Nat.gcd_dvd_left _ _)) (hd.trans (Nat.gcd_dvd_right _ _)) hC
        hrank
    obtain ⟨-, K, _, _, hK, ⟨e0⟩⟩ := hC
    have hdiagK : ¬ p ∣ Nat.gcd n (Nat.card K - 1) := by rwa [hK]
    have : Fintype K := Fintype.ofFinite K
    have : CharP K 2 := charP_of_card_eq_prime_pow (f := f) (by rw [← Nat.card_eq_fintype_card, hK])
    let e : T ≃* projectiveSL n K :=
      (e0.trans (projectiveSpecialLinearGroupEquivStatedProj n K).symm).trans
        (LinearCover.projectiveSpecialLinearEquivProjectiveSL n K)
    have : Finite (projectiveSL n K) := Finite.of_equiv T e.toEquiv
    have hα'inn : MulAut.congr e α ∉ innerAut (projectiveSL n K) :=
      fun h => hαinn ((mem_innerAut_congr e α).mp h)
    have hα'ord : orderOf (MulAut.congr e α) = p := (orderOf_congr e α).trans hord
    have hα'p : MulAut.congr e α ^ p = 1 := by
      have := pow_orderOf_eq_one (MulAut.congr e α)
      rwa [hα'ord] at this
    obtain ⟨hgenTop, -⟩ := automorphism_generation (K := K) hn3
    obtain ⟨-, -, -, -, -, -, -, hidx, -, -⟩ := standard_outer_quotients (n := n) (K := K)
    have hE : MulAut.congr e α ∈ semilinearAutGroup n K := by
      have hidx' : (semilinearAutGroup n K).index ≤ 2 := by
        have h2' : (semilinearAutGroup n K).relIndex (standardAutGroup n K) ≤ 2 := hidx
        rwa [hgenTop, Subgroup.relIndex_top_right] at h2'
      refine OutStructure.mem_of_pow_mem_of_index_le_two _ hidx' (hp.odd_of_ne_two hp2) ?_
      rw [hα'p]
      exact Subgroup.one_mem _
    have hD : MulAut.congr e α ∉ linearAutGroup n K := by
      intro hD
      exact hα'inn (OutStructure.linear_D2 hp hn3 hdiagK _ hD 1
        (by rw [pow_one, hα'p]; exact Subgroup.one_mem _))
    obtain ⟨-, -, -, -, -, -, -, hdesc⟩ :=
      CFSG.RankThree.LinearDescent.higher_linear_prime_semilinear_field_descent Nat.prime_two hf
        hn3 hK
    obtain ⟨hpf, σ, hσord, ⟨h, -, hαh⟩, hkcard⟩ := hdesc p hp hp2 _ hE hD hα'ord
    have hfp1 : 1 ≤ f / p := (Nat.one_le_div_iff hp.pos).mpr (Nat.le_of_dvd (by omega) hpf)
    have hff' : f = p * (f / p) := (Nat.mul_div_cancel' hpf).symm
    have hfixset : {x : projectiveSL n K | fieldAut n K σ x = x} =
        ((linearSubfieldInclusion n (semilinearFixedSubfield σ)).range :
          Set (projectiveSL n K)) := by
      by_cases hpq : p ∣ 2 ^ f - 1
      · have hpn : ¬ p ∣ n := fun hpn => hdiag (Nat.dvd_gcd hpn hpq)
        have hcop : Nat.Coprime n p := ((Nat.Prime.coprime_iff_not_dvd hp).mpr hpn).symm
        exact (higher_linear_prime_subfield_fixed_group_and_full_centralizer Nat.prime_two hp hp2
          hf hn3 hcop hK σ hσord).2.1
      · exact (nonsplit_linear_prime_subfield_fixed_group_and_full_centralizer Nat.prime_two hp
          (by omega) hp2 hf hn3 hK hpq σ hσord).2.2.1
    have hinj := linearSubfieldInclusion_injective (by omega : 0 < n) (semilinearFixedSubfield σ)
    have hfixeq : fixSub (fieldAut n K σ) =
        (linearSubfieldInclusion n (semilinearFixedSubfield σ)).range := by
      ext x
      exact Set.ext_iff.mp hfixset x
    let eX : ↥(fixSub (fieldAut n K σ)) ≃* projectiveSL n ↥(semilinearFixedSubfield σ) :=
      (MulEquiv.subgroupCongr hfixeq).trans (MonoidHom.ofInjective hinj).symm
    have hs : IsSimpleGroup (projectiveSL n ↥(semilinearFixedSubfield σ)) :=
      KCLinearSubfield.isSimpleGroup_projectiveSL hn3
    have hnab : ∃ a b : projectiveSL n ↥(semilinearFixedSubfield σ), a * b ≠ b * a := by
      have h1 := KCLinearSubfield.not_commutative_projectiveSL
        (n := n) (K := ↥(semilinearFixedSubfield σ)) hn3
      push Not at h1
      exact h1
    have hXmodel : LieModel (projectiveSL n ↥(semilinearFixedSubfield σ)) .PSL n 2 (f / p) :=
      (lieModel_classical_iff (by decide)).mpr
        ⟨⟨Nat.prime_two, hfp1, hn, fun hc => by have := (Prod.mk.inj hc).1; omega,
            fun hc => by have := (Prod.mk.inj hc).1; omega⟩,
          ↥(semilinearFixedSubfield σ), inferInstance, inferInstance, hkcard,
          ⟨(LinearCover.projectiveSpecialLinearEquivProjectiveSL n
            ↥(semilinearFixedSubfield σ)).symm.trans
              (projectiveSpecialLinearGroupEquivStatedProj n ↥(semilinearFixedSubfield σ))⟩⟩
    have hfix := lieModel_fixRes_of_simple hnab eX hXmodel
    refine fieldAutT_of_conj_fix e hM hff' hfp1 α (fieldAut n K σ) h⁻¹ ?_ hfix
    rw [hαh]
    group
  · have hn2 : n = 2 := by omega
    subst hn2
    exact h2 T p hp hp5 ⟨f, hadm, hM⟩ hrank α q U hord hαinn hq1 hqp hαq hU1 hU2 hαU hqU hmv

end CFSG.RankThree.PartOne.Sec66T

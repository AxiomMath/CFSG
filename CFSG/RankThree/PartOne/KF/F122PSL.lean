module

public import CFSG.RankThree.PartOne.KF.F122Sp
public import CFSG.RankThree.PartOne.KF.F122PSLFour
public import CFSG.RankThree.PartOne.KC.LinearNonsplitSubfieldFixedGroup
public import CFSG.RankThree.PartOne.KC.LinearPrimeSubfieldFixedGroup
public import CFSG.RankThree.SteinbergR3ELinearFieldDescent

public section

namespace CFSG.RankThree.PartOne

open CFSG CFSG.Blueprint CFSG.RankThree.PartOne.Sec66T CFSG.RankThree.PartTwo.Census
open CFSG.Assembly.LowTwoRank
  (StatedLieAdmissible StatedClassicalModel projectiveSpecialLinearGroupEquivStatedProj)
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.GroupTheory.SteinbergBK (semilinearFixedSubfield)
open CFSG.Assembly.RankThreeEven (localRank)

theorem psl_aut_false {T : Type} [Group T] [Finite T] {p n f : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hC : StatedClassicalModel T .PSL n 2 f) (hn3 : 3 ≤ n)
    (hdiag : ¬ p ∣ Nat.gcd n (2 ^ f - 1))
    (hlower : ∀ (f₀ : ℕ) (k : Type) [Field k] [Finite k] [CharP k 2], f = p * f₀ →
      Nat.card k = 2 ^ f₀ → 2 ≤ localRank p (Matrix.ProjectiveSpecialLinearGroup (Fin n) k))
    {α : MulAut T} (hαp : α ^ p = 1) (hαinn : α ∉ innerAut T) (hLRA : LocalRankAut p T α) :
    False := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have hp2 : p ≠ 2 := by omega
  have hα1 : α ≠ 1 := fun h => hαinn (h ▸ Subgroup.one_mem _)
  have hord : orderOf α = p := orderOf_eq_prime hαp hα1
  have hadm := hC.1
  have hf : 1 ≤ f := hadm.2.1
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
  have hψ : h⁻¹ * MulAut.congr e α * h⁻¹⁻¹ = fieldAut n K σ := by
    rw [hαh]
    group
  have hψ' : fixSub (h⁻¹ * MulAut.congr e α * h⁻¹⁻¹) = fixSub (fieldAut n K σ) := by rw [hψ]
  let e12 : ↥(fixSub α) ≃* ↥(fixSub (fieldAut n K σ)) :=
    ((fixSubEquiv e α).trans (fixSubEquiv h⁻¹ (MulAut.congr e α))).trans
      (MulEquiv.subgroupCongr hψ')
  let eY : ↥(fixSub α) ≃* Matrix.ProjectiveSpecialLinearGroup (Fin n) ↥(semilinearFixedSubfield σ) :=
    (e12.trans eX).trans (LinearCover.projectiveSpecialLinearEquivProjectiveSL n _).symm
  have : Fintype ↥(semilinearFixedSubfield σ) := Fintype.ofFinite _
  have : CharP ↥(semilinearFixedSubfield σ) 2 :=
    charP_of_card_eq_prime_pow (f := f / p) (by rw [← Nat.card_eq_fintype_card, hkcard])
  have hN : 2 ≤ localRank p ↥(fixSub α) := by
    rw [localRank_eq_of_mulEquiv eY hp]
    exact hlower (f / p) ↥(semilinearFixedSubfield σ) hff' hkcard
  exact false_of_localRank_fixed hp hαp hαinn (fixSub α) (fun y hy => hy) hN hLRA

theorem kf122Row1_holds : KF122Row 1 := by
  intro G _ _ p L hp hp5 hmodel _ α hαp hαinn hLRA
  obtain ⟨f, -, hpq, hC⟩ := hmodel
  refine psl_aut_false (n := 3) hp hp5 hC (by norm_num) ?_ ?_ hαp hαinn hLRA
  · intro hd
    have := Nat.le_of_dvd (by norm_num) (hd.trans (Nat.gcd_dvd_left _ _))
    omega
  · intro f₀ k _ _ _ hf hk
    have hpk : p ∣ 2 ^ f₀ - 1 := dvd_two_pow_sub_one_of_mul hp (hf ▸ hpq)
    refine le_localRank_PSL_torus (K := k) (m := 2) (n := 3) hp ?_ (by norm_num) (by norm_num)
      (Or.inr fun hd => by
        have := Nat.le_of_dvd (by norm_num) hd
        omega)
    rw [Nat.card_units, hk]
    exact hpk

theorem kf122Row8_holds : KF122Row 8 := by
  intro G _ _ p L hp hp5 hmodel _ α hαp hαinn hLRA
  obtain ⟨f, -, hpq, hC⟩ := hmodel
  refine psl_aut_false (n := 4) hp hp5 hC (by norm_num) ?_ ?_ hαp hαinn hLRA
  · intro hd
    have := Nat.le_of_dvd (by norm_num) (hd.trans (Nat.gcd_dvd_left _ _))
    omega
  · intro f₀ k _ _ _ hf hk
    have hpk : p ∣ 2 ^ f₀ + 1 := dvd_two_pow_add_one_of_mul hp (hf ▸ hpq)
    refine KFU.two_le_localRank_PSL_four_fin (K := k) hp ?_
    rw [CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two, hk]
    have h1 : 1 ≤ 2 ^ f₀ := Nat.one_le_two_pow
    have hsq : (2 ^ f₀) ^ 2 - 1 = (2 ^ f₀ + 1) * (2 ^ f₀ - 1) := by
      zify [h1, Nat.one_le_pow 2 (2 ^ f₀) (by omega)]
      ring
    rw [hsq]
    exact (hpk.mul_right _).mul_left _

end CFSG.RankThree.PartOne

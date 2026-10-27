module

public import CFSG.RankThree.PartOne.CTP.SeitzLinearOuter
public import CFSG.RankThree.PartOne.S11d.OutAbstract

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Seven

open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.GroupTheory.SteinbergBK (semilinearFixedSubfield)

private theorem ksl3c_seven_dvd_card_of_seven_dvd_card {K : Type} [Field K] [Finite K]
    (h7q : 7 ∣ Nat.card K) : 7 ∣ Nat.card (projectiveSL 3 K) := by
  have hq1 : 1 < Nat.card K := Finite.one_lt_card
  have hSL := card_SL_eq (K := K) (n := 3) (by norm_num)
  have hsplit := (scalars 3 K).card_eq_card_quotient_mul_card_subgroup
  have hZ := card_scalars_dvd (K := K) (n := 3) (by norm_num)
  have hrSL : 7 ∣ Nat.card (Matrix.SpecialLinearGroup (Fin 3) K) := by
    rw [hSL]
    exact Dvd.dvd.mul_right (h7q.trans (dvd_pow_self _ (by norm_num))) _
  have hcop : Nat.Coprime 7 (Nat.card (scalars 3 K)) := by
    have h1 : Nat.Coprime 7 (Nat.card K - 1) := by
      refine (Nat.Prime.coprime_iff_not_dvd Nat.prime_seven).mpr fun hd => ?_
      have : 7 ∣ Nat.card K - (Nat.card K - 1) := Nat.dvd_sub h7q hd
      rw [Nat.sub_sub_self hq1.le] at this
      exact Nat.prime_seven.one_lt.ne' (Nat.dvd_one.mp this)
    exact Nat.Coprime.coprime_dvd_right hZ h1
  rw [hsplit] at hrSL
  exact Nat.Coprime.dvd_of_dvd_mul_right hcop hrSL

theorem exists_conj_zpowers_fieldAut_of_card_seven {K : Type} [Field K] [Finite K]
    (hq : ¬ 3 ∣ Nat.card K - 1) (h7 : ¬ 7 ∣ Nat.card (projectiveSL 3 K))
    (W : Subgroup (MulAut (projectiveSL 3 K))) (hW : Nat.card W = 7) :
    ∃ (h : MulAut (projectiveSL 3 K)) (σ : K ≃+* K), orderOf σ = 7 ∧
      Nat.card K = Nat.card (semilinearFixedSubfield σ) ^ 7 ∧
      W = (Subgroup.zpowers (fieldAut 3 K σ)).map (MulAut.conj h).toMonoidHom := by
  haveI : Fact (Nat.Prime 7) := ⟨Nat.prime_seven⟩
  have hcyc : IsCyclic ↥W := isCyclic_of_prime_card hW
  obtain ⟨g, hg⟩ := hcyc.exists_generator
  have hordg : orderOf g = 7 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hg, hW]
  set a : MulAut (projectiveSL 3 K) := (g : MulAut (projectiveSL 3 K)) with ha
  have haord : orderOf a = 7 := by
    rw [ha, Subgroup.orderOf_coe, hordg]
  have ha7 : a ^ 7 = 1 := by
    rw [← haord]
    exact pow_orderOf_eq_one a
  have hWz : W = Subgroup.zpowers a := by
    refine (Subgroup.eq_of_le_of_card_ge ?_ ?_).symm
    · rw [Subgroup.zpowers_le, ha]
      exact g.2
    · rw [hW, Nat.card_zpowers, haord]
  have haMem : a ∈ semilinearAutGroup 3 K :=
    CFSG.RankThree.PartOne.CTP.mem_semilinearAutGroup_of_pow_eq_one (n := 3) (F := K) (p := 7)
      (by norm_num) Nat.prime_seven (by norm_num) ha7
  have hgcd : Nat.gcd 3 (Nat.card K - 1) = 1 := by
    rw [← Nat.coprime_iff_gcd_eq_one]
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hq
  have hcop : Nat.Coprime 7 (Nat.gcd 3 (Nat.card K - 1)) := by
    rw [hgcd]
    exact Nat.coprime_one_right 7
  have haD : a ∉ linearAutGroup 3 K := by
    intro hD
    have hinner : a ∈ CFSG.RankThree.PartOne.innSL 3 K :=
      CFSG.RankThree.PartOne.KCLinPlane.inner_of_mem_linearAut_of_pow_eq_one
        (n := 3) (p := 7) (by norm_num) hcop hD ha7
    obtain ⟨t, ht⟩ := hinner
    have hdvd : 7 ∣ Nat.card (projectiveSL 3 K) := by
      rw [← haord, ← ht]
      exact (orderOf_map_dvd (MulAut.conj : projectiveSL 3 K →* MulAut (projectiveSL 3 K)) t)
        |>.trans (orderOf_dvd_natCard t)
    exact h7 hdvd
  letI : Fintype K := Fintype.ofFinite K
  haveI : CharP K (ringChar K) := ringChar.charP K
  obtain ⟨f, hℓ, hcardf⟩ := FiniteField.card K (ringChar K)
  have hf : 1 ≤ (f : ℕ) := f.pos
  have hK : Nat.card K = ringChar K ^ (f : ℕ) := by
    rw [Nat.card_eq_fintype_card, hcardf]
  have hne7 : (7 : ℕ) ≠ ringChar K := by
    intro h
    apply h7
    apply ksl3c_seven_dvd_card_of_seven_dvd_card
    rw [hK, ← h]
    exact dvd_pow_self 7 (by omega)
  have hdesc := CFSG.RankThree.LinearDescent.higher_linear_prime_semilinear_field_descent
    (K := K) (n := 3) (ℓ := ringChar K) (f := (f : ℕ)) hℓ hf (by norm_num) hK
  obtain ⟨h7f, σ, hσ, ⟨h, -, haeq⟩, hfix⟩ :=
    hdesc.2.2.2.2.2.2.2 7 Nat.prime_seven hne7 a haMem haD haord
  have hpow : Nat.card K = Nat.card (semilinearFixedSubfield σ) ^ 7 := by
    rw [hK, hfix, ← pow_mul, Nat.div_mul_cancel h7f]
  refine ⟨h, σ, hσ, hpow, ?_⟩
  rw [hWz, haeq, MonoidHom.map_zpowers]
  rfl

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Seven

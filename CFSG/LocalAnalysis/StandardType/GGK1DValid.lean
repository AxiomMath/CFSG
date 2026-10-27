module

public import CFSG.LocalAnalysis.StandardType.GGK1DDefs
public import CFSG.LocalAnalysis.StandardType.GGK1DWitt

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Open Polynomial
open CFSG.RankThree.PartOne.KCPrimary
open CFSG.RankThree.PartOne.KCOrthogonal (OddOrderIsometry reciprocalPolynomial fixedSpace)
open CFSG.RankThree.Classical (IsReciprocalTransversal)
open CFSG.GroupTheory.WeirSylow
section ggK1DvLift

open Matrix

private theorem ggK1Dv_charP_two {K : Type} [Field K] [Finite K] {nf : ℕ}
    (hK : Nat.card K = 2 ^ nf) : CharP K 2 := by
  haveI : Fintype K := Fintype.ofFinite K
  exact charP_of_card_eq_prime_pow (p := 2) (f := nf)
    (by rw [← Nat.card_eq_fintype_card]; exact hK)

private theorem ggK1Dv_prime_cast_ne_zero {K : Type} [Field K] [Finite K] {p nf : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hK : Nat.card K = 2 ^ nf) : (p : K) ≠ 0 := by
  haveI : CharP K 2 := ggK1Dv_charP_two hK
  intro h
  rw [CharP.cast_eq_zero_iff K 2] at h
  exact hp2 ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).mp h).symm

private lemma ggK1Dv_lin_apply {ι K : Type*} [Fintype ι] [DecidableEq ι] [Field K]
    (x : GL ι K) (v : ι → K) : ggK1DLin x v = (x : Matrix ι ι K) *ᵥ v := by
  rw [ggK1DLin, LinearMap.GeneralLinearGroup.coe_toLinearEquiv,
    Matrix.GeneralLinearGroup.coe_toLin, Matrix.coe_mulVecLin]

private lemma ggK1Dv_lin_mul {ι K : Type*} [Fintype ι] [DecidableEq ι] [Field K]
    (a b : GL ι K) : ggK1DLin (a * b) = ggK1DLin a * ggK1DLin b := by
  ext v
  rw [LinearEquiv.mul_apply, ggK1Dv_lin_apply, ggK1Dv_lin_apply, ggK1Dv_lin_apply,
    Units.val_mul, Matrix.mulVec_mulVec]

private lemma ggK1Dv_lin_pow {ι K : Type*} [Fintype ι] [DecidableEq ι] [Field K]
    (x : GL ι K) (n : ℕ) : ggK1DLin (x ^ n) = (ggK1DLin x) ^ n := by
  induction n with
  | zero => ext v; rw [pow_zero, pow_zero, ggK1Dv_lin_apply]; simp
  | succ n ih => rw [pow_succ, pow_succ, ggK1Dv_lin_mul, ih]

private theorem ggK1Dv_omegaLift_plus {p nf r : ℕ} {K : Type} [Field K] [Finite K]
    (hp : p.Prime) (hp2 : p ≠ 2) (hnf : 1 ≤ nf) (hK : Nat.card K = 2 ^ nf)
    {x : ↥(LargeEvenOmega (LargeEvenQPlus K r))} (hx : x ^ p = 1) :
    OddOrderIsometry (TableBOrth.qPlusForm K r) p
      (ggK1DLin (x : GL (Fin r ⊕ Fin r) K)) := by
  have hxp : (x : GL (Fin r ⊕ Fin r) K) ^ p = 1 := by
    simpa using congrArg (fun y : ↥(LargeEvenOmega (LargeEvenQPlus K r)) =>
      (y : GL (Fin r ⊕ Fin r) K)) hx
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [TauCeti.QuadraticMap.mem_orthogonalGroup_iff]
    intro v
    rw [ggK1Dv_lin_apply, TableBOrth.coe_qPlusForm]
    exact TableBOrth.isometry_of_mem_orthGroup (TableBOrth.omega_le_orth _ x.2) v
  · rw [← ggK1Dv_lin_pow, hxp]
    ext v; rw [ggK1Dv_lin_apply]; simp
  · exact ggK1Dv_prime_cast_ne_zero hp hp2 hK
  · intro v hv
    exact (TableBOrth.nondegenerate_qPlusForm (K := K) r).1 v (fun w => by
      rw [QuadraticMap.polarBilin_apply_apply]
      exact hv w)

private theorem ggK1Dv_omegaLift_minus {p nf r : ℕ} {K : Type} [Field K] [Finite K]
    (hp : p.Prime) (hp2 : p ≠ 2) (hnf : 1 ≤ nf) (hK : Nat.card K = 2 ^ nf) {b c : K}
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    {x : ↥(LargeEvenOmega (LargeEvenQMinus (r - 1) b c))} (hx : x ^ p = 1) :
    OddOrderIsometry (TableBOrth.qMinusForm K (r - 1) b c) p
      (ggK1DLin (x : GL (LargeEvenMinusIdx (r - 1)) K)) := by
  have hxp : (x : GL (LargeEvenMinusIdx (r - 1)) K) ^ p = 1 := by
    simpa using congrArg (fun y : ↥(LargeEvenOmega (LargeEvenQMinus (r - 1) b c)) =>
      (y : GL (LargeEvenMinusIdx (r - 1)) K)) hx
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [TauCeti.QuadraticMap.mem_orthogonalGroup_iff]
    intro v
    rw [ggK1Dv_lin_apply, TableBOrth.coe_qMinusForm]
    exact TableBOrth.isometry_of_mem_orthGroup (TableBOrth.omega_le_orth _ x.2) v
  · rw [← ggK1Dv_lin_pow, hxp]
    ext v; rw [ggK1Dv_lin_apply]; simp
  · exact ggK1Dv_prime_cast_ne_zero hp hp2 hK
  · intro v hv
    exact (TableBOrth.nondegenerate_qMinusForm (K := K) (r - 1) hirr).1 v (fun w => by
      rw [QuadraticMap.polarBilin_apply_apply]
      exact hv w)

end ggK1DvLift


private theorem ggK1Dv_primaryComponent_eq_fixedSpace {ι K : Type*} [Fintype ι]
    [DecidableEq ι] [Field K] (x : GL ι K) :
    primaryComponent (ggK1DOrthEnd x) (X - 1) = fixedSpace (ggK1DLin x) :=
  CFSG.RankThree.PartOne.KCOrthogonal.fixedSpace_eq_primaryComponent.symm

private theorem ggK1Dv_eps0_of_head_zero {p nf r : ℕ} {K : Type} [Field K] [Finite K]
    (hp : p.Prime) (hp2 : p ≠ 2) (hdvd : p ∣ 2 ^ nf - 1 ∨ p ∣ 2 ^ nf + 1)
    (hnf : 1 ≤ nf) (hK : Nat.card K = 2 ^ nf)
    {x : ↥(LargeEvenOmega (LargeEvenQPlus K r))} {m : List ℕ}
    (hm : GGK1DMultOf p nf (ggMultOrd p nf) r K (x : GL (Fin r ⊕ Fin r) K) m)
    (hx : x ^ p = 1) :
    m.headD 0 = 0 → ggMultEps0 p (ggMultOrd p nf) false m = true := by
  intro h0
  haveI : CharP K 2 := CFSG.RankThree.PartOne.charP_two_of_card_eq_pow hK
  have hxO := ggK1Dv_omegaLift_plus (K := K) hp hp2 hnf hK hx
  obtain ⟨s, hs⟩ := hxO.even_finrank_fixed
  have hdim : Module.finrank K
      (primaryComponent (ggK1DOrthEnd (x : GL (Fin r ⊕ Fin r) K)) (X - 1)) = 2 * s := by
    rw [ggK1Dv_primaryComponent_eq_fixedSpace]
    omega
  have hfin0 : Module.finrank K
      (primaryComponent (ggK1DOrthEnd (x : GL (Fin r ⊕ Fin r) K)) (X - 1)) = 0 := by
    have hhead := hm.head_eq
    omega
  have hbot : primaryComponent (ggK1DOrthEnd (x : GL (Fin r ⊕ Fin r) K)) (X - 1) = ⊥ :=
    Submodule.finrank_eq_zero.mp hfin0
  haveI : Subsingleton ↥(primaryComponent
      (ggK1DOrthEnd (x : GL (Fin r ⊕ Fin r) K)) (X - 1)) := by rw [hbot]; infer_instance
  have hP : IsPlusType
      ((TableBOrth.qPlusForm K r).restrict
        (primaryComponent (ggK1DOrthEnd (x : GL (Fin r ⊕ Fin r) K)) (X - 1))) :=
    isPlusType_of_subsingleton _
  have hw := ggK1D_v0_witt_plus (K := K) hp hp2 hdvd hnf hK hm hx
    (TableBOrth.qPlusForm K r) (TableBOrth.coe_qPlusForm (K := K) r).symm
  exact hw.mp hP

private theorem ggK1Dv_eps0_of_head_zero_minus {p nf r : ℕ} {K : Type} [Field K] [Finite K]
    (hp : p.Prime) (hp2 : p ≠ 2) (hdvd : p ∣ 2 ^ nf - 1 ∨ p ∣ 2 ^ nf + 1)
    (hnf : 1 ≤ nf) (hK : Nat.card K = 2 ^ nf) {b c : K}
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    {x : ↥(LargeEvenOmega (LargeEvenQMinus (r - 1) b c))} {m : List ℕ}
    (hm : GGK1DMultOf p nf (ggMultOrd p nf) r K
      (x : GL (LargeEvenMinusIdx (r - 1)) K) m)
    (hx : x ^ p = 1) :
    m.headD 0 = 0 → ggMultEps0 p (ggMultOrd p nf) true m = true := by
  intro h0
  haveI : CharP K 2 := CFSG.RankThree.PartOne.charP_two_of_card_eq_pow hK
  have hxO := ggK1Dv_omegaLift_minus (K := K) hp hp2 hnf hK hirr hx
  obtain ⟨s, hs⟩ := hxO.even_finrank_fixed
  have hdim : Module.finrank K
      (primaryComponent (ggK1DOrthEnd (x : GL (LargeEvenMinusIdx (r - 1)) K)) (X - 1)) =
        2 * s := by
    rw [ggK1Dv_primaryComponent_eq_fixedSpace]
    omega
  have hfin0 : Module.finrank K
      (primaryComponent (ggK1DOrthEnd (x : GL (LargeEvenMinusIdx (r - 1)) K)) (X - 1)) = 0 := by
    have hhead := hm.head_eq
    omega
  have hbot : primaryComponent
      (ggK1DOrthEnd (x : GL (LargeEvenMinusIdx (r - 1)) K)) (X - 1) = ⊥ :=
    Submodule.finrank_eq_zero.mp hfin0
  haveI : Subsingleton ↥(primaryComponent
      (ggK1DOrthEnd (x : GL (LargeEvenMinusIdx (r - 1)) K)) (X - 1)) := by
    rw [hbot]; infer_instance
  have hP : IsPlusType
      ((TableBOrth.qMinusForm K (r - 1) b c).restrict
        (primaryComponent (ggK1DOrthEnd (x : GL (LargeEvenMinusIdx (r - 1)) K)) (X - 1))) :=
    isPlusType_of_subsingleton _
  have hw := ggK1D_v0_witt_minus (K := K) hp hp2 hdvd hnf hK hirr hm hx
    (TableBOrth.qMinusForm K (r - 1) b c)
    (TableBOrth.coe_qMinusForm (K := K) (r - 1) b c).symm
  exact hw.mp hP

theorem ggK1D_core_valid_plus {p nf r : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hdvd : p ∣ 2 ^ nf - 1 ∨ p ∣ 2 ^ nf + 1) (h4 : 4 ≤ r) {K : Type} [Field K]
    (hnf : 1 ≤ nf) (hK : Nat.card K = 2 ^ nf)
    {x : ↥(LargeEvenOmega (LargeEvenQPlus K r))} {m : List ℕ}
    (hm : GGK1DMultOf p nf (ggMultOrd p nf) r K (x : GL (Fin r ⊕ Fin r) K) m)
    (hx : x ^ p = 1) :
    GGMultValidCl ⟨.D, r, nf⟩ p (ggMultDatumD p nf (ggMultOrd p nf) false m) := by
  haveI : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; positivity)
  have hd0 : ggMultOrd p nf ≠ 0 := by
    rcases hdvd with h | h
    · rw [ggMultOrd, if_pos h]; exact one_ne_zero
    · by_cases h1 : p ∣ 2 ^ nf - 1
      · rw [ggMultOrd, if_pos h1]; exact one_ne_zero
      · rw [ggMultOrd, if_neg h1, if_pos h]; exact two_ne_zero
  refine ⟨.D r, false, nf, by simp [ggKacTypeClOfLabel, h4], ?_⟩
  exact (mem_ggMultTableCl_D hd0).mpr
    ⟨m, hm.length_eq, hm.sum_eq, ggK1Dv_eps0_of_head_zero hp hp2 hdvd hnf hK hm hx, rfl⟩

theorem ggK1D_core_valid_minus {p nf r : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hdvd : p ∣ 2 ^ nf - 1 ∨ p ∣ 2 ^ nf + 1) (h4 : 4 ≤ r) {K : Type} [Field K]
    (hnf : 1 ≤ nf) (hK : Nat.card K = 2 ^ nf) {b c : K}
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    {x : ↥(LargeEvenOmega (LargeEvenQMinus (r - 1) b c))} {m : List ℕ}
    (hm : GGK1DMultOf p nf (ggMultOrd p nf) r K
      (x : GL (LargeEvenMinusIdx (r - 1)) K) m) (hx : x ^ p = 1) :
    GGMultValidCl ⟨.twD, r, nf⟩ p (ggMultDatumD p nf (ggMultOrd p nf) true m) := by
  haveI : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; positivity)
  have hd0 : ggMultOrd p nf ≠ 0 := by
    rcases hdvd with h | h
    · rw [ggMultOrd, if_pos h]; exact one_ne_zero
    · by_cases h1 : p ∣ 2 ^ nf - 1
      · rw [ggMultOrd, if_pos h1]; exact one_ne_zero
      · rw [ggMultOrd, if_neg h1, if_pos h]; exact two_ne_zero
  refine ⟨.D r, true, nf, by simp [ggKacTypeClOfLabel, h4], ?_⟩
  exact (mem_ggMultTableCl_D hd0).mpr
    ⟨m, hm.length_eq, hm.sum_eq,
      ggK1Dv_eps0_of_head_zero_minus hp hp2 hdvd hnf hK hirr hm hx, rfl⟩

end CFSG.StandardType

end

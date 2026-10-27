module

public import CFSG.LocalAnalysis.StandardType.GGK1CCoDefs
public import CFSG.LieType.SeitzGeneration.OrthManyPieces
public import CFSG.LocalAnalysis.StandardType.GGSpNonsplitFrameTorusField
public import CFSG.GroupTheory.HallHigmanPiCore
public import CFSG.LieType.SeitzGeneration.UnitaryNonsplit
public import CFSG.RankThree.PartOne.CTP.SeitzOrthModel
public import CFSG.RankThree.PartOne.KC.OrthogonalKernelSectorRigiditySelfDual
public import CFSG.RankThree.PartTwo.Sec4.Census.Interface

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Open Polynomial
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag (proj)
open CFSG.RankThree.Classical (spEnd IsReciprocalTransversal SpPrimaryBlocks spSupported
  symplectic_cross_prime_primary_centralizer_blocks)
open CFSG.RankThree.PartOne.KCPrimary
open CFSG.RankThree.PartOne.KCOrthogonal (reciprocalPolynomial)

theorem ggK1CBl_ff_degree {K : Type} [Field K] [Fintype K] {p : ℕ} (hp : p.Prime)
    (hpchar : p ≠ ringChar K) {h : K[X]} (hirr : Irreducible h) (hmon : h.Monic)
    (hdvd : h ∣ X ^ p - 1) (hne : h ≠ X - 1) :
    h.natDegree = orderOf ((Fintype.card K : ℕ) : ZMod p) := by
  simpa only [Nat.card_eq_fintype_card] using
    CFSG.LieType.SeitzGeneration.natDegree_eq_orderOf_of_dvd (K := K) hp hpchar hmon hirr hdvd
      hne

theorem ggK1CBl_ff_selfDual {K : Type} [Field K] [Fintype K] {p : ℕ} (hp : p.Prime)
    (hpchar : p ≠ ringChar K) (hpq : p ∣ Fintype.card K + 1) {h : K[X]} (hirr : Irreducible h)
    (hmon : h.Monic) (hdvd : h ∣ X ^ p - 1) (hne : h ≠ X - 1) :
    reciprocalPolynomial h = h := by
  classical
  haveI : Fact (Irreducible h) := ⟨hirr⟩
  haveI : Fact p.Prime := ⟨hp⟩
  have hpK : (p : K) ≠ 0 := by
    intro hc
    have hℓ : (ringChar K).Prime := CharP.char_is_prime K (ringChar K)
    have hdvd' : ringChar K ∣ p := (CharP.cast_eq_zero_iff K (ringChar K) p).mp hc
    exact hpchar ((Nat.prime_dvd_prime_iff_eq hℓ hp).mp hdvd').symm
  have hdvdΦ : h ∣ cyclotomic p K := by
    have h1 : h ∣ cyclotomic p K * (X - 1) := by
      rw [cyclotomic_prime_mul_X_sub_one]
      exact hdvd
    rcases hirr.prime.dvd_or_dvd h1 with h2 | h2
    · exact h2
    · exfalso
      have h3 : (X - 1 : K[X]) = X - C 1 := by rw [map_one]
      rw [h3] at h2 hne
      exact hne (eq_of_monic_of_associated hmon (monic_X_sub_C 1)
        (hirr.associated_of_dvd (irreducible_X_sub_C 1) h2))
  have h0 : h.coeff 0 ≠ 0 := by
    intro hzero
    obtain ⟨g, hg⟩ := hdvd
    have hc : (X ^ p - 1 : K[X]).coeff 0 = h.coeff 0 * g.coeff 0 := by
      rw [hg, mul_coeff_zero]
    have hc' : (X ^ p - 1 : K[X]).coeff 0 = -1 := by
      simp [coeff_X_pow, coeff_one, Ne.symm hp.ne_zero]
    rw [hzero, zero_mul, hc'] at hc
    exact one_ne_zero (neg_eq_zero.mp hc)
  have hζ0 : AdjoinRoot.root h ≠ 0 := by
    intro hr
    apply h0
    have h1 : aeval (AdjoinRoot.root h) h = 0 := by
      rw [AdjoinRoot.aeval_eq, AdjoinRoot.mk_self]
    rw [hr, aeval_def, eval₂_at_zero] at h1
    exact (algebraMap K (AdjoinRoot h)).injective (by rw [h1, map_zero])
  have hζp : AdjoinRoot.root h ^ p = 1 := by
    have h1 : aeval (AdjoinRoot.root h) (X ^ p - C 1 : K[X]) = 0 := by
      rw [AdjoinRoot.aeval_eq]
      exact AdjoinRoot.mk_eq_zero.mpr (by simpa only [C_1] using hdvd)
    have h2 : AdjoinRoot.root h ^ p - 1 = 0 := by simpa using h1
    rwa [sub_eq_zero] at h2
  have hpow : AdjoinRoot.root h ^ (p - 1) = (AdjoinRoot.root h)⁻¹ := by
    apply eq_inv_of_mul_eq_one_left
    rw [← pow_succ, Nat.sub_add_cancel hp.one_lt.le, hζp]
  have hpq' : p ∣ Nat.card K + 1 := by rwa [Nat.card_eq_fintype_card]
  have hζinv : aeval ((AdjoinRoot.root h)⁻¹) h = 0 := by
    rw [← hpow]
    exact SpNS.aeval_root_pow_pred (K := K) (g := h) hp hpK hdvdΦ hpq'
  let u : (AdjoinRoot h)ˣ := Units.mk0 (AdjoinRoot.root h) hζ0
  have hroot : AdjoinRoot.mk h (reciprocalPolynomial h) = 0 := by
    rw [← AdjoinRoot.aeval_eq]
    have hval : (u : AdjoinRoot h) = AdjoinRoot.root h := Units.val_mk0 hζ0
    rw [← hval, CFSG.RankThree.PartOne.KCOrthogonal.aeval_reciprocalPolynomial_of_unit u h,
      Units.val_inv_eq_inv_val, hval, hζinv]
    simp
  have hdvdrec : h ∣ reciprocalPolynomial h := AdjoinRoot.mk_eq_zero.mp hroot
  exact (eq_of_monic_of_associated hmon
    (CFSG.RankThree.PartOne.KCOrthogonal.monic_reciprocalPolynomial h0)
    (hirr.associated_of_dvd
      (CFSG.RankThree.PartOne.KCOrthogonal.irreducible_reciprocalPolynomial hirr h0)
      hdvdrec)).symm

end CFSG.StandardType

end

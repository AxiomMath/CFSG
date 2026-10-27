module

public import CFSG.RankThree.PartOne.KC.PrimaryDecomposition
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat

public section

namespace CFSG.RankThree.PartOne.KCLinComm

open Polynomial Module CFSG.RankThree.PartOne.KCPrimary

variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]

theorem squarefree_minpoly_of_pow_eq_one {p : ℕ} (hpK : (p : K) ≠ 0) {x : Module.End K V}
    (hxp : x ^ p = 1) : Squarefree (minpoly K x) := by
  have hsep : (X ^ p - C (1 : K) : K[X]).Separable := separable_X_pow_sub_C 1 hpK one_ne_zero
  refine squarefree_minpoly_of_aeval_eq_zero (p := X ^ p - C 1) hsep.squarefree ?_
  simp [hxp]

theorem card_primaryFactors_le_finrank {x : Module.End K V} (hx : Squarefree (minpoly K x)) :
    Nat.card (primaryFactors x) ≤ Module.finrank K V := by
  classical
  rw [finrank_eq_sum_primaryComponent hx, Nat.card_eq_fintype_card, ← Finset.card_univ,
    Finset.card_eq_sum_ones]
  refine Finset.sum_le_sum fun a _ => ?_
  have : Nontrivial (primaryComponent x (a : K[X])) :=
    Submodule.nontrivial_iff_ne_bot.mpr (primaryComponent_ne_bot hx a.2)
  exact Module.finrank_pos


theorem orderOf_le_natDegree_of_mem_primaryFactors [Finite K] {p : ℕ} (hp : p.Prime)
    {x : Module.End K V} (hxp : x ^ p = 1) {h : K[X]} (hh : h ∈ primaryFactors x)
    (hne : h ≠ X - C 1) : orderOf ((Nat.card K : ℕ) : ZMod p) ≤ h.natDegree := by
  have : Fact p.Prime := ⟨hp⟩
  have hirr : Irreducible h := irreducible_of_mem_primaryFactors hh
  have : Fact (Irreducible h) := ⟨hirr⟩
  have hdvd : h ∣ X ^ p - 1 := by
    refine (mem_primaryFactors.mp hh).2.2.trans (minpoly.dvd K x ?_)
    simp [hxp]
  have hζp : (AdjoinRoot.root h) ^ p = 1 := by
    have h0 : AdjoinRoot.mk h (X ^ p - 1) = 0 := AdjoinRoot.mk_eq_zero.mpr hdvd
    simpa [sub_eq_zero] using h0
  have hζ1 : AdjoinRoot.root h ≠ 1 := by
    intro h1
    apply hne
    have h0 : AdjoinRoot.mk h (X - C 1) = 0 := by simp [h1]
    have hdvd2 : h ∣ X - C 1 := AdjoinRoot.mk_eq_zero.mp h0
    exact eq_of_monic_of_associated (monic_of_mem_primaryFactors hh) (monic_X_sub_C 1)
      (hirr.associated_of_dvd (irreducible_X_sub_C 1) hdvd2)
  have hord : orderOf (AdjoinRoot.root h) = p := orderOf_eq_prime hζp hζ1
  have hζ0 : AdjoinRoot.root h ≠ 0 := by
    intro h0
    rw [h0, zero_pow hp.ne_zero] at hζp
    exact zero_ne_one hζp
  have hmod : Module.Finite K (AdjoinRoot h) :=
    (AdjoinRoot.powerBasis hirr.ne_zero).finite
  have hfin : Finite (AdjoinRoot h) := Module.finite_of_finite K
  have : Fintype (AdjoinRoot h) := Fintype.ofFinite _
  have hcard : Nat.card (AdjoinRoot h) = Nat.card K ^ h.natDegree := by
    rw [Module.natCard_eq_pow_finrank (K := K) (V := AdjoinRoot h),
      (AdjoinRoot.powerBasis hirr.ne_zero).finrank, AdjoinRoot.powerBasis_dim]
  have hpow : (AdjoinRoot.root h) ^ (Nat.card K ^ h.natDegree - 1) = 1 := by
    rw [← hcard, Nat.card_eq_fintype_card]
    exact FiniteField.pow_card_sub_one_eq_one _ hζ0
  have hpd : p ∣ Nat.card K ^ h.natDegree - 1 := by
    rw [← hord]
    exact orderOf_dvd_of_pow_eq_one hpow
  have hq1 : 1 ≤ Nat.card K ^ h.natDegree := Nat.one_le_pow _ _ Nat.card_pos
  have hzpow : ((Nat.card K : ℕ) : ZMod p) ^ h.natDegree = 1 := by
    have h1 := (ZMod.natCast_eq_zero_iff _ _).mpr hpd
    rw [Nat.cast_sub hq1, Nat.cast_pow, Nat.cast_one, sub_eq_zero] at h1
    exact h1
  exact Nat.le_of_dvd hirr.natDegree_pos (orderOf_dvd_of_pow_eq_one hzpow)


theorem card_primaryFactors_le [Finite K] {p : ℕ} (hp : p.Prime) {x : Module.End K V}
    (hx : Squarefree (minpoly K x)) (hxp : x ^ p = 1) (hpq : ¬ p ∣ Nat.card K) :
    Nat.card (primaryFactors x) ≤ 1 + (p - 1) / orderOf ((Nat.card K : ℕ) : ZMod p) := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  set d := orderOf ((Nat.card K : ℕ) : ZMod p) with hd
  have hd0 : 0 < d := by
    refine orderOf_pos_iff.mpr (isOfFinOrder_iff_pow_eq_one.mpr ⟨p - 1, by have := hp.one_lt; omega,
      ZMod.pow_card_sub_one_eq_one ?_⟩)
    intro h0
    exact hpq ((ZMod.natCast_eq_zero_iff _ _).mp h0)
  set F := primaryFactors x with hF
  set F' := F.erase (X - C 1) with hF'
  set g : K[X] := ∏ h ∈ F', h with hg
  have hmin : minpoly K x ∣ X ^ p - 1 := minpoly.dvd K x (by simp [hxp])
  have hgdvd : g ∣ X ^ p - 1 := by
    refine (dvd_trans ?_ hmin)
    rw [← prod_primaryFactors hx]
    exact Finset.prod_dvd_prod_of_subset F' F id (Finset.erase_subset _ _)
  have hcop : IsCoprime (X - C 1 : K[X]) g := by
    refine IsCoprime.prod_right fun h hh => ?_
    rw [(irreducible_X_sub_C (1 : K)).coprime_iff_not_dvd]
    intro hdvd
    have hhF : h ∈ F := Finset.mem_of_mem_erase hh
    exact (Finset.ne_of_mem_erase hh) (eq_of_monic_of_associated
      (monic_of_mem_primaryFactors hhF) (monic_X_sub_C 1)
      ((irreducible_X_sub_C (1 : K)).associated_of_dvd (irreducible_of_mem_primaryFactors hhF)
        hdvd).symm)
  have hdvd1 : (X - C 1 : K[X]) ∣ X ^ p - 1 := by
    simpa using sub_one_dvd_pow_sub_one (X : K[X]) p
  have hprod : (X - C 1 : K[X]) * g ∣ X ^ p - 1 := hcop.mul_dvd hdvd1 hgdvd
  have hg0 : g ≠ 0 := Finset.prod_ne_zero_iff.mpr fun h hh =>
    (irreducible_of_mem_primaryFactors (Finset.mem_of_mem_erase hh)).ne_zero
  have hX0 : (X ^ p - 1 : K[X]) ≠ 0 := by
    have := (monic_X_pow_sub_C (1 : K) hp.ne_zero).ne_zero
    simpa using this
  have hdeg : (1 + g.natDegree) ≤ p := by
    have h1 := natDegree_le_of_dvd hprod hX0
    rw [natDegree_mul (X_sub_C_ne_zero 1) hg0, natDegree_X_sub_C] at h1
    have h2 : (X ^ p - 1 : K[X]).natDegree = p := by
      simpa using natDegree_X_pow_sub_C (n := p) (r := (1 : K))
    omega
  have hsum : F'.card * d ≤ g.natDegree := by
    have h1 := Finset.card_nsmul_le_sum F' (fun h => h.natDegree) d fun h hh =>
      orderOf_le_natDegree_of_mem_primaryFactors hp hxp (Finset.mem_of_mem_erase hh)
        (Finset.ne_of_mem_erase hh)
    rw [smul_eq_mul] at h1
    rw [hg, natDegree_prod _ _ fun h hh =>
      (irreducible_of_mem_primaryFactors (Finset.mem_of_mem_erase hh)).ne_zero]
    exact h1
  have hle : F'.card ≤ (p - 1) / d := (Nat.le_div_iff_mul_le hd0).mpr (by omega)
  have hF1 : F.card - 1 ≤ F'.card := Finset.pred_card_le_card_erase
  rw [Nat.card_eq_fintype_card, Fintype.card_coe]
  omega


omit [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] in
theorem two_le_orderOf_natCast {p q : ℕ} (hp : p.Prime) (hq : 1 ≤ q) (hpq : ¬ p ∣ q)
    (hpq1 : ¬ p ∣ q - 1) : 2 ≤ orderOf (q : ZMod p) := by
  have : Fact p.Prime := ⟨hp⟩
  have hpos : 0 < orderOf (q : ZMod p) := by
    refine orderOf_pos_iff.mpr (isOfFinOrder_iff_pow_eq_one.mpr ⟨p - 1, by
      have := hp.one_lt; omega, ZMod.pow_card_sub_one_eq_one ?_⟩)
    intro h0
    exact hpq ((ZMod.natCast_eq_zero_iff _ _).mp h0)
  by_contra hlt
  have h1 : orderOf (q : ZMod p) = 1 := by omega
  rw [orderOf_eq_one_iff] at h1
  apply hpq1
  rw [← ZMod.natCast_eq_zero_iff, Nat.cast_sub hq, Nat.cast_one, h1, sub_self]

omit [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] in
theorem one_add_div_lt {p d : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hd : 2 ≤ d) :
    1 + (p - 1) / d < p := by
  have h3 : 3 ≤ p := by
    have := hp.two_le
    omega
  have : (p - 1) / d ≤ (p - 1) / 2 := Nat.div_le_div_left hd (by norm_num)
  omega

end CFSG.RankThree.PartOne.KCLinComm

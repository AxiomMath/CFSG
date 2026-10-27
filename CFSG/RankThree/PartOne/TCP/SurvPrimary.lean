module

public import CFSG.RankThree.PartOne.KC.OrthogonalNormPlanePrimary
public import CFSG.RankThree.Classical.SteinbergBJSymplecticCrossPrimeBlocks
public import CFSG.RankThree.PartOne.KC.OrthogonalSelfDualBlock

public section

namespace CFSG.RankThree.PartOne.TCP

open Polynomial Module CFSG.RankThree.Classical CFSG.RankThree.PartOne.KCPrimary
  CFSG.RankThree.PartOne.KCUnitary CFSG.RankThree.PartOne.KCOrthogonal

variable {K : Type} [Field K] [Finite K] {V : Type*} [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {p : ℕ}

theorem prime_dvd_card_add_one {q : ℕ} (hp : p.Prime) (hord : orderOf (q : ZMod p) = 2) :
    p ∣ q + 1 := by
  have : Fact p.Prime := ⟨hp⟩
  have h2 : (q : ZMod p) ^ 2 = 1 := hord ▸ pow_orderOf_eq_one _
  have h1 : (q : ZMod p) ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hord
    omega
  have h3 : ((q : ZMod p) - 1) * ((q : ZMod p) + 1) = 0 := by linear_combination h2
  rcases mul_eq_zero.mp h3 with h | h
  · exact absurd (sub_eq_zero.mp h) h1
  · rw [← ZMod.natCast_eq_zero_iff]
    push_cast
    exact h

theorem two_dvd_natDegree_of_mem (hp : p.Prime) {y : Module.End K V} (hy : y ^ p = 1)
    (hord : orderOf (Nat.card K : ZMod p) = 2) {h : K[X]} (hh : h ∈ primaryFactors y)
    (h1 : h ≠ X - 1) : 2 ∣ h.natDegree := by
  have : Fact p.Prime := ⟨hp⟩
  have : Fact (Irreducible h) := ⟨irreducible_of_mem_primaryFactors hh⟩
  have hroot := orderOf_root_of_mem hp hy hh h1
  have hz : (AdjoinRoot.root h) ≠ 0 := by
    intro h0
    rw [h0, orderOf_zero] at hroot
    exact hp.ne_zero hroot.symm
  have : Finite (AdjoinRoot h) := Module.finite_of_finite K
  have hdvd := orderOf_dvd_natCard_sub_one hz
  rw [hroot] at hdvd
  have hcard : Nat.card (AdjoinRoot h) = Nat.card K ^ h.natDegree := by
    rw [Module.natCard_eq_pow_finrank (K := K) (V := AdjoinRoot h), finrank_adjoinRoot]
  rw [hcard] at hdvd
  have hQd : (Nat.card K : ZMod p) ^ h.natDegree = 1 := by
    have h1' : 1 ≤ Nat.card K ^ h.natDegree := Nat.one_le_pow _ _ Nat.card_pos
    have h0 := (ZMod.natCast_eq_zero_iff _ _).mpr hdvd
    rw [Nat.cast_sub h1', Nat.cast_pow, Nat.cast_one, sub_eq_zero] at h0
    exact h0
  rw [← hord]
  exact orderOf_dvd_of_pow_eq_one hQd

theorem reciprocalPolynomial_eq_of_mem (hp : p.Prime) {y : Module.End K V} (hy : y ^ p = 1)
    (hord : orderOf (Nat.card K : ZMod p) = 2) {h : K[X]} (hh : h ∈ primaryFactors y)
    (h1 : h ≠ X - 1) : reciprocalPolynomial h = h := by
  have : Fact p.Prime := ⟨hp⟩
  have : Fact (Irreducible h) := ⟨irreducible_of_mem_primaryFactors hh⟩
  have hroot := orderOf_root_of_mem hp hy hh h1
  have hz : (AdjoinRoot.root h) ≠ 0 := by
    intro h0
    rw [h0, orderOf_zero] at hroot
    exact hp.ne_zero hroot.symm
  have : Fintype K := Fintype.ofFinite K
  have hpq : p ∣ Nat.card K + 1 := prime_dvd_card_add_one hp hord
  have hζ1 : AdjoinRoot.root h ^ (Nat.card K + 1) = 1 :=
    orderOf_dvd_iff_pow_eq_one.mp (hroot ▸ hpq)
  have hbar : (FiniteField.frobeniusAlgEquivOfAlgebraic K (AdjoinRoot h)) (AdjoinRoot.root h) =
      (AdjoinRoot.root h)⁻¹ := by
    rw [FiniteField.coe_frobeniusAlgEquivOfAlgebraic, ← Nat.card_eq_fintype_card]
    refine eq_inv_of_mul_eq_one_left ?_
    rw [← pow_succ]
    exact hζ1
  have hmin : minpoly K (AdjoinRoot.root h) = h := by
    rw [AdjoinRoot.minpoly_root (Fact.out : Irreducible h).ne_zero,
      (monic_of_mem_primaryFactors hh).leadingCoeff, inv_one, C_1, mul_one]
  have := reciprocalPolynomial_minpoly_eq (K := K) (E := AdjoinRoot h)
    (FiniteField.frobeniusAlgEquivOfAlgebraic K (AdjoinRoot h)) hz hbar
  rwa [hmin] at this

end CFSG.RankThree.PartOne.TCP

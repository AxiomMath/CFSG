module

public import CFSG.Monster.B.Geometry.F4Weyl
public import CFSG.LieType.Chevalley.LatticeWeylGroup

public section

namespace CFSG.RankThree.PartOne.K133H

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley Polynomial

theorem pow_three_eq_one_of_pow_nine_eq_one {n : Type} [Fintype n] [DecidableEq n]
    (hn : Fintype.card n < 6) (A : Matrix n n ℚ) (h : A ^ 9 = 1) : A ^ 3 = 1 := by
  have hchar0 : A.charpoly ≠ 0 := (Matrix.charpoly_monic A).ne_zero
  have hm9 : minpoly ℚ A ∣ (X : ℚ[X]) ^ 9 - 1 := minpoly.dvd ℚ A (by simp [h])
  have hmc : minpoly ℚ A ∣ A.charpoly := minpoly.dvd ℚ A (Matrix.aeval_self_charpoly A)
  have hmne : minpoly ℚ A ≠ 0 := fun h0 => hchar0 (zero_dvd_iff.1 (h0 ▸ hmc))
  have hdeg : (minpoly ℚ A).natDegree ≤ Fintype.card n := by
    have := Polynomial.natDegree_le_of_dvd hmc hchar0
    rwa [Matrix.charpoly_natDegree_eq_dim] at this
  have hfac : (X : ℚ[X]) ^ 9 - 1 = (X ^ 3 - 1) * cyclotomic 9 ℚ := by
    have := cyclotomic_prime_pow_eq_geom_sum (R := ℚ) (p := 3) (n := 1) Nat.prime_three
    rw [show (9 : ℕ) = 3 ^ (1 + 1) by norm_num, this]
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, pow_one, ← pow_mul]
    ring
  have hirr : Irreducible (cyclotomic 9 ℚ) := cyclotomic.irreducible_rat (by norm_num)
  have hnd : ¬ cyclotomic 9 ℚ ∣ minpoly ℚ A := by
    intro hd
    have h1 := Polynomial.natDegree_le_of_dvd hd hmne
    rw [natDegree_cyclotomic] at h1
    have : Nat.totient 9 = 6 := by decide
    omega
  have hcop : IsCoprime (minpoly ℚ A) (cyclotomic 9 ℚ) :=
    ((Irreducible.coprime_iff_not_dvd hirr).2 hnd).symm
  have hm3 : minpoly ℚ A ∣ (X : ℚ[X]) ^ 3 - 1 :=
    hcop.dvd_of_dvd_mul_right (hfac ▸ hm9)
  have := (minpoly.dvd_iff).1 hm3
  simpa [sub_eq_zero] using this

theorem card_weylGroup_F4 :
    Nat.card (WeylGroup .F4) = 1152 :=
  CFSG.Monster.B.Geometry.card_f4WeylGroup

noncomputable def weylF4Matrix : WeylGroup .F4 →* Matrix (Fin Tag.F4.rank) (Fin Tag.F4.rank) ℚ :=
  (RingHom.mapMatrix (Int.castRingHom ℚ)).toMonoidHom.comp
    ((LinearMap.toMatrixAlgEquiv' (R := ℤ) (n := Fin Tag.F4.rank)).toMonoidHom.comp
      ((Units.coeHom (Module.End ℤ (Fin Tag.F4.rank → ℤ))).comp (weylToAut .F4)))

theorem weylF4Matrix_injective : Function.Injective weylF4Matrix := by
  intro w w' h
  apply weylToAut_injective
  apply Units.ext
  apply (LinearMap.toMatrixAlgEquiv' (R := ℤ) (n := Fin Tag.F4.rank)).injective
  exact Matrix.map_injective Int.cast_injective h

theorem orderOf_eq_one_or_three_of_odd_F4
    (w : WeylGroup .F4) (hodd : Odd (orderOf w)) :
    orderOf w = 1 ∨ orderOf w = 3 := by
  have hdvd : orderOf w ∣ 1152 := card_weylGroup_F4 ▸ orderOf_dvd_natCard w
  have h9 : orderOf w ∣ 9 := by
    have hc : Nat.Coprime (orderOf w) (2 ^ 7) :=
      Nat.Coprime.pow_right 7 (Nat.coprime_two_right.mpr hodd)
    exact hc.dvd_of_dvd_mul_left (by simpa using hdvd : orderOf w ∣ 2 ^ 7 * 9)
  have hdiv : orderOf w ∈ Nat.divisors 9 := Nat.mem_divisors.2 ⟨h9, by norm_num⟩
  have hd9 : Nat.divisors 9 = {1, 3, 9} := by decide
  rw [hd9] at hdiv
  simp only [Finset.mem_insert, Finset.mem_singleton] at hdiv
  rcases hdiv with h | h | h
  · exact Or.inl h
  · exact Or.inr h
  · exfalso
    have h1 : (weylF4Matrix w) ^ 9 = 1 := by
      rw [← map_pow, ← h, pow_orderOf_eq_one, map_one]
    have h2 := pow_three_eq_one_of_pow_nine_eq_one (n := Fin Tag.F4.rank)
      (by rw [Fintype.card_fin]; decide) _ h1
    have h3 : w ^ 3 = 1 := weylF4Matrix_injective (by rw [map_pow, h2, map_one])
    have := orderOf_dvd_of_pow_eq_one h3
    rw [h] at this
    omega

theorem oddOrder_weylGroup_F4 :
    ∀ w : WeylGroup .F4, Odd (orderOf w) → orderOf w = 1 ∨ orderOf w = 3 :=
  orderOf_eq_one_or_three_of_odd_F4

end CFSG.RankThree.PartOne.K133H

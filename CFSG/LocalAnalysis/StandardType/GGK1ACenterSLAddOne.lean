module

public import CFSG.LocalAnalysis.StandardType.GGK1ACenterTorsion
public import CFSG.LinearAlgebra.MatrixPlanes

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Open Polynomial
open CFSG.RankThree.PartOne.KCPrimary

private theorem cenLA_gcd_prime_sub_one {p nf : ℕ} (hnf : nf ≠ 0)
    (hdvd : p ∣ 2 ^ nf + 1) : Nat.gcd p (2 ^ nf - 1) = 1 := by
  have heven : Even (2 ^ nf) := Even.pow_of_ne_zero (by norm_num) hnf
  have hpodd : Odd p := (heven.add_one).of_dvd_nat hdvd
  have hpow : 1 ≤ 2 ^ nf := Nat.one_le_pow _ _ (by norm_num)
  have hdp : Nat.gcd p (2 ^ nf - 1) ∣ p := Nat.gcd_dvd_left _ _
  have hdm : Nat.gcd p (2 ^ nf - 1) ∣ 2 ^ nf - 1 := Nat.gcd_dvd_right _ _
  have hd2 : Nat.gcd p (2 ^ nf - 1) ∣ 2 := by
    have h := Nat.dvd_sub (hdp.trans hdvd) hdm
    rwa [show 2 ^ nf + 1 - (2 ^ nf - 1) = 2 by omega] at h
  rcases (Nat.dvd_prime Nat.prime_two).mp hd2 with h | h
  · exact h
  · exfalso
    obtain ⟨k, hk⟩ := hpodd.of_dvd_nat hdp
    omega

private theorem cenLA_glEnd_pow_eq_one {p N : ℕ} {K : Type} [Field K] {x : GL (Fin N) K}
    (hxp : x ^ p = 1) : ggK1A_glEnd x ^ p = 1 := by
  have hcoe : ((x : GL (Fin N) K) : Matrix (Fin N) (Fin N) K) ^ p = 1 := by
    rw [← Units.val_pow_eq_pow_val, hxp, Units.val_one]
  rw [ggK1A_glEnd, ← Matrix.toLin'_pow, hcoe, Matrix.toLin'_one]
  rfl

private theorem cenLA_minpoly_dvd {p N : ℕ} {K : Type} [Field K] {x : GL (Fin N) K}
    (hxp : x ^ p = 1) : minpoly K (ggK1A_glEnd x) ∣ X ^ p - 1 := by
  apply minpoly.dvd K
  rw [map_sub, map_pow, aeval_X, aeval_one, cenLA_glEnd_pow_eq_one hxp, sub_self]

private theorem cenLA_units_eq_one {p : ℕ} {K : Type} [Field K] [Fintype K] {u : Kˣ}
    (hup : u ^ p = 1) (hgcd : Nat.gcd p (Nat.card K - 1) = 1) : u = 1 := by
  have huq : u ^ (Nat.card K - 1) = 1 := by
    ext
    rw [Units.val_pow_eq_pow_val, Units.val_one, Nat.card_eq_fintype_card]
    exact FiniteField.pow_card_sub_one_eq_one _ u.ne_zero
  have hdvd1 : orderOf u ∣ p := orderOf_dvd_iff_pow_eq_one.mpr hup
  have hdvd2 : orderOf u ∣ Nat.card K - 1 := orderOf_dvd_iff_pow_eq_one.mpr huq
  have hdvd : orderOf u ∣ Nat.gcd p (Nat.card K - 1) := Nat.dvd_gcd hdvd1 hdvd2
  rw [hgcd] at hdvd
  exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp hdvd)

private theorem cenLA_card_adjoinRoot {K : Type} [Field K] [Finite K] {f : K[X]}
    (hf : f.Monic) : Nat.card (AdjoinRoot f) = Nat.card K ^ f.natDegree := by
  have : Module.Finite K (AdjoinRoot f) := hf.finite_adjoinRoot
  rw [Module.natCard_eq_pow_finrank (K := K) (V := AdjoinRoot f),
    (AdjoinRoot.powerBasis' hf).finrank, AdjoinRoot.powerBasis'_dim]

private theorem cenLA_card_adjoinRoot_X_sub_one {K : Type} [Field K] [Finite K] :
    Nat.card (AdjoinRoot (X - C (1 : K) : K[X])) = Nat.card K := by
  rw [cenLA_card_adjoinRoot (monic_X_sub_C (1 : K)), Polynomial.natDegree_X_sub_C, pow_one]

private theorem cenLA_gcd_eq_one_of_eq_X_sub_one {p N : ℕ} {K : Type} [Field K] [Finite K]
    {x : GL (Fin N) K} (a : primaryFactors (ggK1A_glEnd x))
    (ha : (a : K[X]) = X - C 1) (hgcd : Nat.gcd p (Nat.card K - 1) = 1) :
    Nat.gcd p (Nat.card (AdjoinRoot (a : K[X])) - 1) = 1 := by
  have hcard : Nat.card (AdjoinRoot (a : K[X])) = Nat.card K := by
    rw [ha, cenLA_card_adjoinRoot_X_sub_one]
  rw [hcard, hgcd]

private theorem cenLA_gcd_eq_prime_of_ne {p N : ℕ} {K : Type} [Field K] [Finite K]
    {x : GL (Fin N) K} (hp : p.Prime) (hxp : x ^ p = 1)
    (a : primaryFactors (ggK1A_glEnd x)) (ha : (a : K[X]) ≠ X - C 1) :
    Nat.gcd p (Nat.card (AdjoinRoot (a : K[X])) - 1) = p := by
  have : Fact p.Prime := ⟨hp⟩
  have : Fact (Irreducible (a : K[X])) := ⟨irreducible_of_mem_primaryFactors a.2⟩
  have : Module.Finite K (AdjoinRoot (a : K[X])) :=
    (monic_of_mem_primaryFactors a.2).finite_adjoinRoot
  have : Finite (AdjoinRoot (a : K[X])) := Module.finite_of_finite K
  have hadvd : (a : K[X]) ∣ X ^ p - 1 :=
    (mem_primaryFactors.mp a.2).2.2.trans (cenLA_minpoly_dvd hxp)
  have hpow : AdjoinRoot.root (a : K[X]) ^ p = 1 := by
    have h0 : AdjoinRoot.mk (a : K[X]) (X ^ p - 1) = 0 := AdjoinRoot.mk_eq_zero.mpr hadvd
    rw [map_sub, map_pow, AdjoinRoot.mk_X, map_one, sub_eq_zero] at h0
    exact h0
  have hne : AdjoinRoot.root (a : K[X]) ≠ 1 := by
    intro h1
    have h0 : AdjoinRoot.mk (a : K[X]) (X - C 1) = 0 := by
      rw [map_sub, AdjoinRoot.mk_X, AdjoinRoot.mk_C]
      change AdjoinRoot.root (a : K[X]) - algebraMap K (AdjoinRoot (a : K[X])) 1 = 0
      rw [h1, map_one, sub_self]
    have hdv : (a : K[X]) ∣ X - C 1 := AdjoinRoot.mk_eq_zero.mp h0
    have hass : Associated (a : K[X]) (X - C 1) :=
      (irreducible_of_mem_primaryFactors a.2).associated_of_dvd
        (Polynomial.irreducible_X_sub_C 1) hdv
    have heq : (a : K[X]) = X - C 1 :=
      eq_of_monic_of_associated (monic_of_mem_primaryFactors a.2) (monic_X_sub_C 1) hass
    exact ha heq
  have hroot0 : AdjoinRoot.root (a : K[X]) ≠ 0 := fun h0 => hne (by
    have h := hpow
    rw [h0, zero_pow hp.ne_zero] at h
    exact absurd h zero_ne_one)
  let u : (AdjoinRoot (a : K[X]))ˣ := Units.mk0 _ hroot0
  have hu : orderOf u = p := by
    refine orderOf_eq_prime ?_ ?_
    · ext; simpa [u] using hpow
    · intro h1; exact hne (by simpa [u] using congrArg Units.val h1)
  have hpdiv : p ∣ Nat.card (AdjoinRoot (a : K[X])) - 1 := by
    rw [← Nat.card_units, ← hu]
    exact orderOf_dvd_natCard u
  exact Nat.gcd_eq_left hpdiv

private theorem cenLA_card_torsGL_eq {p N : ℕ} {K : Type} [Field K] [Finite K]
    {x : GL (Fin N) K} (hp : p.Prime) (hxp : x ^ p = 1)
    (hgcd : Nat.gcd p (Nat.card K - 1) = 1)
    (hsq : Squarefree (minpoly K (ggK1A_glEnd x))) :
    Nat.card (ggK1A_torsGL x p) = p ^ (ggK1A_selfDualFactors x).card := by
  classical
  rw [card_ggK1A_torsGL hp.pos hsq]
  rw [Finset.prod_coe_sort (primaryFactors (ggK1A_glEnd x))
    (fun a : K[X] => Nat.gcd p (Nat.card (AdjoinRoot a) - 1))]
  trans ∏ a ∈ primaryFactors (ggK1A_glEnd x), (if (a : K[X]) = X - C 1 then 1 else p)
  · apply Finset.prod_congr rfl
    intro a ha
    by_cases h : (a : K[X]) = X - C 1
    · rw [if_pos h]
      exact cenLA_gcd_eq_one_of_eq_X_sub_one ⟨a, ha⟩ h hgcd
    · rw [if_neg h]
      exact cenLA_gcd_eq_prime_of_ne hp hxp ⟨a, ha⟩ h
  · trans ∏ a ∈ (primaryFactors (ggK1A_glEnd x)).filter (fun a => a ≠ X - C 1), p
    · rw [Finset.prod_filter]
      apply Finset.prod_congr rfl
      intro a _
      by_cases h : a = X - C 1 <;> simp [h]
    · rw [Finset.prod_const]
      rfl

theorem ggK1A_exists_torsion_sl_of_dvd_add_one {p nf N : ℕ} {K : Type} [Field K] [Finite K]
    (hp : p.Prime) (hK : Nat.card K = 2 ^ nf) (hdvd : p ∣ 2 ^ nf + 1)
    {x : GL (Fin N) K} (hxp : x ^ p = 1) :
    ∃ T : Subgroup (GL (Fin N) K), T ≤ LargeEvenSLGroup (Fin N) K ∧ T ≤ ggK1A_torsGL x p ∧
      T ⊓ LargeEvenScalars (Fin N) K = ⊥ ∧
      Nat.card T = p ^ (ggK1A_selfDualFactors x).card := by
  classical
  have : Fintype K := Fintype.ofFinite K
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hnf : nf ≠ 0 := by
    intro h0
    have h1 : Nat.card K = 1 := by rw [hK, h0, pow_zero]
    have h2 : 1 < Nat.card K := by
      rw [Nat.card_eq_fintype_card]
      exact Fintype.one_lt_card
    omega
  have : CharP K 2 := by
    apply charP_of_card_eq_prime_pow
    rw [← Nat.card_eq_fintype_card, hK]
  have hpodd : Odd p := by
    have heven : Even (2 ^ nf) := Even.pow_of_ne_zero (by norm_num) hnf
    exact (heven.add_one).of_dvd_nat hdvd
  have hpK : (p : K) ≠ 0 := by
    rw [Ne, CharP.cast_eq_zero_iff K 2]
    exact hpodd.not_two_dvd_nat
  have hgcd : Nat.gcd p (Nat.card K - 1) = 1 := by
    rw [hK]
    exact cenLA_gcd_prime_sub_one hnf hdvd
  have hsq : Squarefree (minpoly K (ggK1A_glEnd x)) :=
    squarefree_minpoly_ggK1A_glEnd hpK hxp
  have hsl : ggK1A_torsGL x p ≤ LargeEvenSLGroup (Fin N) K := by
    intro t ht
    rw [LargeEvenSLGroup, MonoidHom.mem_ker]
    exact cenLA_units_eq_one (by rw [← map_pow, (mem_ggK1A_torsGL_iff.mp ht).1, map_one]) hgcd
  have hdisj : ggK1A_torsGL x p ⊓ LargeEvenScalars (Fin N) K = ⊥ := by
    rcases Nat.eq_zero_or_pos N with hN0 | hN
    · subst hN0
      rw [Subgroup.eq_bot_iff_forall]
      intro t _
      exact Subsingleton.elim t 1
    · have : Nonempty (Fin N) := ⟨⟨0, hN⟩⟩
      apply le_antisymm _ bot_le
      intro t ht
      obtain ⟨htT, htS⟩ := Subgroup.mem_inf.mp ht
      rw [CFSG.Assembly.largeEvenScalars_def, MonoidHom.mem_range] at htS
      obtain ⟨c, rfl⟩ := htS
      rw [Subgroup.mem_bot]
      have hcp : c ^ p = 1 := by
        apply CFSG.LinearAlgebra.generalLinearGroup_scalar_injective (ι := Fin N)
        rw [map_pow, (mem_ggK1A_torsGL_iff.mp htT).1, map_one]
      rw [cenLA_units_eq_one hcp hgcd, map_one]
  exact ⟨ggK1A_torsGL x p, hsl, le_rfl, hdisj, cenLA_card_torsGL_eq hp hxp hgcd hsq⟩

end CFSG.StandardType

end

module

public import CFSG.RankThree.PartOne.KC.LinearCommutatorOdd

public section

namespace CFSG.RankThree.PartOne

open Polynomial Matrix CFSG CFSG.RankThree.LocalRank CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag CFSG.RankThree.PartOne.KCPrimary
open CFSG.RankThree.PartOne.KCLinComm CFSG.RankThree.PartOne.KCLinCommOdd

theorem nonsplit_linear_inner_actor_local_core_commutators_odd {p ℓ f n : ℕ} (hp : p.Prime)
    (hp3 : 3 < p) (hℓ : ℓ.Prime) (hℓp : ℓ ≠ p) (hf : 1 ≤ f) (hn : 3 ≤ n) {K : Type} [Field K]
    [CharP K ℓ] (hK : Nat.card K = ℓ ^ f) (hq : 3 < ℓ ^ f) (hpq : ¬ p ∣ ℓ ^ f - 1)
    (B : Subgroup (MulAut (projectiveSL n K)))
    (hB : (MulAut.conj : projectiveSL n K →* MulAut (projectiveSL n K)).range ≤ B)
    {t : MulAut (projectiveSL n K)}
    (ht : t ∈ (MulAut.conj : projectiveSL n K →* MulAut (projectiveSL n K)).range)
    (htp : orderOf t = p) :
    (∀ A : Subgroup (MulAut (projectiveSL n K)), A ≤ B ⊓ Subgroup.centralizer {t} →
      IsPGroup p A →
      Odd (Nat.card (⁅inSubgroup (aschbacherSolvableCore p) (B ⊓ Subgroup.centralizer {t}), A⁆ :
        Subgroup (MulAut (projectiveSL n K))))) ∧
    ∀ x : SpecialLinearGroup (Fin n) K, orderOf x = p → MulAut.conj (proj n K x) = t →
      Squarefree (minpoly K (Matrix.toLin' (x : Matrix (Fin n) (Fin n) K))) ∧
      Nonempty (commutant (Matrix.toLin' (x : Matrix (Fin n) (Fin n) K)) ≃ₐ[K]
        ((a : primaryFactors (Matrix.toLin' (x : Matrix (Fin n) (Fin n) K))) →
          Matrix (Fin (primaryMultiplicity (Matrix.toLin' (x : Matrix (Fin n) (Fin n) K))
              (a : K[X])))
            (Fin (primaryMultiplicity (Matrix.toLin' (x : Matrix (Fin n) (Fin n) K))
              (a : K[X]))) (AdjoinRoot (a : K[X])))) ∧
      Nat.card (primaryFactors (Matrix.toLin' (x : Matrix (Fin n) (Fin n) K))) ≤
        1 + (p - 1) / orderOf ((ℓ ^ f : ℕ) : ZMod p) ∧
      1 + (p - 1) / orderOf ((ℓ ^ f : ℕ) : ZMod p) < p := by
  have hp2 : p ≠ 2 := by omega
  have : Fact p.Prime := ⟨hp⟩
  have hfin : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; exact pow_ne_zero _ hℓ.ne_zero)
  have hpK : (p : K) ≠ 0 := by
    intro h0
    exact hℓp ((Nat.prime_dvd_prime_iff_eq hℓ hp).mp ((CharP.cast_eq_zero_iff K ℓ p).mp h0))
  have hpq' : ¬ p ∣ Nat.card K := by
    rw [hK]
    intro hdvd
    exact hℓp ((Nat.prime_dvd_prime_iff_eq hp hℓ).mp (hp.dvd_of_dvd_pow hdvd)).symm
  have hq1 : 1 ≤ ℓ ^ f := by omega
  have hd : 2 ≤ orderOf ((ℓ ^ f : ℕ) : ZMod p) := by
    refine KCLinComm.two_le_orderOf_natCast hp hq1 ?_ hpq
    rw [← hK]
    exact hpq'
  have hbound : 1 + (p - 1) / orderOf ((ℓ ^ f : ℕ) : ZMod p) < p :=
    KCLinComm.one_add_div_lt hp hp2 hd
  have hZp : ∀ c : Kˣ, c ^ p = 1 → c ^ n = 1 → c = 1 := by
    intro c hcp _
    have hcq : c ^ (ℓ ^ f - 1) = 1 := by
      have := Fintype.ofFinite K
      have := FiniteField.pow_card_sub_one_eq_one (c : K) c.ne_zero
      rw [Fintype.card_eq_nat_card, hK] at this
      exact Units.ext (by simpa using this)
    have hcop : Nat.Coprime p (ℓ ^ f - 1) := (Nat.Prime.coprime_iff_not_dvd hp).mpr hpq
    have : c ^ Nat.gcd p (ℓ ^ f - 1) = 1 := pow_gcd_eq_one.mpr ⟨hcp, hcq⟩
    rwa [hcop, pow_one] at this
  have hrle : ∀ x : SpecialLinearGroup (Fin n) K, x ^ p = 1 →
      Nat.card (primaryFactors (Matrix.toLin' (x : Matrix (Fin n) (Fin n) K))) ≤
        1 + (p - 1) / orderOf ((ℓ ^ f : ℕ) : ZMod p) := by
    intro x hxp
    have hsq : Squarefree (minpoly K (Matrix.toLin' (x : Matrix (Fin n) (Fin n) K))) := by
      refine KCLinComm.squarefree_minpoly_of_pow_eq_one hpK ?_
      rw [← Matrix.toLin'_pow, ← Matrix.SpecialLinearGroup.coe_pow, hxp,
        Matrix.SpecialLinearGroup.coe_one, Matrix.toLin'_one]
      rfl
    have hxp' : (Matrix.toLin' (x : Matrix (Fin n) (Fin n) K)) ^ p = 1 := by
      rw [← Matrix.toLin'_pow, ← Matrix.SpecialLinearGroup.coe_pow, hxp,
        Matrix.SpecialLinearGroup.coe_one, Matrix.toLin'_one]
      rfl
    have := KCLinComm.card_primaryFactors_le hp hsq hxp' hpq'
    rwa [hK] at this
  refine ⟨fun A hAle hAp => ?_, fun x hxo hxt => ?_⟩
  · exact linear_inner_actor_local_core_commutators_odd_of_params hp hp2 hℓ hℓp hf hn hK hq hZp
      (fun x hxp => lt_of_le_of_lt (hrle x hxp) hbound) B hB ht htp A hAle hAp
  · obtain ⟨hxp, hsq⟩ := lift_data hp hℓp hℓ hxo
    exact ⟨hsq, ⟨commutantEquivMatrix hsq⟩, hrle x hxp, hbound⟩

theorem linear_below_prime_inner_actor_local_core_commutators_odd {p ℓ f n : ℕ} (hp : p.Prime)
    (hp3 : 3 < p) (hℓ : ℓ.Prime) (hℓp : ℓ ≠ p) (hf : 1 ≤ f) (hn : 3 ≤ n) (hnp : n < p)
    {K : Type} [Field K] [CharP K ℓ] (hK : Nat.card K = ℓ ^ f) (hq : 3 < ℓ ^ f)
    (B : Subgroup (MulAut (projectiveSL n K)))
    (hB : (MulAut.conj : projectiveSL n K →* MulAut (projectiveSL n K)).range ≤ B)
    {t : MulAut (projectiveSL n K)}
    (ht : t ∈ (MulAut.conj : projectiveSL n K →* MulAut (projectiveSL n K)).range)
    (htp : orderOf t = p) :
    ∀ A : Subgroup (MulAut (projectiveSL n K)), A ≤ B ⊓ Subgroup.centralizer {t} →
      IsPGroup p A →
      Odd (Nat.card (⁅inSubgroup (aschbacherSolvableCore p) (B ⊓ Subgroup.centralizer {t}), A⁆ :
        Subgroup (MulAut (projectiveSL n K)))) := by
  intro A hAle hAp
  have hp2 : p ≠ 2 := by omega
  have : Fact p.Prime := ⟨hp⟩
  have hfin : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; exact pow_ne_zero _ hℓ.ne_zero)
  have hpK : (p : K) ≠ 0 := by
    intro h0
    exact hℓp ((Nat.prime_dvd_prime_iff_eq hℓ hp).mp ((CharP.cast_eq_zero_iff K ℓ p).mp h0))
  have hZp : ∀ c : Kˣ, c ^ p = 1 → c ^ n = 1 → c = 1 := by
    intro c hcp hcn
    have hcop : Nat.Coprime p n :=
      (Nat.Prime.coprime_iff_not_dvd hp).mpr (Nat.not_dvd_of_pos_of_lt (by omega) hnp)
    have : c ^ Nat.gcd p n = 1 := pow_gcd_eq_one.mpr ⟨hcp, hcn⟩
    rwa [hcop, pow_one] at this
  have hr : ∀ x : SpecialLinearGroup (Fin n) K, x ^ p = 1 →
      Nat.card (primaryFactors (Matrix.toLin' (x : Matrix (Fin n) (Fin n) K))) < p := by
    intro x hxp
    have hxp' : (Matrix.toLin' (x : Matrix (Fin n) (Fin n) K)) ^ p = 1 := by
      rw [← Matrix.toLin'_pow, ← Matrix.SpecialLinearGroup.coe_pow, hxp,
        Matrix.SpecialLinearGroup.coe_one, Matrix.toLin'_one]
      rfl
    have hsq := KCLinComm.squarefree_minpoly_of_pow_eq_one hpK hxp'
    have := KCLinComm.card_primaryFactors_le_finrank hsq
    rw [Module.finrank_fin_fun] at this
    omega
  exact linear_inner_actor_local_core_commutators_odd_of_params hp hp2 hℓ hℓp hf hn hK hq hZp hr
    B hB ht htp A hAle hAp

end CFSG.RankThree.PartOne

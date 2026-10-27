module

public import Mathlib.LinearAlgebra.Charpoly.Basic
public import Mathlib.Algebra.Field.ZMod
import Mathlib.FieldTheory.Finite.Basic

public section

namespace CFSG.RankThree.PartTwo.Sec18.Item187Proof

@[expose] def lcmPowTwoSubOne (d : ℕ) : ℕ := (Finset.Icc 1 d).lcm fun j => 2 ^ j - 1

theorem lcmPowTwoSubOne_mono {d e : ℕ} (h : d ≤ e) : lcmPowTwoSubOne d ∣ lcmPowTwoSubOne e :=
  Finset.lcm_mono (Finset.Icc_subset_Icc le_rfl h)

section PolyDvd

open Polynomial

private theorem irreducible_dvd_lcmPowTwoSubOne {p : Polynomial (ZMod 2)} (hp : Irreducible p)
    {N d : ℕ} (hN0 : N ≠ 0) (hpN : p ∣ X ^ N - 1) (hdeg : p.natDegree ≤ d) :
    p ∣ X ^ lcmPowTwoSubOne d - 1 := by
  have hp0 : p ≠ 0 := hp.ne_zero
  have he : 1 ≤ p.natDegree := hp.natDegree_pos
  haveI : Fact (Irreducible p) := ⟨hp⟩
  have hroot : AdjoinRoot.root p ^ N = 1 := by
    have h := AdjoinRoot.mk_eq_zero.mpr hpN
    rwa [map_sub, map_pow, AdjoinRoot.mk_X, map_one, sub_eq_zero] at h
  have hne : AdjoinRoot.root p ≠ 0 := by
    intro h0
    rw [h0, zero_pow hN0] at hroot
    exact zero_ne_one hroot
  haveI : Module.Finite (ZMod 2) (AdjoinRoot p) := (AdjoinRoot.powerBasis hp0).finite
  haveI : Finite (AdjoinRoot p) := Module.finite_of_finite (ZMod 2)
  have hcard : Nat.card (AdjoinRoot p) = 2 ^ p.natDegree := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod,
      (AdjoinRoot.powerBasis hp0).finrank, AdjoinRoot.powerBasis_dim hp0]
  letI : Fintype (AdjoinRoot p) := Fintype.ofFinite _
  have hpow : AdjoinRoot.root p ^ (2 ^ p.natDegree - 1) = 1 := by
    have h := FiniteField.pow_card_sub_one_eq_one (AdjoinRoot.root p) hne
    rwa [← Nat.card_eq_fintype_card, hcard] at h
  have hdvd₁ : p ∣ X ^ (2 ^ p.natDegree - 1) - 1 :=
    AdjoinRoot.mk_eq_zero.mp (by
      rw [map_sub, map_pow, AdjoinRoot.mk_X, map_one, sub_eq_zero]
      exact hpow)
  have hdvd₂ : 2 ^ p.natDegree - 1 ∣ lcmPowTwoSubOne d :=
    Finset.dvd_lcm (f := fun j => 2 ^ j - 1) (Finset.mem_Icc.mpr ⟨he, hdeg⟩)
  obtain ⟨k, hk⟩ := hdvd₂
  have hdvd₃ : (X ^ (2 ^ p.natDegree - 1) - 1 : Polynomial (ZMod 2)) ∣
      X ^ lcmPowTwoSubOne d - 1 := by
    rw [hk, pow_mul]
    simpa only [one_pow] using
      sub_dvd_pow_sub_pow (X ^ (2 ^ p.natDegree - 1) : Polynomial (ZMod 2)) 1 k
  exact hdvd₁.trans hdvd₃

private theorem dvd_lcmPowTwoSubOne_of_squarefree {μ : Polynomial (ZMod 2)} (hμ0 : μ ≠ 0)
    (hμsq : Squarefree μ) {N d : ℕ} (hN0 : N ≠ 0) (hμN : μ ∣ X ^ N - 1)
    (hμd : μ.natDegree ≤ d) : μ ∣ X ^ lcmPowTwoSubOne d - 1 := by
  suffices h : ∀ g : Polynomial (ZMod 2), g ∣ μ → g ∣ X ^ lcmPowTwoSubOne d - 1 from
    h μ dvd_rfl
  intro g
  refine UniqueFactorizationMonoid.induction_on_prime
    (P := fun g => g ∣ μ → g ∣ X ^ lcmPowTwoSubOne d - 1) g ?_ ?_ ?_
  · intro h0
    exact absurd (zero_dvd_iff.mp h0) hμ0
  · intro u hu _
    exact (isUnit_iff_dvd_one.mp hu).trans (one_dvd _)
  · intro a p _ hp ih hpa
    have hpirr : Irreducible p := hp.irreducible
    have hpμ : p ∣ μ := (dvd_mul_right p a).trans hpa
    have hpdiv : p ∣ X ^ lcmPowTwoSubOne d - 1 :=
      irreducible_dvd_lcmPowTwoSubOne hpirr hN0 (hpμ.trans hμN)
        ((Polynomial.natDegree_le_of_dvd hpμ hμ0).trans hμd)
    have hnd : ¬ p ∣ a := by
      rintro ⟨b, rfl⟩
      have hdiv : p * p ∣ p * (p * b) := ⟨b, by ring⟩
      exact hpirr.not_isUnit (hμsq p (hdiv.trans hpa))
    exact ((Irreducible.coprime_iff_not_dvd hpirr).mpr hnd).mul_dvd hpdiv
      (ih ((dvd_mul_left a p).trans hpa))

end PolyDvd

theorem pow_lcmPowTwoSubOne_eq_one {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V] (f : Module.End (ZMod 2) V) {N : ℕ} (hN : Odd N)
    (hf : f ^ N = 1) : f ^ lcmPowTwoSubOne (Module.finrank (ZMod 2) V) = 1 := by
  have hN0 : N ≠ 0 := by
    rintro rfl
    obtain ⟨m, hm⟩ := hN
    omega
  have hNF : (N : ZMod 2) ≠ 0 := by
    intro h
    rw [ZMod.natCast_eq_zero_iff_even] at h
    exact (Nat.not_even_iff_odd.mpr hN) h
  have hsep : (Polynomial.X ^ N - 1 : Polynomial (ZMod 2)).Separable := by
    have h := Polynomial.separable_X_pow_sub_C (1 : ZMod 2) hNF one_ne_zero
    rwa [map_one] at h
  have hint : IsIntegral (ZMod 2) f := LinearMap.isIntegral f
  have hμ0 : minpoly (ZMod 2) f ≠ 0 := minpoly.ne_zero hint
  have hXN : Polynomial.aeval f (Polynomial.X ^ N - 1 : Polynomial (ZMod 2)) = 0 := by
    simp [hf]
  have hμN : minpoly (ZMod 2) f ∣ Polynomial.X ^ N - 1 := minpoly.dvd (ZMod 2) f hXN
  have hμsq : Squarefree (minpoly (ZMod 2) f) :=
    Squarefree.squarefree_of_dvd hμN hsep.squarefree
  have hμd : (minpoly (ZMod 2) f).natDegree ≤ Module.finrank (ZMod 2) V := by
    have h1 : minpoly (ZMod 2) f ∣ f.charpoly := LinearMap.minpoly_dvd_charpoly f
    have h2 := Polynomial.natDegree_le_of_dvd h1 (LinearMap.charpoly_monic f).ne_zero
    rwa [LinearMap.charpoly_natDegree f] at h2
  obtain ⟨q, hq⟩ := dvd_lcmPowTwoSubOne_of_squarefree hμ0 hμsq hN0 hμN hμd
  have hz : Polynomial.aeval f
      (Polynomial.X ^ lcmPowTwoSubOne (Module.finrank (ZMod 2) V) - 1 :
        Polynomial (ZMod 2)) = 0 := by
    rw [hq, map_mul, minpoly.aeval (ZMod 2) f, zero_mul]
  simpa [sub_eq_zero] using hz

theorem lcmPowTwoSubOne_eleven : lcmPowTwoSubOne 11 = 34654391537535 := by
  unfold lcmPowTwoSubOne
  decide +kernel

theorem lcmPowTwoSubOne_eight : lcmPowTwoSubOne 8 = 21082635 := by
  unfold lcmPowTwoSubOne
  decide +kernel

theorem not_thirteen_dvd_lcmPowTwoSubOne : ¬ 13 ∣ lcmPowTwoSubOne 11 := by
  rw [lcmPowTwoSubOne_eleven]
  decide

theorem not_dvd_lcmPowTwoSubOne_eight {m : ℕ} (hm : Odd m) (h3 : 3 ≤ m) :
    ¬ (4 ^ m + 2 ^ m + 1) ∣ lcmPowTwoSubOne 8 := by
  intro h
  rw [lcmPowTwoSubOne_eight] at h
  have hle : 4 ^ m + 2 ^ m + 1 ≤ 21082635 := Nat.le_of_dvd (by norm_num) h
  have hm12 : m ≤ 12 := by
    by_contra hc
    push Not at hc
    have h4 : 4 ^ 13 ≤ 4 ^ m := Nat.pow_le_pow_right (by norm_num) hc
    have h2 : 0 < 2 ^ m := by positivity
    omega
  obtain ⟨k, rfl⟩ := hm
  have hk : k ≤ 5 := by omega
  have hk1 : 1 ≤ k := by omega
  interval_cases k <;> revert h <;> decide

end CFSG.RankThree.PartTwo.Sec18.Item187Proof

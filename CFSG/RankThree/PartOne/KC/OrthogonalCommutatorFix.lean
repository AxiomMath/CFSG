module

public import CFSG.RankThree.PartOne.KC.PrimaryDecomposition
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
public import Mathlib.Tactic.Polynomial.Basic

public section

namespace CFSG.RankThree.PartOne.KCOrthComm

open Polynomial Module CFSG.RankThree.PartOne.KCPrimary

section Semilinear

variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]
  (σ : K ≃+* K) (F : V ≃+ V) {x : Module.End K V}

theorem F_pow_apply (hFx : ∀ v, F (x v) = x (F v)) (n : ℕ) (v : V) :
    F ((x ^ n) v) = (x ^ n) (F v) := by
  induction n generalizing v with
  | zero => simp
  | succ n ih => rw [pow_succ, Module.End.mul_apply, ih, hFx, Module.End.mul_apply]

theorem F_aeval (hF : ∀ (c : K) (v : V), F (c • v) = σ c • F v)
    (hFx : ∀ v, F (x v) = x (F v)) (f : K[X]) (v : V) :
    F (aeval x f v) = aeval x (f.map (σ : K →+* K)) (F v) := by
  induction f using Polynomial.induction_on' with
  | add p q hp hq =>
    simp only [Polynomial.map_add, map_add, LinearMap.add_apply]
    rw [hp, hq]
  | monomial n c =>
    rw [Polynomial.map_monomial, aeval_monomial, aeval_monomial, Module.End.mul_apply,
      Module.End.mul_apply, Module.algebraMap_end_apply, Module.algebraMap_end_apply, hF,
      F_pow_apply F hFx]
    rfl

theorem F_mem_primaryComponent (hF : ∀ (c : K) (v : V), F (c • v) = σ c • F v)
    (hFx : ∀ v, F (x v) = x (F v)) {a : K[X]} {v : V} (hv : v ∈ primaryComponent x a) :
    F v ∈ primaryComponent x (a.map (σ : K →+* K)) := by
  rw [mem_primaryComponent] at hv ⊢
  have h := F_aeval σ F hF hFx a v
  rw [hv, map_zero] at h
  exact h.symm

theorem map_minpoly_eq [FiniteDimensional K V] (hF : ∀ (c : K) (v : V), F (c • v) = σ c • F v)
    (hFx : ∀ v, F (x v) = x (F v)) :
    (minpoly K x).map (σ : K →+* K) = minpoly K x := by
  have hmon : ((minpoly K x).map (σ : K →+* K)).Monic :=
    (minpoly.monic (Algebra.IsIntegral.isIntegral x)).map _
  have hzero : aeval x ((minpoly K x).map (σ : K →+* K)) = 0 := by
    refine LinearMap.ext fun w => ?_
    obtain ⟨v, rfl⟩ := F.surjective w
    have h := F_aeval σ F hF hFx (minpoly K x) v
    rw [minpoly.aeval, LinearMap.zero_apply, map_zero] at h
    rw [LinearMap.zero_apply]
    exact h.symm
  have hdvd : minpoly K x ∣ (minpoly K x).map (σ : K →+* K) := minpoly.dvd K x hzero
  exact eq_of_monic_of_dvd_of_natDegree_le (minpoly.monic (Algebra.IsIntegral.isIntegral x))
    hmon hdvd (by rw [natDegree_map])

end Semilinear

section Factors

variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  {x : Module.End K V}

theorem map_mem_primaryFactors {τ : K ≃+* K}
    (hτ : (minpoly K x).map (τ : K →+* K) = minpoly K x) {a : K[X]} (ha : a ∈ primaryFactors x) :
    a.map (τ : K →+* K) ∈ primaryFactors x := by
  rw [mem_primaryFactors] at ha ⊢
  obtain ⟨hirr, hmon, hdvd⟩ := ha
  refine ⟨?_, hmon.map _, ?_⟩
  · have := (MulEquiv.irreducible_iff (Polynomial.mapEquiv τ)).mpr hirr
    simpa using this
  · have := Polynomial.map_dvd (τ : K →+* K) hdvd
    rwa [hτ] at this

omit [FiniteDimensional K V] in
theorem map_minpoly_eq_of_mem_zpowers {σ : K ≃+* K}
    (hσ : (minpoly K x).map (σ : K →+* K) = minpoly K x) {τ : K ≃+* K}
    (hτ : τ ∈ Subgroup.zpowers σ) : (minpoly K x).map (τ : K →+* K) = minpoly K x := by
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hτ
  have hpos : ∀ m : ℕ, (minpoly K x).map ((σ ^ m : K ≃+* K) : K →+* K) = minpoly K x := by
    intro m
    induction m with
    | zero =>
      have : ((σ ^ 0 : K ≃+* K) : K →+* K) = RingHom.id K := rfl
      rw [this, Polynomial.map_id]
    | succ m ih =>
      have : ((σ ^ (m + 1) : K ≃+* K) : K →+* K) =
          (σ : K →+* K).comp ((σ ^ m : K ≃+* K) : K →+* K) := by
        rw [pow_succ']
        rfl
      rw [this, ← Polynomial.map_map, ih, hσ]
  rcases n with n | n
  · simpa using hpos n
  · have h1 := hpos (n + 1)
    have h2 : ((σ ^ (Int.negSucc n) : K ≃+* K) : K →+* K) =
        (((σ ^ (n + 1) : K ≃+* K)⁻¹ : K ≃+* K) : K →+* K) := by
      rw [zpow_negSucc]
    rw [h2]
    have h3 := congrArg (fun m : K[X] =>
      m.map ((((σ ^ (n + 1) : K ≃+* K)⁻¹ : K ≃+* K)) : K →+* K)) h1
    simp only [Polynomial.map_map] at h3
    have h4 : ((((σ ^ (n + 1) : K ≃+* K)⁻¹ : K ≃+* K)) : K →+* K).comp
        ((σ ^ (n + 1) : K ≃+* K) : K →+* K) = RingHom.id K :=
      RingHom.ext fun c => (σ ^ (n + 1)).symm_apply_apply c
    rw [h4, Polynomial.map_id] at h3
    exact h3.symm

open scoped _root_.Classical in
theorem card_primaryFactors_erase_le {p : ℕ} (hp : p.Prime) (hsq : Squarefree (minpoly K x))
    (hxp : x ^ p = 1) : ((primaryFactors x).erase (X - C 1)).card ≤ p - 1 := by
  classical
  set F := primaryFactors x with hF
  set F' := F.erase (X - C 1) with hF'
  set g : K[X] := ∏ h ∈ F', h with hg
  have hmin : minpoly K x ∣ X ^ p - 1 := minpoly.dvd K x (by simp [hxp])
  have hgdvd : g ∣ X ^ p - 1 := by
    refine dvd_trans ?_ hmin
    rw [← prod_primaryFactors hsq]
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
  have hdeg : 1 + g.natDegree ≤ p := by
    have h1 := natDegree_le_of_dvd hprod hX0
    rw [natDegree_mul (X_sub_C_ne_zero 1) hg0, natDegree_X_sub_C] at h1
    have h2 : (X ^ p - 1 : K[X]).natDegree = p := by
      simpa using natDegree_X_pow_sub_C (n := p) (r := (1 : K))
    omega
  have hsum : F'.card * 1 ≤ g.natDegree := by
    have h1 := Finset.card_nsmul_le_sum F' (fun h => h.natDegree) 1 fun h hh =>
      (irreducible_of_mem_primaryFactors (Finset.mem_of_mem_erase hh)).natDegree_pos
    rw [smul_eq_mul] at h1
    rw [hg, natDegree_prod _ _ fun h hh =>
      (irreducible_of_mem_primaryFactors (Finset.mem_of_mem_erase hh)).ne_zero]
    exact h1
  omega

theorem map_eq_self_of_pow_eq_one [Finite K] {p : ℕ} (hp : p.Prime)
    (hsq : Squarefree (minpoly K x)) (hxp : x ^ p = 1) {σ : K ≃+* K} {j : ℕ}
    (hσj : σ ^ p ^ j = 1) (hσ : (minpoly K x).map (σ : K →+* K) = minpoly K x) {a : K[X]}
    (ha : a ∈ primaryFactors x) : a.map (σ : K →+* K) = a := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  by_cases ha1 : a = X - C 1
  · rw [ha1, Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C]
    simp
  set G : Subgroup (K ≃+* K) := Subgroup.zpowers σ with hG
  have hGp : IsPGroup p G := by
    refine IsPGroup.of_card_dvd_pow (n := j) ?_
    rw [hG, Nat.card_zpowers]
    exact orderOf_dvd_of_pow_eq_one hσj
  have hsmul : ∀ (τ : G) (f : K[X]), τ • f = f.map ((τ : K ≃+* K) : K →+* K) := fun τ f => by
    rw [Polynomial.smul_eq_map K τ]
    rfl
  have hsub : MulAction.orbit G a ⊆ ((primaryFactors x).erase (X - C 1) : Set K[X]) := by
    rintro _ ⟨τ, rfl⟩
    have hτ := map_minpoly_eq_of_mem_zpowers hσ τ.2
    show τ • a ∈ _
    rw [hsmul]
    refine Finset.mem_coe.mpr (Finset.mem_erase.mpr ⟨?_, map_mem_primaryFactors hτ ha⟩)
    intro h1
    apply ha1
    have h3 := congrArg (Polynomial.map (((τ : K ≃+* K).symm : K ≃+* K) : K →+* K)) h1
    rw [Polynomial.map_map] at h3
    have h4 : (((τ : K ≃+* K).symm : K ≃+* K) : K →+* K).comp ((τ : K ≃+* K) : K →+* K) =
        RingHom.id K := RingHom.ext fun c => (τ : K ≃+* K).symm_apply_apply c
    rw [h4, Polynomial.map_id, Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C] at h3
    simpa using h3
  have hfin : (MulAction.orbit G a).Finite :=
    (Finset.finite_toSet _).subset hsub
  have := hfin.to_subtype
  obtain ⟨n, hn⟩ := hGp.card_orbit a
  have hle : Nat.card (MulAction.orbit G a) ≤ p - 1 := by
    calc Nat.card (MulAction.orbit G a) ≤ Nat.card
          (((primaryFactors x).erase (X - C 1) : Finset K[X]) : Set K[X]) :=
        Nat.card_mono (Finset.finite_toSet _) hsub
      _ = ((primaryFactors x).erase (X - C 1)).card := by
        rw [Nat.card_coe_set_eq, Set.ncard_coe_finset]
      _ ≤ p - 1 := card_primaryFactors_erase_le hp hsq hxp
  have hn0 : n = 0 := by
    by_contra hne
    have : p ≤ p ^ n := Nat.le_self_pow hne p
    have := hp.two_le
    omega
  rw [hn0, pow_zero, Nat.card_eq_one_iff_unique] at hn
  obtain ⟨hsing, -⟩ := hn
  have h1 : (⟨(⟨σ, Subgroup.mem_zpowers σ⟩ : G) • a, ⟨_, rfl⟩⟩ :
      MulAction.orbit G a) = ⟨a, MulAction.mem_orbit_self a⟩ := hsing.elim _ _
  have h2 : (⟨σ, Subgroup.mem_zpowers σ⟩ : G) • a = a := congrArg Subtype.val h1
  rw [hsmul] at h2
  exact h2

end Factors

end CFSG.RankThree.PartOne.KCOrthComm

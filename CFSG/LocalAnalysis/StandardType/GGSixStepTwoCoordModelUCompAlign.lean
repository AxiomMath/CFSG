module

public import CFSG.LocalAnalysis.StandardType.GGSixStepTwoCoordModelUCompRoots

public section

namespace CFSG.StandardType

namespace CoordSU

open Matrix Module Polynomial CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag
  CFSG.LinearGroups SUTB NoOffOm NsFrameComp CFSG.RankThree.PartOne.KCPrimary
  CFSG.RankThree.PartOne.KCUnitary Multiplicative

section Linear

variable {K : Type} [Field K] {V : Type} [AddCommGroup V] [Module K V]

theorem pow_apply_mem {T : Module.End K V} {U : Submodule K V} (hTU : ∀ u ∈ U, T u ∈ U) (N : ℕ)
    {u : V} (hu : u ∈ U) : (T ^ N) u ∈ U := by
  induction N with
  | zero => simpa using hu
  | succ N ih =>
    rw [pow_succ', Module.End.mul_apply]
    exact hTU _ ih

theorem aeval_apply_comp_pow {T₁ T₂ θ : Module.End K V} {U : Submodule K V}
    (hTU : ∀ u ∈ U, T₂ u ∈ U) (m : ℕ) (hT : ∀ u ∈ U, T₁ (θ u) = θ ((T₂ ^ m) u)) (Q : K[X])
    {u : V} (hu : u ∈ U) : aeval T₁ Q (θ u) = θ (aeval T₂ (Q.comp (X ^ m)) u) := by
  have hpow : ∀ N : ℕ, ∀ u ∈ U, (T₁ ^ N) (θ u) = θ ((T₂ ^ (m * N)) u) := by
    intro N
    induction N with
    | zero => intro u _; simp
    | succ N ih =>
      intro u hu
      rw [pow_succ, Module.End.mul_apply, hT u hu, ih _ (pow_apply_mem hTU m hu)]
      congr 1
      rw [← Module.End.mul_apply, ← pow_add, Nat.mul_succ]
  induction Q using Polynomial.induction_on' with
  | add P R hP hR => rw [map_add, LinearMap.add_apply, hP, hR, add_comp, map_add,
      LinearMap.add_apply, map_add]
  | monomial N c =>
    rw [← C_mul_X_pow_eq_monomial, mul_comp, C_comp, X_pow_comp, ← pow_mul, map_mul, map_mul,
      aeval_C, aeval_C, map_pow, map_pow, aeval_X, aeval_X, Module.End.mul_apply,
      Module.End.mul_apply, hpow N u hu, Module.algebraMap_end_apply,
      Module.algebraMap_end_apply, map_smul]

theorem coe_aeval_restrict {T : Module.End K V} {U : Submodule K V} (hTU : ∀ u ∈ U, T u ∈ U)
    (Q : K[X]) (u : U) : ((aeval (T.restrict hTU) Q u : U) : V) = aeval T Q (u : V) := by
  have hpow : ∀ N : ℕ, (((T.restrict hTU) ^ N) u : V) = (T ^ N) (u : V) := by
    intro N
    induction N generalizing u with
    | zero => rfl
    | succ N ih =>
      rw [pow_succ, pow_succ, Module.End.mul_apply, Module.End.mul_apply, ih]
      rfl
  induction Q using Polynomial.induction_on' with
  | add P R hP hR => simp [hP, hR]
  | monomial N c => simp [aeval_monomial, hpow]

theorem exists_root_of_restrict [FiniteDimensional K V] {T : Module.End K V} {U : Submodule K V}
    (hTU : ∀ u ∈ U, T u ∈ U) (hU : U ≠ ⊥) {R₁ R₂ R₃ : K[X]}
    (h₁ : ∀ u ∈ U, aeval T R₁ u = 0) (h₂ : ∀ u ∈ U, aeval T R₂ u = 0)
    (h₃ : ∀ u ∈ U, aeval T R₃ u = 0) :
    ∃ ν : AlgebraicClosure K, aeval ν R₁ = 0 ∧ aeval ν R₂ = 0 ∧ aeval ν R₃ = 0 := by
  set T' := T.restrict hTU with hT'
  have hzero : ∀ R : K[X], (∀ u ∈ U, aeval T R u = 0) → aeval T' R = 0 := by
    intro R hR
    ext u
    rw [coe_aeval_restrict hTU R u]
    exact hR u u.2
  have : Nontrivial U := Submodule.nontrivial_iff_ne_bot.mpr hU
  have hint : IsIntegral K T' := Algebra.IsIntegral.isIntegral T'
  have hdeg : (minpoly K T').degree ≠ 0 := by
    have := minpoly.natDegree_pos hint
    rw [degree_eq_natDegree (minpoly.ne_zero hint)]
    exact_mod_cast this.ne'
  obtain ⟨ν, hν⟩ := IsAlgClosed.exists_aeval_eq_zero_of_injective (k := AlgebraicClosure K)
    (algebraMap K (AlgebraicClosure K)).injective (minpoly K T') hdeg
  have hroot : ∀ R : K[X], (∀ u ∈ U, aeval T R u = 0) → aeval ν R = 0 := by
    intro R hR
    obtain ⟨g, hg⟩ := minpoly.dvd K T' (hzero R hR)
    rw [hg, map_mul, hν, zero_mul]
  exact ⟨ν, hroot R₁ h₁, hroot R₂ h₂, hroot R₃ h₃⟩

end Linear

section Cyclotomic

variable {K E : Type} [Field K] [Field E] [Algebra K E] {p : ℕ}

theorem aeval_one_ne_zero_of_dvd (hp : p.Prime) (hpK : (p : K) ≠ 0) {c : K[X]}
    (hcd : c ∣ cyclotomic p K) : aeval (1 : E) c ≠ 0 := by
  have : Fact p.Prime := ⟨hp⟩
  intro h0
  obtain ⟨g, hg⟩ := hcd
  have h1 : aeval (algebraMap K E 1) (cyclotomic p K) = 0 := by
    rw [map_one, hg, map_mul, h0, zero_mul]
  rw [aeval_algebraMap_apply_eq_algebraMap_eval, eval_one_cyclotomic_prime,
    map_eq_zero_iff _ (algebraMap K E).injective] at h1
  exact hpK h1

theorem exists_isPrimitiveRoot [IsAlgClosed E] (hp : p.Prime) (hpE : (p : E) ≠ 0) :
    ∃ ζ : E, IsPrimitiveRoot ζ p := by
  have : Fact p.Prime := ⟨hp⟩
  have : NeZero (p : E) := ⟨hpE⟩
  have hdeg : (cyclotomic p E).degree ≠ 0 := by
    rw [degree_cyclotomic, Nat.totient_prime hp]
    have := hp.two_le
    norm_cast
    omega
  obtain ⟨ζ, hζ⟩ := IsAlgClosed.exists_root (cyclotomic p E) hdeg
  exact ⟨ζ, (isRoot_cyclotomic_iff).mp hζ⟩

end Cyclotomic

end CoordSU

end CFSG.StandardType

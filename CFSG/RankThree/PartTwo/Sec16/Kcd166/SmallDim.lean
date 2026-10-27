module

public import Mathlib.LinearAlgebra.Eigenspace.Charpoly
public import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
public import Mathlib.RepresentationTheory.Irreducible
public import CFSG.RankThree.PartTwo.KFacts.KS116LinRep
public import CFSG.ThirdParty.QiuzhenCFSG.Theory.Representation.SubrepresentationLattice
public import Mathlib.GroupTheory.IsPerfect

public section

namespace CFSG.RankThree.PartTwo.Sec16.Kcd166

open Polynomial
open CFSG.RankThree.PartTwo.KFacts.NDC

theorem eq_one_of_sub_one_mul_sub_one_eq_zero {𝕜 : Type*} [Field 𝕜] {W : Type*}
    [AddCommGroup W] [Module 𝕜 W] {f : Module.End 𝕜 W} (hf : (f - 1) * (f - 1) = 0) {n : ℕ}
    (hn : f ^ n = 1) (hn0 : (n : 𝕜) ≠ 0) : f = 1 := by
  set N : Module.End 𝕜 W := f - 1 with hN
  have hN2 : N * N = 0 := by simpa [hN] using hf
  have hf_eq : f = 1 + N := by rw [hN]; abel
  have hpow : ∀ k : ℕ, (1 + N) ^ k = 1 + k • N := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ, ih]
      have hsm : (k • N) * N = 0 := by
        rw [← Nat.cast_smul_eq_nsmul 𝕜 k N, smul_mul_assoc, hN2, smul_zero]
      calc
        (1 + k • N) * (1 + N) = 1 + N + k • N + (k • N) * N := by
          rw [add_mul, one_mul, mul_add, mul_one]
          abel
        _ = 1 + N + k • N := by rw [hsm, add_zero]
        _ = 1 + (k + 1) • N := by
          rw [add_assoc, add_comm N (k • N), ← succ_nsmul]
  have hfk : (1 + N) ^ n = 1 := by rw [← hf_eq]; exact hn
  rw [hpow n] at hfk
  have hnsmul : n • N = 0 := by
    have h : 1 + n • N = 1 + (0 : Module.End 𝕜 W) := by simpa using hfk
    exact add_left_cancel h
  have hscalar : (n : 𝕜) • N = 0 := by rw [Nat.cast_smul_eq_nsmul 𝕜, hnsmul]
  have hN0 : N = 0 := (smul_eq_zero.mp hscalar).resolve_left hn0
  rw [hf_eq, hN0, add_zero]


private lemma sub_one_sq_eq_zero_of_det_eq_one_of_hasEigenvalue_one
    {𝕜 : Type*} [Field 𝕜] {W : Type*} [AddCommGroup W] [Module 𝕜 W]
    [FiniteDimensional 𝕜 W] {F : Module.End 𝕜 W} (hW : Module.finrank 𝕜 W = 2)
    (hdet : LinearMap.det F = 1) (h : F.HasEigenvalue 1) :
    (F - 1) * (F - 1) = 0 := by
  let b := Module.finBasisOfFinrankEq 𝕜 W hW
  let M : Matrix (Fin 2) (Fin 2) 𝕜 := LinearMap.toMatrix b b F
  have hMdet : M.det = 1 := by simpa [M] using hdet
  have hrootF : F.charpoly.IsRoot 1 :=
    (Module.End.hasEigenvalue_iff_isRoot_charpoly F 1).mp h
  have hroot : M.charpoly.IsRoot 1 := by
    dsimp only [M]
    rw [LinearMap.charpoly_toMatrix F b]
    exact hrootF
  have hMchar : M.charpoly = Polynomial.X ^ 2 - Polynomial.C M.trace * Polynomial.X +
      Polynomial.C M.det := Matrix.charpoly_fin_two M
  have htrace : M.trace = 2 := by
    have h' := hroot
    rw [Polynomial.IsRoot.def, hMchar, hMdet] at h'
    simp only [Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_mul,
      Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C, Polynomial.eval_one,
      map_one, one_pow, mul_one] at h'
    linear_combination -h'
  have hcharF : F.charpoly = (Polynomial.X - Polynomial.C 1 : 𝕜[X]) ^ 2 := by
    rw [← LinearMap.charpoly_toMatrix F b, hMchar, hMdet, htrace]
    simp only [map_one, map_ofNat]
    ring
  have haeval : aeval F ((Polynomial.X - Polynomial.C 1 : 𝕜[X]) ^ 2) = 0 := by
    rw [← hcharF]
    exact LinearMap.aeval_self_charpoly F
  have hX : aeval F (Polynomial.X - Polynomial.C 1 : 𝕜[X]) = F - 1 := by
    simp [map_sub, aeval_X, Algebra.algebraMap_eq_smul_one]
  calc
    (F - 1) * (F - 1) = (F - 1) ^ 2 := by rw [pow_two]
    _ = (aeval F (Polynomial.X - Polynomial.C 1 : 𝕜[X])) ^ 2 := by rw [hX]
    _ = aeval F ((Polynomial.X - Polynomial.C 1 : 𝕜[X]) ^ 2) := by rw [map_pow]
    _ = 0 := haeval

private lemma ker_aeval_X_sub_C {𝕜 W : Type*} [Field 𝕜] [AddCommGroup W] [Module 𝕜 W]
    (F : Module.End 𝕜 W) (μ : 𝕜) :
    LinearMap.ker (aeval F (Polynomial.X - Polynomial.C μ)) = F.eigenspace μ := by
  rw [Module.End.eigenspace_def]
  congr 1
  simp [map_sub, aeval_X, Algebra.algebraMap_eq_smul_one]

private lemma isCoprime_X_sub_one_X_sq_add_X_add_one {𝕜 : Type*} [Field 𝕜]
    (h3 : (3 : 𝕜) ≠ 0) :
    IsCoprime (Polynomial.X - Polynomial.C 1 : 𝕜[X])
      (Polynomial.X ^ 2 + Polynomial.X + 1 : 𝕜[X]) := by
  refine isRelPrime_iff_isCoprime.mp ?_
  intro d hd1 hd2
  have hcomb : d ∣ -(3 : 𝕜[X]) := by
    have h : (Polynomial.X + Polynomial.C 2) * (Polynomial.X - Polynomial.C 1) -
        (Polynomial.X ^ 2 + Polynomial.X + 1 : 𝕜[X]) = -(3 : 𝕜[X]) := by
      simp only [map_ofNat, map_one]
      ring
    rw [← h]
    exact dvd_sub (dvd_mul_of_dvd_right hd1 _) hd2
  have hd3 : d ∣ (3 : 𝕜[X]) := dvd_neg.mp hcomb
  have h3unit : IsUnit (3 : 𝕜[X]) :=
    isUnit_C.mpr (isUnit_iff_ne_zero.mpr h3)
  exact isUnit_of_dvd_unit hd3 h3unit

private lemma isCompl_eigenspaces_of_quadratic {𝕜 W : Type*} [Field 𝕜] [AddCommGroup W]
    [Module 𝕜 W] (F : Module.End 𝕜 W) {a μ : 𝕜} (hquad : F ^ 2 + F + 1 = 0)
    (hne : a ≠ μ)
    (hprod : (Polynomial.X - Polynomial.C a) * (Polynomial.X - Polynomial.C μ) =
      (Polynomial.X ^ 2 + Polynomial.X + 1 : 𝕜[X])) :
    IsCompl (F.eigenspace a) (F.eigenspace μ) := by
  have hcop : IsCoprime (Polynomial.X - Polynomial.C a) (Polynomial.X - Polynomial.C μ) :=
    isCoprime_X_sub_C_of_isUnit_sub (sub_ne_zero.mpr hne).isUnit
  have hdis : Disjoint (F.eigenspace a) (F.eigenspace μ) := by
    rw [← ker_aeval_X_sub_C, ← ker_aeval_X_sub_C]
    exact disjoint_ker_aeval_of_isCoprime F hcop
  have hsup : F.eigenspace a ⊔ F.eigenspace μ = ⊤ := by
    rw [← ker_aeval_X_sub_C, ← ker_aeval_X_sub_C,
      sup_ker_aeval_eq_ker_aeval_mul_of_coprime F hcop, hprod]
    have hzero : aeval F (Polynomial.X ^ 2 + Polynomial.X + 1 : 𝕜[X]) = 0 := by
      simpa [map_add, map_pow, aeval_X, map_one, Algebra.algebraMap_eq_smul_one] using hquad
    rw [hzero, LinearMap.ker_zero]
  exact isCompl_iff.mpr ⟨hdis, codisjoint_iff.mpr hsup⟩


private lemma det_eq_one_of_perfect {𝕜 G W : Type*} [Field 𝕜] [Group G]
    [AddCommGroup W] [Module 𝕜 W] (hperf : Group.IsPerfect G)
    (σ : Representation 𝕜 G W) : ∀ g : G, LinearMap.det (σ g) = 1 := by
  let δ : G →* 𝕜ˣ :=
    (Units.map (LinearMap.det : Module.End 𝕜 W →* 𝕜)).comp σ.asGroupHom
  have hker : commutator G ≤ δ.ker := Abelianization.commutator_subset_ker δ
  rw [hperf.commutator_eq_top] at hker
  intro g
  have h1 : δ g = 1 := MonoidHom.mem_ker.mp (hker (Subgroup.mem_top g))
  have h2 : (δ g : 𝕜) = 1 := by rw [h1, Units.val_one]
  simpa [δ, Representation.asGroupHom_apply] using h2

private lemma exists_central_order_three {P : Type*} [Group P] [Finite P]
    (hP : IsPGroup 3 P) (hnt : Nontrivial P) :
    ∃ z : P, z ∈ Subgroup.center P ∧ orderOf z = 3 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hcP : IsPGroup 3 (Subgroup.center P) := hP.to_subgroup (Subgroup.center P)
  haveI : Nontrivial (Subgroup.center P) := hP.center_nontrivial
  have hcard_gt : 1 < Nat.card (Subgroup.center P) :=
    Finite.one_lt_card_iff_nontrivial.mpr inferInstance
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hcP
  have hn0 : n ≠ 0 := by
    rintro rfl
    rw [pow_zero] at hn
    omega
  have h3dvd : 3 ∣ Nat.card (Subgroup.center P) := by
    rw [hn]
    exact dvd_pow_self 3 hn0
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := Subgroup.center P) 3 h3dvd
  refine ⟨z, z.2, ?_⟩
  rw [Subgroup.orderOf_coe]
  exact hz


private lemma quadratic_of_cube_one_of_no_fixed {𝕜 W : Type*} [Field 𝕜] [AddCommGroup W]
    [Module 𝕜 W] (h3 : (3 : 𝕜) ≠ 0) {F : Module.End 𝕜 W} (hF3 : F ^ 3 = 1)
    (hbot : F.eigenspace 1 = ⊥) : F ^ 2 + F + 1 = 0 := by
  have hcop := isCoprime_X_sub_one_X_sq_add_X_add_one h3
  have hsup := sup_ker_aeval_eq_ker_aeval_mul_of_coprime F hcop
  have hker1 : LinearMap.ker (aeval F (Polynomial.X - Polynomial.C 1 : 𝕜[X])) = ⊥ := by
    rw [ker_aeval_X_sub_C]
    exact hbot
  have hprod : (Polynomial.X - Polynomial.C 1) *
      (Polynomial.X ^ 2 + Polynomial.X + 1 : 𝕜[X]) = Polynomial.X ^ 3 - 1 := by
    simp only [map_one, map_ofNat]
    ring
  rw [hker1, hprod] at hsup
  have hzero : aeval F (Polynomial.X ^ 3 - 1 : 𝕜[X]) = 0 := by
    simp [map_sub, map_pow, aeval_X, hF3]
  rw [hzero, LinearMap.ker_zero, bot_sup_eq] at hsup
  have hqzero : aeval F (Polynomial.X ^ 2 + Polynomial.X + 1 : 𝕜[X]) = 0 := by
    rw [← LinearMap.ker_eq_top]
    exact hsup
  simpa [pow_two, map_add, map_pow, aeval_X, map_one, Algebra.algebraMap_eq_smul_one]
    using hqzero


private lemma exists_eigenvalue_quadratic {𝕜 W : Type*} [Field 𝕜] [IsAlgClosed 𝕜]
    [AddCommGroup W] [Module 𝕜 W] [FiniteDimensional 𝕜 W] (h3 : (3 : 𝕜) ≠ 0)
    {F : Module.End 𝕜 W} (hW : Module.finrank 𝕜 W = 2) (hquad : F ^ 2 + F + 1 = 0) :
    ∃ a : 𝕜, a ≠ 1 ∧ a ^ 2 + a + 1 = 0 ∧ a ^ 3 = 1 ∧ F.eigenspace a ≠ ⊥ := by
  haveI : Nontrivial W := Module.finrank_pos_iff.mp (by rw [hW]; norm_num)
  obtain ⟨a, haeig⟩ := Module.End.exists_eigenvalue F
  obtain ⟨v, hv⟩ := haeig.exists_hasEigenvector
  have haquad : a ^ 2 + a + 1 = 0 := by
    have h1 : (F ^ 2 + F + 1 : Module.End 𝕜 W) v = 0 := by rw [hquad, LinearMap.zero_apply]
    have h2 : (F ^ 2 + F + 1 : Module.End 𝕜 W) v = (a ^ 2 + a + 1) • v := by
      calc
        (F ^ 2 + F + 1 : Module.End 𝕜 W) v = F (F v) + F v + v := by
          simp [pow_two, LinearMap.add_apply, Module.End.one_apply]
        _ = F (a • v) + a • v + v := by rw [hv.apply_eq_smul]
        _ = a • (a • v) + a • v + v := by rw [map_smul, hv.apply_eq_smul]
        _ = (a ^ 2 + a + 1) • v := by
          simp only [smul_smul]
          module
    rw [h2] at h1
    exact (smul_eq_zero.mp h1).resolve_right hv.2
  have ha1 : a ≠ 1 := by
    intro h
    rw [h] at haquad
    have h3zero : (3 : 𝕜) = 0 := by
      norm_num at haquad ⊢
      exact haquad
    exact h3 h3zero
  have ha3 : a ^ 3 = 1 := by
    have h : a ^ 3 - 1 = (a - 1) * (a ^ 2 + a + 1) := by ring
    rw [haquad, mul_zero] at h
    linear_combination h
  exact ⟨a, ha1, haquad, ha3, Module.End.hasEigenvalue_iff.mp haeig⟩

private lemma exists_other_root_and_compl {𝕜 W : Type*} [Field 𝕜] [AddCommGroup W]
    [Module 𝕜 W] {F : Module.End 𝕜 W} {a : 𝕜} (hquad : F ^ 2 + F + 1 = 0)
    (ha1 : a ≠ 1) (haquad : a ^ 2 + a + 1 = 0) (ha3 : a ^ 3 = 1) :
    ∃ μ : 𝕜, a ≠ μ ∧ μ ^ 2 + μ + 1 = 0 ∧ μ = a ^ 2 ∧ a * μ = 1 ∧
      IsCompl (F.eigenspace a) (F.eigenspace μ) := by
  let μ : 𝕜 := -1 - a
  have hμquad : μ ^ 2 + μ + 1 = 0 := by
    dsimp [μ]
    linear_combination haquad
  have hμeq : μ = a ^ 2 := by
    dsimp [μ]
    linear_combination -haquad
  have hne : a ≠ μ := by
    intro h
    have haa : a = a ^ 2 := by rw [← hμeq, h]
    have hfac : a * (a - 1) = 0 := by
      calc
        a * (a - 1) = a ^ 2 - a := by ring
        _ = 0 := by rw [← haa, sub_self]
    rcases mul_eq_zero.mp hfac with h0 | h1
    · rw [h0] at haquad
      norm_num at haquad
    · exact ha1 (sub_eq_zero.mp h1)
  have hsum : a + μ = -1 := by dsimp [μ]; ring
  have hmul : a * μ = 1 := by
    rw [hμeq]
    calc
      a * a ^ 2 = a ^ 3 := by ring
      _ = 1 := ha3
  have hprod : (Polynomial.X - Polynomial.C a) * (Polynomial.X - Polynomial.C μ) =
      (Polynomial.X ^ 2 + Polynomial.X + 1 : 𝕜[X]) := by
    rw [show (Polynomial.X - Polynomial.C a) * (Polynomial.X - Polynomial.C μ) =
        Polynomial.X ^ 2 - Polynomial.C (a + μ) * Polynomial.X +
          Polynomial.C (a * μ) by
      simp only [map_add, map_mul]
      ring]
    rw [hsum, hmul]
    simp [map_neg, map_one]
  exact ⟨μ, hne, hμquad, hμeq, hmul,
    isCompl_eigenspaces_of_quadratic F hquad hne hprod⟩

private lemma eigenspace_other_ne_bot {𝕜 W : Type*} [Field 𝕜] [AddCommGroup W]
    [Module 𝕜 W] (h3 : (3 : 𝕜) ≠ 0) {F : Module.End 𝕜 W}
    (hW : Module.finrank 𝕜 W = 2) (hquad : F ^ 2 + F + 1 = 0)
    (hdet : LinearMap.det F = 1) {a μ : 𝕜} (hμeq : μ = a ^ 2)
    (hμquad : μ ^ 2 + μ + 1 = 0)
    (hcompl : IsCompl (F.eigenspace a) (F.eigenspace μ)) : F.eigenspace μ ≠ ⊥ := by
  intro hbot
  have haTop : F.eigenspace a = ⊤ := by
    have h := hcompl.sup_eq_top
    rwa [hbot, sup_bot_eq] at h
  have hFscalar : F = a • 1 := by
    ext x
    have hx : x ∈ F.eigenspace a := by rw [haTop]; trivial
    simpa using Module.End.mem_eigenspace_iff.mp hx
  have hdet_scalar : LinearMap.det F = a ^ 2 := by
    rw [hFscalar, LinearMap.det_smul, map_one, mul_one, hW]
  have ha2 : a ^ 2 = 1 := by
    rw [hdet_scalar] at hdet
    exact hdet
  have hμ1 : μ = 1 := by rw [hμeq, ha2]
  have h3zero : (3 : 𝕜) = 0 := by
    rw [hμ1] at hμquad
    norm_num at hμquad ⊢
    exact hμquad
  exact h3 h3zero

private lemma exists_eigenvalue_pair_of_quadratic {𝕜 W : Type*} [Field 𝕜] [IsAlgClosed 𝕜]
    [AddCommGroup W] [Module 𝕜 W] [FiniteDimensional 𝕜 W] (h3 : (3 : 𝕜) ≠ 0)
    {F : Module.End 𝕜 W} (hW : Module.finrank 𝕜 W = 2) (hquad : F ^ 2 + F + 1 = 0)
    (hdet : LinearMap.det F = 1) :
    ∃ a μ : 𝕜, a ≠ 1 ∧ a ≠ μ ∧ a ^ 2 + a + 1 = 0 ∧ μ ^ 2 + μ + 1 = 0 ∧
      a * μ = 1 ∧ F.eigenspace a ≠ ⊥ ∧ F.eigenspace μ ≠ ⊥ ∧
      IsCompl (F.eigenspace a) (F.eigenspace μ) := by
  obtain ⟨a, ha1, haquad, ha3, hEa⟩ := exists_eigenvalue_quadratic h3 hW hquad
  obtain ⟨μ, hne, hμquad, hμeq, hmul, hcompl⟩ :=
    exists_other_root_and_compl hquad ha1 haquad ha3
  have hEμ : F.eigenspace μ ≠ ⊥ :=
    eigenspace_other_ne_bot h3 hW hquad hdet hμeq hμquad hcompl
  exact ⟨a, μ, ha1, hne, haquad, hμquad, hmul, hEa, hEμ, hcompl⟩

private lemma linearIndependent_eigenbasis_pair {𝕜 W : Type*} [Field 𝕜] [AddCommGroup W]
    [Module 𝕜 W] {F : Module.End 𝕜 W} {a μ : 𝕜} (hne : a ≠ μ) {m₁ m₂ : W}
    (hm₁mem : m₁ ∈ F.eigenspace a) (hm₂mem : m₂ ∈ F.eigenspace μ)
    (hm₁W : m₁ ≠ 0) (hm₂W : m₂ ≠ 0) : LinearIndependent 𝕜 ![m₁, m₂] := by
  rw [LinearIndependent.pair_iff]
  intro s t hst
  have h2 : (F - a • 1) (s • m₁ + t • m₂) = 0 := by rw [hst, map_zero]
  have hm₁ : (F - a • 1) m₁ = 0 := by
    rw [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply,
      Module.End.mem_eigenspace_iff.mp hm₁mem, sub_self]
  have hm₂ : (F - a • 1) m₂ = (μ - a) • m₂ := by
    rw [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply,
      Module.End.mem_eigenspace_iff.mp hm₂mem, ← sub_smul]
  rw [map_add, map_smul, map_smul, hm₁, hm₂, smul_zero, zero_add, smul_smul] at h2
  have hμa : μ - a ≠ 0 := sub_ne_zero.mpr (Ne.symm hne)
  have ht : t = 0 := by
    by_contra ht0
    have hcoef : t * (μ - a) ≠ 0 := mul_ne_zero ht0 hμa
    exact hm₂W ((smul_eq_zero.mp h2).resolve_left hcoef)
  subst ht
  have hs : s = 0 := by
    have hst' : s • m₁ = 0 := by simpa using hst
    exact (smul_eq_zero.mp hst').resolve_right hm₁W
  exact ⟨hs, rfl⟩

private lemma exists_eigenbasis_of_isCompl {𝕜 W : Type*} [Field 𝕜] [AddCommGroup W]
    [Module 𝕜 W] [FiniteDimensional 𝕜 W] {F : Module.End 𝕜 W}
    (hW : Module.finrank 𝕜 W = 2) {a μ : 𝕜} (hne : a ≠ μ)
    (hcompl : IsCompl (F.eigenspace a) (F.eigenspace μ))
    (hEa : F.eigenspace a ≠ ⊥) (hEμ : F.eigenspace μ ≠ ⊥) :
    ∃ m₁ m₂ : W, m₁ ≠ 0 ∧ m₂ ≠ 0 ∧
      (∀ x : W, x ∈ F.eigenspace a → ∃ c : 𝕜, c • m₁ = x) ∧
      (∀ x : W, x ∈ F.eigenspace μ → ∃ c : 𝕜, c • m₂ = x) ∧
      LinearIndependent 𝕜 ![m₁, m₂] ∧ F m₁ = a • m₁ ∧ F m₂ = μ • m₂ := by
  have hsum := Submodule.finrank_add_eq_of_isCompl hcompl
  have h1a : 1 ≤ Module.finrank 𝕜 (F.eigenspace a) :=
    Submodule.one_le_finrank_iff.mpr hEa
  have h1μ : 1 ≤ Module.finrank 𝕜 (F.eigenspace μ) :=
    Submodule.one_le_finrank_iff.mpr hEμ
  rw [hW] at hsum
  have hfa : Module.finrank 𝕜 (F.eigenspace a) = 1 := by omega
  have hfμ : Module.finrank 𝕜 (F.eigenspace μ) = 1 := by omega
  obtain ⟨m₁, hm₁0, hm₁span⟩ := _root_.finrank_eq_one_iff'.mp hfa
  obtain ⟨m₂, hm₂0, hm₂span⟩ := _root_.finrank_eq_one_iff'.mp hfμ
  have hm₁W : (m₁ : W) ≠ 0 := fun h => hm₁0 (Subtype.ext h)
  have hm₂W : (m₂ : W) ≠ 0 := fun h => hm₂0 (Subtype.ext h)
  have hli := linearIndependent_eigenbasis_pair hne m₁.2 m₂.2 hm₁W hm₂W
  refine ⟨m₁, m₂, hm₁W, hm₂W, ?_, ?_, hli, ?_, ?_⟩
  · intro x hx
    obtain ⟨c, hc⟩ := hm₁span ⟨x, hx⟩
    exact ⟨c, congrArg Subtype.val hc⟩
  · intro x hx
    obtain ⟨c, hc⟩ := hm₂span ⟨x, hx⟩
    exact ⟨c, congrArg Subtype.val hc⟩
  · exact Module.End.mem_eigenspace_iff.mp m₁.2
  · exact Module.End.mem_eigenspace_iff.mp m₂.2

private lemma mapsTo_eigenspace_of_commute {𝕜 W : Type*} [Field 𝕜] [AddCommGroup W]
    [Module 𝕜 W] {F G : Module.End 𝕜 W} {a : 𝕜} (hcomm : F * G = G * F) {m : W}
    (hm : F m = a • m) : G m ∈ F.eigenspace a := by
  rw [Module.End.mem_eigenspace_iff]
  calc
    F (G m) = (F * G) m := rfl
    _ = (G * F) m := by rw [hcomm]
    _ = G (F m) := rfl
    _ = G (a • m) := by rw [hm]
    _ = a • G m := by rw [map_smul]

private lemma coefficient_ne_zero_of_injective {𝕜 W : Type*} [Field 𝕜] [AddCommGroup W]
    [Module 𝕜 W] {G : Module.End 𝕜 W} (hG : Function.Injective G) {m : W} (hm : m ≠ 0)
    {c : 𝕜} (hc : G m = c • m) : c ≠ 0 := by
  intro h0
  apply hm
  apply hG
  rw [hc, h0, zero_smul, map_zero]

private lemma exists_scaling_of_central_eigenline {𝕜 W P : Type*} [Field 𝕜]
    [AddCommGroup W] [Module 𝕜 W] [Group P] (σ : Representation 𝕜 P W) {z : P}
    (hzmem : z ∈ Subgroup.center P) (F : Module.End 𝕜 W) (hF : F = σ z)
    {a μ : 𝕜} {m₁ m₂ : W} (hli : LinearIndependent 𝕜 ![m₁, m₂])
    (hm₁eig : F m₁ = a • m₁) (hm₂eig : F m₂ = μ • m₂)
    (hm₁ : ∀ x : W, x ∈ F.eigenspace a → ∃ c : 𝕜, c • m₁ = x)
    (hm₂ : ∀ x : W, x ∈ F.eigenspace μ → ∃ c : 𝕜, c • m₂ = x) :
    ∀ p : P, ∃ a₁ a₂ : 𝕜ˣ, σ p m₁ = (a₁ : 𝕜) • m₁ ∧
      σ p m₂ = (a₂ : 𝕜) • m₂ := by
  have hm₁0 : m₁ ≠ 0 := hli.ne_zero 0
  have hm₂0 : m₂ ≠ 0 := hli.ne_zero 1
  have hcomm : ∀ p : P, F * σ p = σ p * F := by
    intro p
    have hzp : z * p = p * z := ((Subgroup.mem_center_iff.mp hzmem) p).symm
    have hmap : σ (z * p) = σ (p * z) := by rw [hzp]
    simpa [hF, map_mul] using hmap
  have hinj : ∀ p : P, Function.Injective (σ p) := by
    intro p x y hxy
    have := congrArg (σ p⁻¹) hxy
    simpa [← map_mul, inv_mul_cancel] using this
  intro p
  obtain ⟨c₁, hc₁⟩ := hm₁ (σ p m₁) (mapsTo_eigenspace_of_commute (hcomm p) hm₁eig)
  obtain ⟨c₂, hc₂⟩ := hm₂ (σ p m₂) (mapsTo_eigenspace_of_commute (hcomm p) hm₂eig)
  have hc₁0 : c₁ ≠ 0 := coefficient_ne_zero_of_injective (hinj p) hm₁0 hc₁.symm
  have hc₂0 : c₂ ≠ 0 := coefficient_ne_zero_of_injective (hinj p) hm₂0 hc₂.symm
  exact ⟨Units.mk0 c₁ hc₁0, Units.mk0 c₂ hc₂0, by simpa using hc₁.symm,
    by simpa using hc₂.symm⟩

private lemma eigenbasis_det_product_eq_one {𝕜 W P : Type*} [Field 𝕜] [AddCommGroup W]
    [Module 𝕜 W] [Group P] [FiniteDimensional 𝕜 W] {ρ : P →* (W ≃ₗ[𝕜] W)}
    (hW : Module.finrank 𝕜 W = 2) (hdet : ∀ p : P, LinearEquiv.det (ρ p) = 1)
    {m₁ m₂ : W} (hli : LinearIndependent 𝕜 ![m₁, m₂]) {a₁ a₂ : P → 𝕜ˣ}
    (h₁ : ∀ p : P, ρ p m₁ = (a₁ p : 𝕜) • m₁)
    (h₂ : ∀ p : P, ρ p m₂ = (a₂ p : 𝕜) • m₂) :
    ∀ p : P, (a₁ p : 𝕜) * (a₂ p : 𝕜) = 1 := by
  let b : Module.Basis (Fin 2) 𝕜 W :=
    basisOfLinearIndependentOfCardEqFinrank' ![m₁, m₂] hli (by simp [hW])
  have hb0 : b 0 = m₁ := by simp [b]
  have hb1 : b 1 = m₂ := by simp [b]
  have e1 : ∀ p, ρ p (b 0) = (a₁ p : 𝕜) • b 0 := fun p => by rw [hb0]; exact h₁ p
  have e2 : ∀ p, ρ p (b 1) = (a₂ p : 𝕜) • b 1 := fun p => by rw [hb1]; exact h₂ p
  intro p
  have h1 := hdet p
  have h2 : LinearMap.det ((ρ p : W ≃ₗ[𝕜] W) : W →ₗ[𝕜] W) = 1 := by
    have := congrArg (fun u : 𝕜ˣ => (u : 𝕜)) h1
    simpa [LinearEquiv.coe_det] using this
  rw [← LinearMap.det_toMatrix b] at h2
  have hmat : LinearMap.toMatrix b b ((ρ p : W ≃ₗ[𝕜] W) : W →ₗ[𝕜] W) =
      Matrix.diagonal ![(a₁ p : 𝕜), (a₂ p : 𝕜)] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [LinearMap.toMatrix_apply, e1, e2, Module.Basis.repr_self, Finsupp.single_apply,
        Matrix.diagonal_apply]
  rw [hmat, Matrix.det_diagonal, Fin.prod_univ_two] at h2
  simpa using h2

private lemma exists_injective_character_of_eigenbasis {𝕜 W P : Type*} [Field 𝕜]
    [AddCommGroup W] [Module 𝕜 W] [Group P] [FiniteDimensional 𝕜 W]
    (ρ : P →* (W ≃ₗ[𝕜] W))
    (hW : Module.finrank 𝕜 W = 2) (hρ : Function.Injective ρ)
    (hdet : ∀ p : P, LinearEquiv.det (ρ p) = 1) {m₁ m₂ : W}
    (hli : LinearIndependent 𝕜 ![m₁, m₂])
    (heig : ∀ p : P, ∃ a₁ a₂ : 𝕜ˣ, ρ p m₁ = (a₁ : 𝕜) • m₁ ∧
      ρ p m₂ = (a₂ : 𝕜) • m₂) :
    ∃ f : P →* 𝕜ˣ, Function.Injective f := by
  classical
  have hm₁ : m₁ ≠ 0 := by simpa using hli.ne_zero 0
  choose a₁ a₂ h₁ h₂ using heig
  have hcancel : ∀ a b : 𝕜ˣ, (a : 𝕜) • m₁ = (b : 𝕜) • m₁ → a = b :=
    fun a b h => Units.ext (smul_left_injective 𝕜 hm₁ h)
  have hdet' := eigenbasis_det_product_eq_one hW hdet hli h₁ h₂
  let b : Module.Basis (Fin 2) 𝕜 W :=
    basisOfLinearIndependentOfCardEqFinrank' ![m₁, m₂] hli (by simp [hW])
  have hb0 : b 0 = m₁ := by simp [b]
  have hb1 : b 1 = m₂ := by simp [b]
  have e1 : ∀ p, ρ p (b 0) = (a₁ p : 𝕜) • b 0 := fun p => by rw [hb0]; exact h₁ p
  have e2 : ∀ p, ρ p (b 1) = (a₂ p : 𝕜) • b 1 := fun p => by rw [hb1]; exact h₂ p
  let f : P →* 𝕜ˣ :=
    { toFun := a₁
      map_one' := by
        apply hcancel
        rw [← h₁ 1, map_one]
        simp
      map_mul' := fun p q => by
        apply hcancel
        have h : ρ (p * q) m₁ = ρ p (ρ q m₁) := by rw [map_mul]; rfl
        rw [← h₁ (p * q), h, h₁ q, map_smul, h₁ p, smul_smul]
        simp [mul_comm] }
  refine ⟨f, ?_⟩
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro p hp
  rw [MonoidHom.mem_ker] at hp
  have ha1 : (a₁ p : 𝕜) = 1 := by
    have : a₁ p = 1 := hp
    simp [this]
  have ha2 : (a₂ p : 𝕜) = 1 := by
    have := hdet' p
    rw [ha1, one_mul] at this
    exact this
  have hρ1 : ρ p = ρ 1 := by
    refine LinearEquiv.toLinearMap_injective (b.ext fun i => ?_)
    fin_cases i
    · simp [e1, ha1]
    · simp [e2, ha2]
  rw [Subgroup.mem_bot]
  exact hρ hρ1

private lemma isCyclic_of_eigenbasis {𝕜 W P : Type*} [Field 𝕜] [AddCommGroup W]
    [Module 𝕜 W] [Group P] [Finite P] [FiniteDimensional 𝕜 W]
    (ρ : P →* (W ≃ₗ[𝕜] W))
    (hW : Module.finrank 𝕜 W = 2) (hρ : Function.Injective ρ)
    (hdet : ∀ p : P, LinearEquiv.det (ρ p) = 1) {m₁ m₂ : W}
    (hli : LinearIndependent 𝕜 ![m₁, m₂])
    (heig : ∀ p : P, ∃ a₁ a₂ : 𝕜ˣ, ρ p m₁ = (a₁ : 𝕜) • m₁ ∧
      ρ p m₂ = (a₂ : 𝕜) • m₂) :
    IsCyclic P := by
  obtain ⟨f, hf⟩ := exists_injective_character_of_eigenbasis ρ hW hρ hdet hli heig
  exact isCyclic_of_injective_ringHom ((Units.coeHom 𝕜).comp f)
    (Units.val_injective.comp hf)


private lemma exists_quadratic_endomorphism_of_isPGroup {𝕜 P W : Type*} [Field 𝕜]
    [IsAlgClosed 𝕜] [Group P] [Finite P] [Nontrivial P] (h3 : (3 : 𝕜) ≠ 0)
    (hP : IsPGroup 3 P) [AddCommGroup W] [Module 𝕜 W]
    (hW : Module.finrank 𝕜 W = 2) (σ : Representation 𝕜 P W)
    (hfaith : Function.Injective σ) (hdet : ∀ x : P, LinearMap.det (σ x) = 1) :
    ∃ (z : P) (F : Module.End 𝕜 W), z ∈ Subgroup.center P ∧ F = σ z ∧ F ^ 3 = 1 ∧
      F ≠ 1 ∧ LinearMap.det F = 1 ∧ F ^ 2 + F + 1 = 0 := by
  obtain ⟨z, hzmem, hzord⟩ := exists_central_order_three hP inferInstance
  let F : Module.End 𝕜 W := σ z
  have hF3 : F ^ 3 = 1 := by
    have hz3 : z ^ 3 = 1 := by
      rw [← hzord]
      exact pow_orderOf_eq_one z
    simpa [F, map_pow] using congrArg σ hz3
  have hFne : F ≠ 1 := by
    intro hF1
    have hz1 : z = 1 := hfaith (by simpa [F] using hF1)
    rw [hz1, orderOf_one] at hzord
    omega
  have hdetF : LinearMap.det F = 1 := hdet z
  haveI : FiniteDimensional 𝕜 W :=
    Module.finite_of_finrank_pos (by rw [hW]; norm_num)
  have hE1bot : F.eigenspace 1 = ⊥ := by
    by_contra hbot
    have heig : F.HasEigenvalue 1 := Module.End.hasEigenvalue_iff.mpr hbot
    have hsq := sub_one_sq_eq_zero_of_det_eq_one_of_hasEigenvalue_one hW hdetF heig
    exact hFne (eq_one_of_sub_one_mul_sub_one_eq_zero hsq hF3 h3)
  have hFquad : F ^ 2 + F + 1 = 0 := quadratic_of_cube_one_of_no_fixed h3 hF3 hE1bot
  exact ⟨z, F, hzmem, rfl, hF3, hFne, hdetF, hFquad⟩

theorem isCyclic_of_finrank_eq_two {𝕜 : Type*} [Field 𝕜] [IsAlgClosed 𝕜] (h3 : (3 : 𝕜) ≠ 0)
    {P : Type*} [Group P] [Finite P] (hP : IsPGroup 3 P)
    {W : Type*} [AddCommGroup W] [Module 𝕜 W] (hW : Module.finrank 𝕜 W = 2)
    (σ : Representation 𝕜 P W) (hfaith : Function.Injective σ)
    (hdet : ∀ x : P, LinearMap.det (σ x) = 1) : IsCyclic P := by
  classical
  by_cases htriv : Subsingleton P
  · exact isCyclic_of_subsingleton
  haveI : Nontrivial P := not_subsingleton_iff_nontrivial.mp htriv
  obtain ⟨z, F, hzmem, hF, hF3, hFne, hdetF, hFquad⟩ :=
    exists_quadratic_endomorphism_of_isPGroup h3 hP hW σ hfaith hdet
  haveI : FiniteDimensional 𝕜 W :=
    Module.finite_of_finrank_pos (by rw [hW]; norm_num)
  obtain ⟨a, μ, -, hne, -, -, -, hEa, hEμ, hcompl⟩ :=
    exists_eigenvalue_pair_of_quadratic h3 hW hFquad hdetF
  obtain ⟨m₁, m₂, -, -, hm₁span, hm₂span, hli, hm₁eig, hm₂eig⟩ :=
    exists_eigenbasis_of_isCompl hW hne hcompl hEa hEμ
  let ρ : P →* (W ≃ₗ[𝕜] W) :=
    (LinearMap.GeneralLinearGroup.generalLinearEquiv 𝕜 W).toMonoidHom.comp σ.asGroupHom
  have heig : ∀ p : P, ∃ a₁ a₂ : 𝕜ˣ, ρ p m₁ = (a₁ : 𝕜) • m₁ ∧
      ρ p m₂ = (a₂ : 𝕜) • m₂ := by
    intro p
    obtain ⟨a₁, a₂, h₁, h₂⟩ :=
      exists_scaling_of_central_eigenline σ hzmem F hF hli hm₁eig hm₂eig hm₁span
        hm₂span p
    exact ⟨a₁, a₂, by simpa [ρ, Representation.asGroupHom_apply] using h₁,
      by simpa [ρ, Representation.asGroupHom_apply] using h₂⟩
  have hρ : Function.Injective ρ := by
    intro p q hpq
    apply hfaith
    have h := congrArg (fun e : W ≃ₗ[𝕜] W => (e : W →ₗ[𝕜] W)) hpq
    simpa [ρ, Representation.asGroupHom_apply] using h
  have hdetρ : ∀ p : P, LinearEquiv.det (ρ p) = 1 := by
    intro p
    apply Units.ext
    rw [LinearEquiv.coe_det]
    simpa [ρ, Representation.asGroupHom_apply] using hdet p
  exact isCyclic_of_eigenbasis ρ hW hρ hdetρ hli heig


private lemma representation_eq_one_of_finrank_le_one {𝕜 G V : Type*} [Field 𝕜] [Group G]
    [AddCommGroup V] [Module 𝕜 V] [FiniteDimensional 𝕜 V] (hV : Module.finrank 𝕜 V ≤ 1)
    (hperf : Group.IsPerfect G) (τ : Representation 𝕜 G V) : ∀ g : G, τ g = 1 := by
  intro g
  exact perfect_trivial_of_comm τ hperf.commutator_eq_top
    (fun a _ b _ => comm_of_finrank_le_one hV (τ a) (τ b)) g (Subgroup.mem_top g)

private lemma eq_one_of_eq_one_on_sub_and_quot {𝕜 W G : Type*} [Field 𝕜] [AddCommGroup W]
    [Module 𝕜 W] [Group G] (h3 : (3 : 𝕜) ≠ 0) (ρ : Representation 𝕜 G W)
    (U : Submodule 𝕜 W) (hU : ∀ g, U ≤ U.comap (ρ g)) {P : Subgroup G}
    (hP : IsPGroup 3 P) {x : P}
    (h1 : ρ.subrepresentation U hU (x : G) = 1)
    (h2 : ρ.quotient U hU (x : G) = 1) : ρ (x : G) = 1 := by
  have h1' : ∀ u ∈ U, ρ (x : G) u = u := fun u hu =>
    (sub_apply_eq_one_iff ρ U hU (x : G)).mp h1 u hu
  have h2' : ∀ v, ρ (x : G) v - v ∈ U := fun v =>
    (quot_apply_eq_one_iff ρ U hU (x : G)).mp h2 v
  have hsq : (ρ (x : G) - 1) * (ρ (x : G) - 1) = 0 := by
    ext v
    have hfix : (ρ (x : G) - 1) (ρ (x : G) v - v) = 0 := by
      rw [LinearMap.sub_apply, Module.End.one_apply, h1' _ (h2' v), sub_self]
    simpa [Module.End.mul_apply] using hfix
  have hord0 : ((orderOf (x : G) : ℕ) : 𝕜) ≠ 0 := by
    rw [Subgroup.orderOf_coe]
    obtain ⟨k, hk⟩ := hP.exists_orderOf_eq_pow x
    rw [hk]
    simpa using pow_ne_zero k h3
  have hpow : (ρ (x : G)) ^ orderOf (x : G) = 1 := by
    rw [← map_pow, pow_orderOf_eq_one, map_one]
  exact eq_one_of_sub_one_mul_sub_one_eq_zero hsq hpow hord0


private lemma isCyclic_of_finrank_le_two {𝕜 : Type*} [Field 𝕜] [IsAlgClosed 𝕜]
    (h3 : (3 : 𝕜) ≠ 0) {G : Type*} [Group G] [Finite G] (hperf : Group.IsPerfect G)
    {W : Type*} [AddCommGroup W] [Module 𝕜 W] [FiniteDimensional 𝕜 W]
    (hW : Module.finrank 𝕜 W ≤ 2) (σ : Representation 𝕜 G W)
    (hfaith : Function.Injective σ) {P : Subgroup G} (hP : IsPGroup 3 P) : IsCyclic P := by
  by_cases hle1 : Module.finrank 𝕜 W ≤ 1
  · have htriv : ∀ g : G, σ g = 1 :=
      representation_eq_one_of_finrank_le_one hle1 hperf σ
    have hsubG : Subsingleton G := ⟨fun a b => hfaith (by rw [htriv a, htriv b])⟩
    haveI : Subsingleton P := ⟨fun a b => Subtype.ext (Subsingleton.elim _ _)⟩
    exact isCyclic_of_subsingleton
  · have h2 : Module.finrank 𝕜 W = 2 := by omega
    have hdet : ∀ g : G, LinearMap.det (σ g) = 1 := det_eq_one_of_perfect hperf σ
    let τ : Representation 𝕜 P W := σ.comp P.subtype
    have hfaithτ : Function.Injective τ := by
      intro p q hpq
      exact Subtype.ext (hfaith (by simpa [τ] using hpq))
    exact isCyclic_of_finrank_eq_two h3 hP h2 τ hfaithτ (fun p => hdet p)


private lemma det_quotient_eq_one_of_one_dim_subrepresentation {𝕜 W G : Type*}
    [Field 𝕜] [AddCommGroup W] [Module 𝕜 W] [FiniteDimensional 𝕜 W] [Group G]
    {σ : Representation 𝕜 G W} (hperf : Group.IsPerfect G)
    {U : Subrepresentation σ} (hU1 : Module.finrank 𝕜 U.toSubmodule = 1) :
    ∀ g : G, LinearMap.det (U.quotient g) = 1 := by
  have hUinv : ∀ g : G, U.toSubmodule ≤ U.toSubmodule.comap (σ g) :=
    U.apply_mem_toSubmodule
  have hUtriv : ∀ g : G, U.toRepresentation g = 1 :=
    representation_eq_one_of_finrank_le_one (by omega) hperf U.toRepresentation
  intro g
  have hdet := det_eq_one_of_perfect hperf σ g
  have hrec := LinearMap.det_eq_det_mul_det (W := U.toSubmodule) (e := σ g) (hUinv g)
  rw [hdet] at hrec
  have hdetU : LinearMap.det ((σ g).restrict (hUinv g)) = 1 := by
    rw [show (σ g).restrict (hUinv g) = U.toRepresentation g from rfl, hUtriv g]
    simp
  rw [hdetU] at hrec
  simpa [Subrepresentation.quotient] using hrec.symm

private lemma det_sub_eq_one_of_two_dim_subrepresentation {𝕜 W G : Type*}
    [Field 𝕜] [AddCommGroup W] [Module 𝕜 W] [FiniteDimensional 𝕜 W] [Group G]
    {σ : Representation 𝕜 G W} (hperf : Group.IsPerfect G)
    {U : Subrepresentation σ} (hQ1 : Module.finrank 𝕜 (W ⧸ U.toSubmodule) = 1) :
    ∀ g : G, LinearMap.det (U.toRepresentation g) = 1 := by
  have hUinv : ∀ g : G, U.toSubmodule ≤ U.toSubmodule.comap (σ g) :=
    U.apply_mem_toSubmodule
  have hQtriv : ∀ g : G, U.quotient g = 1 :=
    representation_eq_one_of_finrank_le_one (by omega) hperf U.quotient
  intro g
  have hdet := det_eq_one_of_perfect hperf σ g
  have hrec := LinearMap.det_eq_det_mul_det (W := U.toSubmodule) (e := σ g) (hUinv g)
  rw [hdet] at hrec
  have hdetQ : LinearMap.det
      (U.toSubmodule.mapQ U.toSubmodule (σ g) (hUinv g)) = 1 := by
    rw [show U.toSubmodule.mapQ U.toSubmodule (σ g) (hUinv g) = U.quotient g from rfl,
      hQtriv g]
    simp
  rw [hdetQ] at hrec
  simpa [Subrepresentation.toRepresentation] using hrec.symm

private lemma isCyclic_of_one_dim_subrepresentation {𝕜 W G : Type*} [Field 𝕜]
    [IsAlgClosed 𝕜] (h3 : (3 : 𝕜) ≠ 0) [AddCommGroup W] [Module 𝕜 W]
    [FiniteDimensional 𝕜 W] [Group G] [Finite G] {σ : Representation 𝕜 G W}
    (hperf : Group.IsPerfect G) (hfaith : Function.Injective σ)
    (hdim3 : Module.finrank 𝕜 W = 3) {P : Subgroup G} (hP : IsPGroup 3 P)
    {U : Subrepresentation σ} (hU1 : Module.finrank 𝕜 U.toSubmodule = 1) : IsCyclic P := by
  have hUinv : ∀ g : G, U.toSubmodule ≤ U.toSubmodule.comap (σ g) :=
    U.apply_mem_toSubmodule
  have hUtriv : ∀ g : G, U.toRepresentation g = 1 :=
    representation_eq_one_of_finrank_le_one (by omega) hperf U.toRepresentation
  have hQdet := det_quotient_eq_one_of_one_dim_subrepresentation hperf hU1
  have hQ2 : Module.finrank 𝕜 (W ⧸ U.toSubmodule) = 2 := by
    have := Submodule.finrank_quotient_add_finrank U.toSubmodule
    rw [hU1, hdim3] at this
    omega
  have hfaithQ : Function.Injective (U.quotient.comp P.subtype) := by
    intro p q hpq
    apply Subtype.ext
    have hpq' : U.quotient (p : G) = U.quotient (q : G) := by simpa using hpq
    let x : P := ⟨(p : G)⁻¹ * (q : G), P.mul_mem (P.inv_mem p.2) q.2⟩
    have hquot : σ.quotient U.toSubmodule hUinv (x : G) = 1 := by
      calc
        σ.quotient U.toSubmodule hUinv (x : G) = U.quotient (p : G)⁻¹ * U.quotient (q : G) := by
          rw [show (x : G) = (p : G)⁻¹ * (q : G) from rfl, map_mul]
          rfl
        _ = U.quotient (p : G)⁻¹ * U.quotient (p : G) := by rw [hpq']
        _ = U.quotient ((p : G)⁻¹ * (p : G)) := by rw [map_mul]
        _ = 1 := by rw [inv_mul_cancel, map_one]
    have hsub : σ.subrepresentation U.toSubmodule hUinv (x : G) = 1 := by
      calc
        σ.subrepresentation U.toSubmodule hUinv (x : G) = U.toRepresentation (x : G) := rfl
        _ = 1 := hUtriv (x : G)
    have hσ1 : σ (x : G) = 1 :=
      eq_one_of_eq_one_on_sub_and_quot h3 σ U.toSubmodule hUinv hP hsub hquot
    have hx1' : (x : G) = 1 := hfaith (by simpa using hσ1)
    have hx1 : (p : G)⁻¹ * (q : G) = 1 := by simpa [x] using hx1'
    have hpqG : (q : G) = (p : G) := by
      calc
        (q : G) = (p : G) * ((p : G)⁻¹ * (q : G)) := by group
        _ = (p : G) := by rw [hx1, mul_one]
    exact hpqG.symm
  exact isCyclic_of_finrank_eq_two h3 hP hQ2 (U.quotient.comp P.subtype) hfaithQ
    (fun p => hQdet p)

private lemma isCyclic_of_two_dim_subrepresentation {𝕜 W G : Type*} [Field 𝕜]
    [IsAlgClosed 𝕜] (h3 : (3 : 𝕜) ≠ 0) [AddCommGroup W] [Module 𝕜 W]
    [FiniteDimensional 𝕜 W] [Group G] [Finite G] {σ : Representation 𝕜 G W}
    (hperf : Group.IsPerfect G) (hfaith : Function.Injective σ)
    (hdim3 : Module.finrank 𝕜 W = 3) {P : Subgroup G} (hP : IsPGroup 3 P)
    {U : Subrepresentation σ} (hU2 : Module.finrank 𝕜 U.toSubmodule = 2) : IsCyclic P := by
  have hUinv : ∀ g : G, U.toSubmodule ≤ U.toSubmodule.comap (σ g) :=
    U.apply_mem_toSubmodule
  have hQ1 : Module.finrank 𝕜 (W ⧸ U.toSubmodule) = 1 := by
    have := Submodule.finrank_quotient_add_finrank U.toSubmodule
    rw [hU2, hdim3] at this
    omega
  have hQtriv : ∀ g : G, U.quotient g = 1 :=
    representation_eq_one_of_finrank_le_one (by omega) hperf U.quotient
  have hUdet := det_sub_eq_one_of_two_dim_subrepresentation hperf hQ1
  have hfaithU : Function.Injective (U.toRepresentation.comp P.subtype) := by
    intro p q hpq
    apply Subtype.ext
    have hpq' : U.toRepresentation (p : G) = U.toRepresentation (q : G) := by simpa using hpq
    let x : P := ⟨(p : G)⁻¹ * (q : G), P.mul_mem (P.inv_mem p.2) q.2⟩
    have hsub : σ.subrepresentation U.toSubmodule hUinv (x : G) = 1 := by
      calc
        σ.subrepresentation U.toSubmodule hUinv (x : G) = U.toRepresentation (x : G) := rfl
        _ = U.toRepresentation (p : G)⁻¹ * U.toRepresentation (q : G) := by
          rw [show (x : G) = (p : G)⁻¹ * (q : G) from rfl, map_mul]
        _ = U.toRepresentation (p : G)⁻¹ * U.toRepresentation (p : G) := by rw [hpq']
        _ = U.toRepresentation ((p : G)⁻¹ * (p : G)) := by rw [map_mul]
        _ = 1 := by rw [inv_mul_cancel, map_one]
    have hquot : σ.quotient U.toSubmodule hUinv (x : G) = 1 := by
      calc
        σ.quotient U.toSubmodule hUinv (x : G) = U.quotient (x : G) := rfl
        _ = 1 := hQtriv (x : G)
    have hσ1 : σ (x : G) = 1 :=
      eq_one_of_eq_one_on_sub_and_quot h3 σ U.toSubmodule hUinv hP hsub hquot
    have hx1' : (x : G) = 1 := hfaith (by simpa using hσ1)
    have hx1 : (p : G)⁻¹ * (q : G) = 1 := by simpa [x] using hx1'
    have hpqG : (q : G) = (p : G) := by
      calc
        (q : G) = (p : G) * ((p : G)⁻¹ * (q : G)) := by group
        _ = (p : G) := by rw [hx1, mul_one]
    exact hpqG.symm
  exact isCyclic_of_finrank_eq_two h3 hP hU2 (U.toRepresentation.comp P.subtype) hfaithU
    (fun p => hUdet p)

theorem isIrreducible_and_finrank_eq_three {𝕜 : Type*} [Field 𝕜] [IsAlgClosed 𝕜]
    (h3 : (3 : 𝕜) ≠ 0) {G : Type*} [Group G] [Finite G] (hperf : Group.IsPerfect G)
    {W : Type*} [AddCommGroup W] [Module 𝕜 W] [FiniteDimensional 𝕜 W]
    (hW : Module.finrank 𝕜 W ≤ 3) (σ : Representation 𝕜 G W) (hfaith : Function.Injective σ)
    {P : Subgroup G} (hP : IsPGroup 3 P) (hPc : ¬ IsCyclic P) :
    σ.IsIrreducible ∧ Module.finrank 𝕜 W = 3 := by
  classical
  haveI : Group.IsPerfect G := hperf
  have hdim3 : Module.finrank 𝕜 W = 3 := by
    by_contra hne
    have hlt : Module.finrank 𝕜 W < 3 := lt_of_le_of_ne hW hne
    have hle2 : Module.finrank 𝕜 W ≤ 2 := by omega
    exact hPc (isCyclic_of_finrank_le_two h3 hperf hle2 σ hfaith hP)
  refine ⟨?_, hdim3⟩
  haveI : Nontrivial W := Module.finrank_pos_iff.mp (by rw [hdim3]; norm_num)
  refine IsSimpleOrder.of_forall_eq_top ?_
  intro U hUbot
  by_cases hUtop : U = ⊤
  · exact hUtop
  exfalso
  have hUbot' : U.toSubmodule ≠ ⊥ := by
    intro h
    apply hUbot
    apply Subrepresentation.toSubmodule_injective
    rw [h]
    rfl
  have hUtop' : U.toSubmodule ≠ ⊤ := by
    intro h
    apply hUtop
    apply Subrepresentation.toSubmodule_injective
    rw [h]
    rfl
  have hposU : 0 < Module.finrank 𝕜 U.toSubmodule := by
    by_contra h
    have h0 : Module.finrank 𝕜 U.toSubmodule = 0 := by omega
    exact hUbot' (Submodule.finrank_eq_zero.mp h0)
  have hdimU_lt : Module.finrank 𝕜 U.toSubmodule < 3 := by
    have hlt : U.toSubmodule < ⊤ := lt_top_iff_ne_top.mpr hUtop'
    have h := Submodule.finrank_lt_finrank_of_lt hlt
    rwa [finrank_top, hdim3] at h
  rcases (show Module.finrank 𝕜 U.toSubmodule = 1 ∨
      Module.finrank 𝕜 U.toSubmodule = 2 by omega) with h1 | h2
  · exact hPc (isCyclic_of_one_dim_subrepresentation h3 hperf hfaith hdim3 hP h1)
  · exact hPc (isCyclic_of_two_dim_subrepresentation h3 hperf hfaith hdim3 hP h2)

end CFSG.RankThree.PartTwo.Sec16.Kcd166

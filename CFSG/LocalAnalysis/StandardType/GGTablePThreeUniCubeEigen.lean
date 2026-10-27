module

public import CFSG.LocalAnalysis.StandardType.GGTablePThreeUniCubeDefs

public section

namespace CFSG.StandardType.TablePThreeKG

open Matrix Module CFSG CFSG.Assembly CFSG.AGLEmbedding

private lemma cube_root_pow_three {K : Type} [Field K] {ω : K}
    (hω : ω ^ 2 + ω + 1 = 0) : ω ^ 3 = 1 := by
  have h : (ω - 1) * (ω ^ 2 + ω + 1) = ω ^ 3 - 1 := by ring
  rw [hω, mul_zero] at h
  exact sub_eq_zero.mp h.symm

private lemma cube_root_eq_of_sq_add_eq_zero {K : Type} [Field K] {ω : K}
    (hω : ω ^ 2 + ω + 1 = 0) :
    ∀ μ : K, μ ^ 3 = 1 → μ = 1 ∨ μ = ω ∨ μ = ω ^ 2 := by
  have hω3 : ω ^ 3 = 1 := cube_root_pow_three hω
  have hsum : ω + ω ^ 2 = -1 := by
    calc ω + ω ^ 2 = (ω ^ 2 + ω + 1) - 1 := by ring
      _ = -1 := by rw [hω, zero_sub]
  have hprod : ω * ω ^ 2 = 1 := by
    rw [show ω * ω ^ 2 = ω ^ 3 by ring, hω3]
  intro μ hμ
  have hfac : (μ - 1) * (μ ^ 2 + μ + 1) = 0 := by
    have h : μ ^ 3 - 1 = (μ - 1) * (μ ^ 2 + μ + 1) := by ring
    simpa [h] using sub_eq_zero.mpr hμ
  rcases mul_eq_zero.mp hfac with h1 | hq
  · left
    exact sub_eq_zero.mp h1
  · right
    have hquad : (μ - ω) * (μ - ω ^ 2) = 0 := by
      calc (μ - ω) * (μ - ω ^ 2) = μ ^ 2 - (ω + ω ^ 2) * μ + ω * ω ^ 2 := by ring
        _ = μ ^ 2 + μ + 1 := by rw [hsum, hprod]; ring
        _ = 0 := hq
    rcases mul_eq_zero.mp hquad with h | h
    · exact Or.inl (sub_eq_zero.mp h)
    · exact Or.inr (sub_eq_zero.mp h)

private lemma three_ne_zero {K : Type} [Field K] [CharP K 2] : (3 : K) ≠ 0 := by
  have htwo : (2 : K) = 0 := CharP.cast_eq_zero K 2
  have h : (3 : K) = (2 : K) + 1 := by norm_num
  rw [h, htwo, zero_add]
  exact one_ne_zero

private lemma cube_roots_distinct {K : Type} [Field K] [CharP K 2] {ω : K}
    (hω : ω ^ 2 + ω + 1 = 0) :
    (1 : K) ≠ ω ∧ (1 : K) ≠ ω ^ 2 ∧ ω ≠ ω ^ 2 := by
  have h3 : (3 : K) ≠ 0 := three_ne_zero
  have h1ω : (1 : K) ≠ ω := by
    intro h
    have h3zero : (3 : K) = 0 := by
      have h' : (1 : K) ^ 2 + 1 + 1 = 0 := by simpa [← h] using hω
      calc (3 : K) = (1 : K) ^ 2 + 1 + 1 := by norm_num
        _ = 0 := h'
    exact h3 h3zero
  have hω0 : ω ≠ 0 := by
    intro h0
    have h : (1 : K) = 0 := by simpa [h0] using hω
    exact one_ne_zero h
  have h1ω2 : (1 : K) ≠ ω ^ 2 := by
    intro h
    have hω_eq : ω = 0 := by
      have h' : (1 : K) + ω + 1 = 0 := by simpa [← h] using hω
      have htwo : (2 : K) = 0 := CharP.cast_eq_zero K 2
      calc ω = (1 + ω + 1) - 2 := by ring
        _ = 0 := by rw [h', htwo, sub_zero]
    exact hω0 hω_eq
  have hωω2 : ω ≠ ω ^ 2 := by
    intro h
    have h1eq : (1 : K) = ω := by
      have h2 : ω = ω * ω := by simpa [pow_two] using h
      have hc := congrArg (fun x => ω⁻¹ * x) h2
      rwa [inv_mul_cancel₀ hω0, ← mul_assoc, inv_mul_cancel₀ hω0, one_mul] at hc
    exact h1ω h1eq
  exact ⟨h1ω, h1ω2, hωω2⟩

private lemma pow_eq_one_of_mem_eigenspace {K : Type} [Field K] {n : ℕ}
    {M : Module.End K (Fin n → K)} (hM3 : M ^ 3 = 1) {μ : K} {v : Fin n → K}
    (hv : v ∈ M.eigenspace μ) (hv0 : v ≠ 0) : μ ^ 3 = 1 := by
  have h : (M ^ 3) v = μ ^ 3 • v :=
    (Module.End.hasEigenvector_iff.mpr ⟨hv, hv0⟩).pow_apply 3
  have h1 : (M ^ 3) v = v := by rw [hM3]; rfl
  have hμ : (μ ^ 3 - 1) • v = 0 := by
    rw [sub_smul, one_smul, ← h, h1, sub_self]
  exact sub_eq_zero.mp ((smul_eq_zero_iff_left hv0).mp hμ)

private lemma hermitian_orthogonal_of_eigen {K : Type} [Field K] {q n : ℕ}
    (hq3 : 3 ∣ q + 1) {d : GL (Fin n) K}
    (hd : IsHermIsometry q (d : Matrix (Fin n) (Fin n) K))
    {μ ν : K} (hμ3 : μ ^ 3 = 1) (hν3 : ν ^ 3 = 1) (hμν : μ ≠ ν)
    {v w : Fin n → K} (hv : v ∈ cubeEigen d μ) (hw : w ∈ cubeEigen d ν) :
    ∑ i, v i ^ q * w i = 0 := by
  have hv' : (d : Matrix (Fin n) (Fin n) K) *ᵥ v = μ • v := by
    have h := Module.End.mem_eigenspace_iff.mp hv
    simpa [cubeEigen, Matrix.toLin'_apply] using h
  have hw' : (d : Matrix (Fin n) (Fin n) K) *ᵥ w = ν • w := by
    have h := Module.End.mem_eigenspace_iff.mp hw
    simpa [cubeEigen, Matrix.toLin'_apply] using h
  have hsum : (∑ i, (μ • v) i ^ q * (ν • w) i) =
      (μ ^ q * ν) * ∑ i, v i ^ q * w i := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro i _
    simp only [Pi.smul_apply, smul_eq_mul, mul_pow]
    ring
  have hiso := hd v w
  rw [hv', hw', hsum] at hiso
  have hμ0 : μ ≠ 0 := by
    intro h0
    rw [h0] at hμ3
    norm_num at hμ3
  have hμq : μ ^ q = μ⁻¹ := by
    obtain ⟨m, hm⟩ := hq3
    have hpow : μ ^ q * μ = 1 := by
      rw [← pow_succ, hm, pow_mul, hμ3, one_pow]
    exact eq_inv_of_mul_eq_one_left hpow
  rw [hμq] at hiso
  have hzero : (μ⁻¹ * ν - 1) * (∑ i, v i ^ q * w i) = 0 := by
    rw [sub_mul, one_mul, hiso, sub_self]
  have hne : μ⁻¹ * ν - 1 ≠ 0 := by
    apply sub_ne_zero.mpr
    intro h
    exact hμν ((inv_mul_eq_one₀ hμ0).mp h)
  exact (mul_eq_zero.mp hzero).resolve_left hne

theorem uni_cube_eigen {K : Type} [Field K] [Finite K] [CharP K 2] {q n : ℕ}
    (hK : Nat.card K = q ^ 2) (hq3 : 3 ∣ q + 1)
    {d : GL (Fin n) K} (hd : IsHermIsometry q (d : Matrix (Fin n) (Fin n) K)) (hd3 : d ^ 3 = 1) :
    (∀ μ ν : K, μ ^ 3 = 1 → ν ^ 3 = 1 → μ ≠ ν → ∀ v ∈ cubeEigen d μ, ∀ w ∈ cubeEigen d ν,
        ∑ i, v i ^ q * w i = 0) ∧
      ∀ ω : K, ω ^ 2 + ω + 1 = 0 →
        Module.finrank K (cubeEigen d 1) + Module.finrank K (cubeEigen d ω) +
          Module.finrank K (cubeEigen d (ω ^ 2)) = n := by
  constructor
  · intro μ ν hμ3 hν3 hμν v hv w hw
    exact hermitian_orthogonal_of_eigen hq3 hd hμ3 hν3 hμν hv hw
  · intro ω hω
    let M : Module.End K (Fin n → K) := Matrix.toLin' (d : Matrix (Fin n) (Fin n) K)
    have hmat3 : (d : Matrix (Fin n) (Fin n) K) ^ 3 = 1 := by
      have h := congrArg (fun g : GL (Fin n) K => (g : Matrix (Fin n) (Fin n) K)) hd3
      simpa using h
    have hM3 : M ^ 3 = 1 := by
      rw [show M = Matrix.toLin' (d : Matrix (Fin n) (Fin n) K) from rfl,
        ← Matrix.toLin'_pow, hmat3, Matrix.toLin'_one]
      exact Module.End.one_eq_id.symm
    have hq3K : (3 : K) ≠ 0 := three_ne_zero
    have hsep : (Polynomial.X ^ 3 - 1 : Polynomial K).Separable := by
      rw [Polynomial.X_pow_sub_one_separable_iff]
      exact hq3K
    have hsq : Squarefree (Polynomial.X ^ 3 - 1 : Polynomial K) := hsep.squarefree
    have haeval : Polynomial.aeval M (Polynomial.X ^ 3 - 1 : Polynomial K) = 0 := by
      simp [hM3]
    have hss : M.IsSemisimple :=
      Module.End.isSemisimple_of_squarefree_aeval_eq_zero hsq haeval
    obtain ⟨h1ω, h1ω2, hωω2⟩ := cube_roots_distinct hω
    have hroot : ∀ μ : K, μ ^ 3 = 1 → μ = 1 ∨ μ = ω ∨ μ = ω ^ 2 :=
      cube_root_eq_of_sq_add_eq_zero hω
    have hω3 : ω ^ 3 = 1 := cube_root_pow_three hω
    have hWinv : (M.eigenspace 1 ⊔ M.eigenspace ω ⊔ M.eigenspace (ω ^ 2)) ∈ M.invtSubmodule := by
      exact Module.End.invtSubmodule.sup_mem
        (Module.End.invtSubmodule.sup_mem
          (Module.End.eigenspace_mem_invtSubmodule M 1)
          (Module.End.eigenspace_mem_invtSubmodule M ω))
        (Module.End.eigenspace_mem_invtSubmodule M (ω ^ 2))
    obtain ⟨U, hUinv, hWU⟩ := (Module.End.isSemisimple_iff.mp hss)
      (M.eigenspace 1 ⊔ M.eigenspace ω ⊔ M.eigenspace (ω ^ 2)) hWinv
    have hthree : M.eigenspace 1 ⊔ M.eigenspace ω ⊔ M.eigenspace (ω ^ 2) = ⊤ := by
      by_contra hWne
      have hUne : U ≠ ⊥ := by
        intro hUbot
        apply hWne
        simpa [hUbot] using hWU.codisjoint
      have hUM : ∀ x ∈ U, M x ∈ U :=
        (Module.End.mem_invtSubmodule_iff_forall_mem_of_mem M).mp hUinv
      let g : Module.End K U := LinearMap.restrict M hUM
      have hg3 : g ^ 3 = 1 := by
        apply LinearMap.ext
        intro x
        apply Subtype.ext
        show (M ^ 3) (x : Fin n → K) = (x : Fin n → K)
        rw [hM3]
        rfl
      have hgpoly : Polynomial.aeval g (Polynomial.X ^ 3 - 1 : Polynomial K) = 0 := by
        simp [hg3]
      have hgmin_dvd : minpoly K g ∣ (Polynomial.X ^ 3 - 1 : Polynomial K) :=
        minpoly.dvd K g hgpoly
      have hgmin_ne : minpoly K g ≠ 0 := minpoly.ne_zero_of_finite K g
      have hXne : (Polynomial.X ^ 3 - 1 : Polynomial K) ≠ 0 := by
        simpa using
          (Polynomial.monic_X_pow_sub_C (1 : K) (by norm_num : (3 : ℕ) ≠ 0)).ne_zero
      have hXsplit : (Polynomial.X ^ 3 - 1 : Polynomial K).Splits := by
        have hprim : IsPrimitiveRoot ω 3 := by
          rw [← orderOf_eq_prime hω3 h1ω.symm]
          exact IsPrimitiveRoot.orderOf ω
        simpa using Polynomial.X_pow_sub_one_splits hprim
      have hsplit : (minpoly K g).Splits :=
        Polynomial.Splits.of_dvd hXsplit hXne hgmin_dvd
      haveI : Nontrivial U := Submodule.nontrivial_iff_ne_bot.mpr hUne
      have hint : IsIntegral K g := IsIntegral.of_finite K g
      have hdeg : (minpoly K g).degree ≠ 0 := ne_of_gt (minpoly.degree_pos hint)
      obtain ⟨μ, hμroot⟩ := hsplit.exists_eval_eq_zero hdeg
      have hμeig : g.HasEigenvalue μ :=
        (Module.End.hasEigenvalue_iff_isRoot).mpr hμroot
      obtain ⟨x, hx⟩ := hμeig.exists_hasEigenvector
      have hx0 : x ≠ 0 := hx.2
      have hxapp : g x = μ • x := Module.End.HasEigenvector.apply_eq_smul hx
      have hxapp' : M (x : Fin n → K) = μ • (x : Fin n → K) := by
        have := congrArg (fun y : U => (y : Fin n → K)) hxapp
        simpa [g, LinearMap.restrict_coe_apply] using this
      have hvμ : (x : Fin n → K) ∈ M.eigenspace μ :=
        Module.End.mem_eigenspace_iff.mpr hxapp'
      have hxv0 : (x : Fin n → K) ≠ 0 := by
        intro h0
        exact hx0 (Submodule.coe_eq_zero.mp h0)
      have hμ3 : μ ^ 3 = 1 := pow_eq_one_of_mem_eigenspace hM3 hvμ hxv0
      have hxW : (x : Fin n → K) ∈
          M.eigenspace 1 ⊔ M.eigenspace ω ⊔ M.eigenspace (ω ^ 2) := by
        rcases hroot μ hμ3 with rfl | rfl | rfl
        · exact Submodule.mem_sup_left (Submodule.mem_sup_left hvμ)
        · exact Submodule.mem_sup_left (Submodule.mem_sup_right hvμ)
        · exact Submodule.mem_sup_right hvμ
      have hxU : (x : Fin n → K) ∈ U := x.2
      have hxzero : (x : Fin n → K) = 0 :=
        (Submodule.disjoint_def.mp hWU.disjoint) _ hxW hxU
      exact hx0 (Submodule.coe_eq_zero.mp hxzero)
    have hABC : Disjoint (M.eigenspace 1) (M.eigenspace ω ⊔ M.eigenspace (ω ^ 2)) := by
      classical
      have hsup : ({1, ω, ω ^ 2} : Finset K).SupIndep M.eigenspace :=
        M.eigenspaces_iSupIndep.supIndep' _
      have h := hsup.disjoint_sup_sup (u := ({1} : Finset K))
        (v := ({ω, ω ^ 2} : Finset K)) (by simp) (by simp) (by simp [h1ω, h1ω2])
      simpa [Finset.sup_insert, Finset.sup_singleton, Finset.sup_empty] using h
    have hBC : Disjoint (M.eigenspace ω) (M.eigenspace (ω ^ 2)) :=
      M.eigenspaces_iSupIndep.pairwiseDisjoint hωω2
    have hthree' : M.eigenspace 1 ⊔ (M.eigenspace ω ⊔ M.eigenspace (ω ^ 2)) = ⊤ := by
      rw [← sup_assoc]
      exact hthree
    have hdim1 := Submodule.finrank_sup_add_finrank_inf_eq (M.eigenspace 1)
      (M.eigenspace ω ⊔ M.eigenspace (ω ^ 2))
    rw [hthree', hABC.eq_bot, finrank_bot, add_zero, finrank_top, Module.finrank_fin_fun] at hdim1
    have hdim2 := Submodule.finrank_sup_add_finrank_inf_eq (M.eigenspace ω)
      (M.eigenspace (ω ^ 2))
    rw [hBC.eq_bot, finrank_bot, add_zero] at hdim2
    change Module.finrank K (M.eigenspace 1) + Module.finrank K (M.eigenspace ω) +
      Module.finrank K (M.eigenspace (ω ^ 2)) = n
    omega

end CFSG.StandardType.TablePThreeKG

end

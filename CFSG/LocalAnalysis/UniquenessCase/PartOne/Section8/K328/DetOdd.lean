module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.K328.DetOddTools
import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Export
import CFSG.GroupTheory.PerfectCoverProduct
import CFSG.GroupTheory.WeirSylow.UniqueE27Orthogonal
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.K328.DetDefs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.K328

open CFSG.Blueprint (LieModel)

open CFSG.Open
open CFSG.Blueprint (LieModel)
open Matrix
open CFSG.Open.StatedAPI
open Polynomial

private theorem k328dpuo_model_unpack {S : Type} [Group S] [Finite S]
    {n p f : ℕ} (h : LieModel S .PSU n p f) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = (p ^ f) ^ 2 ∧
      Nonempty (S ≃* StatedProj (StatedSU n (p ^ f) K)) := by
  have hcl := h.statedClassicalModel (t := .PSU) (by decide)
  exact hcl.2

private theorem k328dpuo_pos_transport {S : Type} [Group S] [Finite S]
    (K : Type) [Field K] [Finite K] (n q : ℕ) (e : S ≃* StatedProj (StatedSU n q K))
    (h : K328DetPosIn S) : K328DetPosIn (StatedProj (StatedSU n q K)) := by
  obtain ⟨Z, X, hpos, hX⟩ := h
  refine ⟨Z.map e.toMonoidHom, X.map e.toMonoidHom, pos_map e hpos, ?_⟩
  intro htop
  apply hX
  have hback : (X.map e.toMonoidHom).map e.symm.toMonoidHom = X := by
    rw [Subgroup.map_map]
    have : (e.symm.toMonoidHom.comp e.toMonoidHom) = MonoidHom.id S := by ext x; simp
    rw [this, Subgroup.map_id]
  rw [htop] at hback
  rw [Subgroup.map_top_of_surjective _ e.symm.surjective] at hback
  exact hback.symm

private theorem k328dpuo_lift_center
    (K : Type) [Field K] [Finite K] (n q : ℕ)
    (Z X : Subgroup (StatedProj (StatedSU n q K)))
    (hpos : Pos (StatedProj (StatedSU n q K)) Z X) :
    ∃ (Y : Subgroup (StatedSU n q K)) (ψ : Y →* ↥X),
      ⁅Y, Y⁆ = Y ∧ Function.Surjective ψ ∧
        ψ.ker ≤ Subgroup.center Y ∧
        (Subgroup.center Y).map ψ = Subgroup.center ↥X := by
  let U : Subgroup (GL (Fin n) K) := StatedSU n q K
  let N : Subgroup U := (StatedScalars (Fin n) K).subgroupOf U
  let T := StatedProj U
  let π : U →* T := QuotientGroup.mk' N
  let Xp : Subgroup U := X.comap π
  have hXp : Xp.map π = X :=
    (Subgroup.map_comap_eq_self_of_surjective (f := π) (QuotientGroup.mk'_surjective N)) X
  let Y : Subgroup U := CFSG.Quasithin.perfectCore Xp
  have hYperf : ⁅Y, Y⁆ = Y := CFSG.Quasithin.perfectCore_perfect Xp
  have hqs := hpos.2.2.2.2.1
  have hXcomm : ⁅X, X⁆ = X :=
    Subgroup.isPerfect_iff.mp (Group.isPerfect_def.mpr hqs.1)
  have hYmap : Y.map π = X := by
    rw [show Y = CFSG.Quasithin.perfectCore Xp from rfl, CFSG.Quasithin.map_perfectCore,
      hXp, CFSG.Quasithin.perfectCore_eq_self_of_perfect hXcomm]
  let πY : Y →* T := π.comp Y.subtype
  have hrange : πY.range ≤ X := by
    rw [show πY.range = Y.map π by ext x; simp [πY], hYmap]
  let ψ : Y →* ↥X := πY.codRestrict X (fun x => by
    rw [← hYmap]
    exact Subgroup.mem_map_of_mem π x.2)
  have hψ : Function.Surjective ψ := by
    intro x
    have hx : (x : T) ∈ Y.map π := by rw [hYmap]; exact x.2
    rw [Subgroup.mem_map] at hx
    obtain ⟨y, hy, hxy⟩ := hx
    refine ⟨⟨y, hy⟩, ?_⟩
    exact Subtype.ext hxy
  have hker : ψ.ker ≤ Subgroup.center Y := by
    intro y hy
    rw [Subgroup.mem_center_iff]
    intro z
    have hy1 : ψ y = 1 := hy
    have hπy : π (y : U) = 1 := by
      have := congrArg (fun w : ↥X => (w : T)) hy1
      simpa [ψ, πY] using this
    have hyN : (y : U) ∈ N := by
      rw [← QuotientGroup.ker_mk' N]
      exact MonoidHom.mem_ker.mpr hπy
    have hcen : (y : U) ∈ Subgroup.center U :=
      CFSG.Open.StatedAPI.statedScalars_subgroupOf_le_center U hyN
    have hcomm := Subgroup.mem_center_iff.mp hcen (z : U)
    exact Subtype.ext hcomm
  refine ⟨Y, ψ, hYperf, hψ, hker, ?_⟩
  have hYcommtop : commutator ↥Y = ⊤ :=
    Group.isPerfect_def.mp (Subgroup.isPerfect_iff.mpr hYperf)
  exact CFSG.HardMathSupport.Solomon.Coordinator.LieComp.map_center_of_surjective
    hYcommtop ψ hψ hker

private theorem k328dpuo_test_poly {K V : Type} [Field K] [AddCommGroup V] [Module K V]
    (T : Module.End K V) {ω : K} (hω : ω ^ 2 + ω + 1 = 0) (hω3 : ω ^ 3 = 1)
    (hT3 : T ^ 3 = 1) :
    (T - 1) * (T - ω • 1) * (T - ω ^ 2 • 1) = 0 := by
  have h1 : (1 : K) + ω + ω ^ 2 = 0 := by linear_combination hω
  have hfac : (Polynomial.X - Polynomial.C (1 : K)) * (Polynomial.X - Polynomial.C ω) *
      (Polynomial.X - Polynomial.C (ω ^ 2)) = Polynomial.X ^ 3 - Polynomial.C (1 : K) := by
    rw [map_one]
    ring_nf
    have hA : (1 : K[X]) + Polynomial.C ω + Polynomial.C (ω ^ 2) = 0 := by
      simpa [map_add, map_one] using congrArg (Polynomial.C : K →+* K[X]) h1
    have hB : Polynomial.C ω * Polynomial.C (ω ^ 2) = 1 := by
      have h2 : ω * ω ^ 2 = 1 := by linear_combination hω3
      simpa [map_mul, map_one] using congrArg (Polynomial.C : K →+* K[X]) h2
    linear_combination (Polynomial.X - Polynomial.X ^ 2) * hA + (Polynomial.X - 1) * hB
  let aevalT : K[X] →ₐ[K] Module.End K V :=
    @Polynomial.aeval K (Module.End K V) _ _ (Module.End.instAlgebra K K V) T
  have h := congrArg aevalT hfac
  simpa only [aevalT, Polynomial.aeval_X, Polynomial.aeval_C, map_neg, map_add, map_sub, map_mul,
    map_pow, map_one, ← Algebra.algebraMap_eq_smul_one, hT3, sub_eq_add_neg, add_neg_cancel] using h

private theorem k328dpuo_eigenvalue_exists {K V : Type} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (T : Module.End K V) {ω : K}
    (hω : ω ^ 2 + ω + 1 = 0) (hω3 : ω ^ 3 = 1) (hT3 : T ^ 3 = 1) (hTne : T ≠ 1) :
    T.eigenspace ω ≠ ⊥ ∨ T.eigenspace (ω ^ 2) ≠ ⊥ := by
  by_contra h
  rw [not_or] at h
  have hωe : T.eigenspace ω = ⊥ := by simpa using h.1
  have hω2e : T.eigenspace (ω ^ 2) = ⊥ := by simpa using h.2
  have hker1 : (T - ω • (1 : Module.End K V)).ker = ⊥ := by
    rw [← Module.End.eigenspace_def]
    exact hωe
  have hker2 : (T - ω ^ 2 • (1 : Module.End K V)).ker = ⊥ := by
    rw [← Module.End.eigenspace_def]
    exact hω2e
  have hinj1 : Function.Injective (T - ω • (1 : Module.End K V)) := by simpa using LinearMap.ker_eq_bot.mp hker1
  have hinj2 : Function.Injective (T - ω ^ 2 • (1 : Module.End K V)) := by simpa using LinearMap.ker_eq_bot.mp hker2
  have hsurj1 : Function.Surjective (T - ω • (1 : Module.End K V)) :=
    LinearMap.injective_iff_surjective.mp hinj1
  have hsurj2 : Function.Surjective (T - ω ^ 2 • (1 : Module.End K V)) :=
    LinearMap.injective_iff_surjective.mp hinj2
  have hfac := k328dpuo_test_poly T hω hω3 hT3
  let g : Module.End K V := (T - ω • (1 : Module.End K V)) * (T - ω ^ 2 • (1 : Module.End K V))
  have hsurjG : Function.Surjective g := by
    rw [show g = (T - ω • (1 : Module.End K V)).comp (T - ω ^ 2 • (1 : Module.End K V)) by
      simp [g, Module.End.mul_eq_comp]]
    exact hsurj1.comp hsurj2
  have hzero : (T - 1) * g = 0 := by
    rw [show (T - 1) * g = (T - 1) * (T - ω • (1 : Module.End K V)) * (T - ω ^ 2 • (1 : Module.End K V)) by
      simp [g, mul_assoc]]
    exact hfac
  have hTsub : T - 1 = 0 := by
    ext v
    obtain ⟨u, hu⟩ := hsurjG v
    have h1 : ((T - 1) * g) u = 0 := by rw [hzero]; rfl
    rw [Module.End.mul_eq_comp, LinearMap.comp_apply, hu] at h1
    exact h1
  exact hTne (sub_eq_zero.mp hTsub)

private theorem k328dpuo_toLin_sub_smul {K : Type} [Field K] {n : ℕ}
    (A : Matrix (Fin n) (Fin n) K) (μ : K) :
    Matrix.toLin' (A - μ • (1 : Matrix (Fin n) (Fin n) K)) =
      (Matrix.toLin' A - μ • (1 : Module.End K (Fin n → K))) := by
  ext v
  simp [Matrix.toLin'_apply]

private theorem k328dpuo_eigenspace_finrank_eq {K : Type} [Field K] {n : ℕ}
    (A : Matrix (Fin n) (Fin n) K) (μ : K) :
    Module.finrank K (Module.End.eigenspace (Matrix.toLin' A) μ) =
      n - (A - μ • (1 : Matrix (Fin n) (Fin n) K)).rank := by
  rw [Module.End.eigenspace_def, ← k328dpuo_toLin_sub_smul]
  have hrank : Module.finrank K (LinearMap.range (Matrix.toLin' (A - μ • (1 : Matrix (Fin n) (Fin n) K)))) =
      (A - μ • (1 : Matrix (Fin n) (Fin n) K)).rank := by
    rw [Matrix.toLin'_apply', Matrix.rank]
  have h := LinearMap.finrank_range_add_finrank_ker
    (Matrix.toLin' (A - μ • (1 : Matrix (Fin n) (Fin n) K)))
  rw [hrank, Module.finrank_pi, Fintype.card_fin] at h
  omega

private theorem k328dpuo_eigenspace_transpose {K : Type} [Field K] {n : ℕ}
    (A : Matrix (Fin n) (Fin n) K) (μ : K) :
    Module.finrank K (Module.End.eigenspace (Matrix.toLin' Aᵀ) μ) =
      Module.finrank K (Module.End.eigenspace (Matrix.toLin' A) μ) := by
  rw [k328dpuo_eigenspace_finrank_eq, k328dpuo_eigenspace_finrank_eq]
  have h1 : (μ • (1 : Matrix (Fin n) (Fin n) K))ᵀ = μ • (1 : Matrix (Fin n) (Fin n) K) := by
    ext i j
    simp [Matrix.transpose_apply, Matrix.one_apply, eq_comm]
  have h : (Aᵀ - μ • (1 : Matrix (Fin n) (Fin n) K)) =
      (A - μ • (1 : Matrix (Fin n) (Fin n) K))ᵀ := by
    rw [Matrix.transpose_sub, h1]
  rw [h, Matrix.rank_transpose]

private theorem k328dpuo_eigenspace_sq_op {K V : Type} [Field K] [AddCommGroup V] [Module K V]
    (T : Module.End K V) {ω : K} (hω3 : ω ^ 3 = 1) (hT3 : T ^ 3 = 1) :
    (T ^ 2).eigenspace ω = T.eigenspace (ω ^ 2) := by
  ext v
  rw [Module.End.mem_eigenspace_iff, Module.End.mem_eigenspace_iff]
  rw [pow_two, Module.End.mul_eq_comp, LinearMap.comp_apply]
  constructor
  · intro hv
    have h2 : v = ω • T v := by
      calc v = (T ^ 3) v := by rw [hT3]; rfl
        _ = T (T (T v)) := by rw [pow_succ, pow_succ]; rfl
        _ = T (ω • v) := by rw [hv]
        _ = ω • T v := by rw [map_smul]
    symm
    calc ω ^ 2 • v = ω ^ 2 • (ω • T v) := by conv_lhs => rw [h2]
      _ = (ω ^ 2 * ω) • T v := by rw [smul_smul]
      _ = (ω ^ 3) • T v := by rw [show ω ^ 2 * ω = ω ^ 3 by ring]
      _ = (1 : K) • T v := by rw [hω3]
      _ = T v := by rw [one_smul]
  · intro hv
    calc T (T v) = T (ω ^ 2 • v) := by rw [hv]
      _ = ω ^ 2 • T v := by rw [map_smul]
      _ = ω ^ 2 • (ω ^ 2 • v) := by rw [hv]
      _ = (ω ^ 2 * ω ^ 2) • v := by rw [smul_smul]
      _ = (ω ^ 4) • v := by rw [show ω ^ 2 * ω ^ 2 = ω ^ 4 by ring]
      _ = ω • v := by
        congr 1
        calc ω ^ 4 = ω ^ 3 * ω := by ring
          _ = 1 * ω := by rw [hω3]
          _ = ω := by ring

private theorem k328dpuo_eigenspace_map_finrank {K : Type} [Field K] [Finite K] {n : ℕ}
    (σ : K →+* K) (hσ : Function.Bijective σ)
    (A : Matrix (Fin n) (Fin n) K) {ω : K} (hω : σ ω = ω) :
    Module.finrank K (Module.End.eigenspace (Matrix.toLin' (A.map σ)) ω) =
      Module.finrank K (Module.End.eigenspace (Matrix.toLin' A) ω) := by
  classical
  have _ : Fintype K := Fintype.ofFinite K
  let e : K ≃ K := Equiv.ofBijective σ hσ
  let eV : (Fin n → K) ≃ (Fin n → K) := Equiv.piCongrRight (fun _ => e)
  have hev : ∀ v : Fin n → K, eV v = σ ∘ v := fun v => rfl
  have hmem : ∀ v : Fin n → K,
      (v ∈ Module.End.eigenspace (Matrix.toLin' A) ω) ↔
        (eV v ∈ Module.End.eigenspace (Matrix.toLin' (A.map σ)) ω) := by
    intro v
    rw [hev, Module.End.mem_eigenspace_iff, Module.End.mem_eigenspace_iff]
    constructor
    · intro hv
      ext i
      have hv' : (A *ᵥ v) = ω • v := by simpa [Matrix.toLin'_apply] using hv
      have h1 := RingHom.map_mulVec σ A v i
      have h2 : (ω • (σ ∘ v)) i = σ (ω * v i) := by
        simp [Pi.smul_apply, map_mul, hω]
      calc (A.map σ *ᵥ (σ ∘ v)) i = σ ((A *ᵥ v) i) := h1.symm
        _ = σ ((ω • v) i) := by rw [hv']
        _ = σ (ω * v i) := by simp [Pi.smul_apply]
        _ = (ω • (σ ∘ v)) i := h2.symm
    · intro hv
      ext i
      have h1 := RingHom.map_mulVec σ A v i
      have h2 : (ω • (σ ∘ v)) i = σ (ω * v i) := by
        simp [Pi.smul_apply, map_mul, hω]
      have h3 : (A.map σ *ᵥ (σ ∘ v)) i = (ω • (σ ∘ v)) i := by
        have := congr_fun hv i
        simpa [Matrix.toLin'_apply] using this
      apply σ.injective
      simp only [Matrix.toLin'_apply]
      rw [h1, h3, h2]
      simp [Pi.smul_apply]
  let eSub : (Module.End.eigenspace (Matrix.toLin' A) ω) ≃
      (Module.End.eigenspace (Matrix.toLin' (A.map σ)) ω) :=
    Equiv.subtypeEquiv eV hmem
  have hcard : Nat.card (Module.End.eigenspace (Matrix.toLin' A) ω) =
      Nat.card (Module.End.eigenspace (Matrix.toLin' (A.map σ)) ω) :=
    Nat.card_congr eSub
  rw [Module.natCard_eq_pow_finrank (K := K)
        (V := Module.End.eigenspace (Matrix.toLin' A) ω),
      Module.natCard_eq_pow_finrank (K := K)
        (V := Module.End.eigenspace (Matrix.toLin' (A.map σ)) ω)] at hcard
  exact (Nat.pow_right_injective (Finite.one_lt_card (α := K)) hcard).symm

private theorem k328dpuo_exists_cube_root {K : Type} [Field K] [Finite K] {p f : ℕ}
    (hcard : Nat.card K = (p ^ f) ^ 2) (hq1 : p ^ f % 3 = 1) :
    ∃ ω : K, ω ^ 3 = 1 ∧ ω ≠ 1 ∧ ω ^ (p ^ f) = ω := by
  have hqmod : (p ^ f) ^ 2 % 3 = 1 := by
    rw [pow_two, Nat.mul_mod, hq1]
  have h3dvd : 3 ∣ Nat.card Kˣ := by
    rw [Nat.card_units, hcard]
    omega
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨ωu, hωu⟩ := exists_prime_orderOf_dvd_card' (G := Kˣ) 3 h3dvd
  refine ⟨(ωu : K), ?_, ?_, ?_⟩
  · have h3 : ωu ^ 3 = 1 := by rw [← hωu, pow_orderOf_eq_one]
    exact congrArg (fun u : Kˣ => (u : K)) h3
  · intro h
    have h1 : ωu = 1 := Units.ext h
    rw [h1, orderOf_one] at hωu
    norm_num at hωu
  · have h := pow_mod_orderOf ωu (p ^ f)
    rw [hωu, hq1] at h
    have h' : ωu ^ (p ^ f) = ωu := by simpa using h.symm
    simpa [Units.val_pow_eq_pow_val] using congrArg (fun u : Kˣ => (u : K)) h'

private theorem k328dpuo_mid_bound {K : Type} [Field K] [Finite K] {n p f : ℕ}
    (hp : p.Prime) (hn7 : n ≤ 7) (hcard : Nat.card K = (p ^ f) ^ 2)
    (hq1 : p ^ f % 3 = 1) (A : Matrix (Fin n) (Fin n) K)
    (hA3 : A ^ 3 = 1) (huni : (A.map (· ^ (p ^ f)))ᵀ * A = 1) (hAne : A ≠ 1) :
    ∃ μ : K, μ ≠ 1 ∧
      Module.End.eigenspace (Matrix.toLin' A) μ ≠ ⊥ ∧
      Module.finrank K (Module.End.eigenspace (Matrix.toLin' A) μ) ≤ 4 := by
  classical
  obtain ⟨ω, hω3, hω_ne1, hωpow⟩ := k328dpuo_exists_cube_root hcard hq1
  have hωfac : (ω - 1) * (ω ^ 2 + ω + 1) = 0 := by
    have := hω3
    linear_combination this
  have hω : ω ^ 2 + ω + 1 = 0 := by
    rcases mul_eq_zero.mp hωfac with h | h
    · exact absurd (sub_eq_zero.mp h) hω_ne1
    · exact h
  have _ : Fintype K := Fintype.ofFinite K
  have : Fact p.Prime := ⟨hp⟩
  have hchar : CharP K p := charP_of_card_eq_prime_pow (f := 2 * f) (by
    rw [← Nat.card_eq_fintype_card, hcard, ← pow_mul, mul_comm])
  have _ : ExpChar K p := .prime hp
  let σ : K →+* K := iterateFrobenius K p f
  have hσapply : ∀ x : K, σ x = x ^ (p ^ f) := fun x => iterateFrobenius_def (R := K) p f x
  have hσinj : Function.Injective σ := RingHom.injective σ
  have hσbij : Function.Bijective σ :=
    ⟨hσinj, Finite.injective_iff_surjective.mp hσinj⟩
  have hωσ : σ ω = ω := by rw [hσapply, hωpow]
  have hmap : A.map (· ^ (p ^ f)) = A.map σ := by
    ext i j
    exact hσapply (A i j)
  have huni' : (A.map σ)ᵀ * A = 1 := by simpa [hmap] using huni
  let T : Module.End K (Fin n → K) := Matrix.toLin' A
  have hT3 : T ^ 3 = 1 := by
    dsimp [T]
    rw [← Matrix.toLin'_pow, hA3, Matrix.toLin'_one]
    rfl
  have hA1 : A * A ^ 2 = 1 := by
    calc A * A ^ 2 = A ^ 3 := by noncomm_ring
      _ = 1 := hA3
  have hB : (A.map σ)ᵀ = A ^ 2 := by
    calc (A.map σ)ᵀ = (A.map σ)ᵀ * 1 := by rw [mul_one]
      _ = (A.map σ)ᵀ * (A * A ^ 2) := by rw [hA1]
      _ = ((A.map σ)ᵀ * A) * A ^ 2 := by rw [mul_assoc]
      _ = 1 * A ^ 2 := by rw [huni']
      _ = A ^ 2 := by rw [one_mul]
  have hstep : T.eigenspace (ω ^ 2) = (T ^ 2).eigenspace ω :=
    (k328dpuo_eigenspace_sq_op T hω3 hT3).symm
  have hT2 : T ^ 2 = Matrix.toLin' (A ^ 2) := by
    dsimp [T]
    rw [Matrix.toLin'_pow]
  have hdim1 : Module.finrank K (T.eigenspace (ω ^ 2)) =
      Module.finrank K ((T ^ 2).eigenspace ω) := by rw [hstep]
  have hdim2 : Module.finrank K ((T ^ 2).eigenspace ω) =
      Module.finrank K (Module.End.eigenspace (Matrix.toLin' (A ^ 2)) ω) := by rw [hT2]
  have hdim3 : Module.finrank K (Module.End.eigenspace (Matrix.toLin' (A ^ 2)) ω) =
      Module.finrank K (Module.End.eigenspace (Matrix.toLin' ((A.map σ)ᵀ)) ω) := by rw [hB]
  have hdim4 : Module.finrank K (Module.End.eigenspace (Matrix.toLin' ((A.map σ)ᵀ)) ω) =
      Module.finrank K (Module.End.eigenspace (Matrix.toLin' (A.map σ)) ω) :=
    k328dpuo_eigenspace_transpose (A.map σ) ω
  have hdim5 : Module.finrank K (Module.End.eigenspace (Matrix.toLin' (A.map σ)) ω) =
      Module.finrank K (T.eigenspace ω) := by
    dsimp [T]
    exact k328dpuo_eigenspace_map_finrank σ hσbij A hωσ
  have hmeq : Module.finrank K (T.eigenspace (ω ^ 2)) =
      Module.finrank K (T.eigenspace ω) :=
    hdim1.trans (hdim2.trans (hdim3.trans (hdim4.trans hdim5)))
  have hdisj : T.eigenspace ω ⊓ T.eigenspace (ω ^ 2) = ⊥ := by
    rw [eq_bot_iff]
    intro v hv
    rw [Submodule.mem_bot]
    have h1 : T v = ω • v := Module.End.mem_eigenspace_iff.mp hv.1
    have h2 : T v = ω ^ 2 • v := Module.End.mem_eigenspace_iff.mp hv.2
    have h3 : (ω - ω ^ 2) • v = 0 := by
      rw [sub_smul, ← h1, h2, sub_self]
    have hne : ω - ω ^ 2 ≠ 0 := by
      intro h
      have hωeq : ω = ω ^ 2 := sub_eq_zero.mp h
      have hsq1 : ω ^ 2 = 1 := by
        calc ω ^ 2 = ω * ω := by ring
          _ = ω * ω ^ 2 := by rw [← hωeq]
          _ = ω ^ 3 := by ring
          _ = 1 := hω3
      exact hω_ne1 (hωeq.trans hsq1)
    exact (smul_eq_zero.mp h3).resolve_left hne
  have hsum := Submodule.finrank_sup_add_finrank_inf_eq (T.eigenspace ω) (T.eigenspace (ω ^ 2))
  rw [hdisj, finrank_bot, add_zero] at hsum
  have hle_sup : Module.finrank K ↥(T.eigenspace ω ⊔ T.eigenspace (ω ^ 2)) ≤ n := by
    have h := Submodule.finrank_mono (le_top :
      (T.eigenspace ω ⊔ T.eigenspace (ω ^ 2) : Submodule K (Fin n → K)) ≤
        (⊤ : Submodule K (Fin n → K)))
    simpa [Module.finrank_pi, Fintype.card_fin] using h
  have hle : Module.finrank K (T.eigenspace ω) + Module.finrank K (T.eigenspace (ω ^ 2)) ≤ n := by
    rw [← hsum]
    exact hle_sup
  have hm2 : 2 * Module.finrank K (T.eigenspace ω) ≤ n := by
    calc 2 * Module.finrank K (T.eigenspace ω) =
        Module.finrank K (T.eigenspace ω) + Module.finrank K (T.eigenspace ω) := by ring
      _ = Module.finrank K (T.eigenspace ω) + Module.finrank K (T.eigenspace (ω ^ 2)) := by rw [hmeq]
      _ ≤ n := hle
  have hm_le : Module.finrank K (T.eigenspace ω) ≤ 4 := by omega
  have hm2_le : Module.finrank K (T.eigenspace (ω ^ 2)) ≤ 4 := by
    rw [hmeq]
    exact hm_le
  have hTne : T ≠ 1 := by
    intro h
    apply hAne
    have := congrArg LinearMap.toMatrix' h
    simpa [T] using this
  have hex := k328dpuo_eigenvalue_exists T hω hω3 hT3 hTne
  have hω2_ne1 : ω ^ 2 ≠ 1 := by
    intro h
    apply hω_ne1
    calc ω = ω * ω ^ 2 := by rw [h]; ring
      _ = ω ^ 3 := by ring
      _ = 1 := hω3
  rcases hex with h | h
  · exact ⟨ω, hω_ne1, h, hm_le⟩
  · exact ⟨ω ^ 2, hω2_ne1, h, hm2_le⟩

private theorem k328dpuo_exists_cube_root_of_dvd {K : Type} [Field K] [Finite K]
    (h3dvd : 3 ∣ Nat.card K - 1) : ∃ ω : K, ω ^ 3 = 1 ∧ ω ≠ 1 := by
  have h3dvd' : 3 ∣ Nat.card Kˣ := by rwa [Nat.card_units]
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨ωu, hωu⟩ := exists_prime_orderOf_dvd_card' (G := Kˣ) 3 h3dvd'
  refine ⟨(ωu : K), ?_, ?_⟩
  · have h3 : ωu ^ 3 = 1 := by rw [← hωu, pow_orderOf_eq_one]
    exact congrArg (fun u : Kˣ => (u : K)) h3
  · intro h
    have h1 : ωu = 1 := Units.ext h
    rw [h1, orderOf_one] at hωu
    norm_num at hωu

private theorem k328dpuo_three_dvd_card_sub_one {K : Type} [Field K] [Finite K] {p f : ℕ}
    (hcard : Nat.card K = (p ^ f) ^ 2) (hqne : p ^ f % 3 ≠ 0) :
    3 ∣ Nat.card K - 1 := by
  have hqlt : p ^ f % 3 < 3 := Nat.mod_lt _ (by norm_num)
  have hq : p ^ f % 3 = 1 ∨ p ^ f % 3 = 2 := by omega
  have hqmod : (p ^ f) ^ 2 % 3 = 1 := by
    rcases hq with h | h <;> rw [pow_two, Nat.mul_mod, h]
  rw [hcard]
  omega

private theorem k328dpuo_small_bound {K : Type} [Field K] [Finite K] {n : ℕ}
    (hn4 : n ≤ 4) (h3dvd : 3 ∣ Nat.card K - 1) (A : Matrix (Fin n) (Fin n) K)
    (hA3 : A ^ 3 = 1) (hAne : A ≠ 1) :
    ∃ μ : K, μ ≠ 1 ∧
      Module.End.eigenspace (Matrix.toLin' A) μ ≠ ⊥ ∧
      Module.finrank K (Module.End.eigenspace (Matrix.toLin' A) μ) ≤ 4 := by
  obtain ⟨ω, hω3, hω_ne1⟩ := k328dpuo_exists_cube_root_of_dvd h3dvd
  have hωfac : (ω - 1) * (ω ^ 2 + ω + 1) = 0 := by
    have := hω3
    linear_combination this
  have hω : ω ^ 2 + ω + 1 = 0 := by
    rcases mul_eq_zero.mp hωfac with h | h
    · exact absurd (sub_eq_zero.mp h) hω_ne1
    · exact h
  let T : Module.End K (Fin n → K) := Matrix.toLin' A
  have hT3 : T ^ 3 = 1 := by
    dsimp [T]
    rw [← Matrix.toLin'_pow, hA3, Matrix.toLin'_one]
    rfl
  have hTne : T ≠ 1 := by
    intro h
    apply hAne
    have := congrArg LinearMap.toMatrix' h
    simpa [T] using this
  have hbound : ∀ μ : K, Module.finrank K (T.eigenspace μ) ≤ 4 := by
    intro μ
    have h := Submodule.finrank_mono (le_top : T.eigenspace μ ≤ (⊤ : Submodule K (Fin n → K)))
    have htop : Module.finrank K ↥(⊤ : Submodule K (Fin n → K)) = n := by
      simp [Fintype.card_fin]
    omega
  have hω2_ne1 : ω ^ 2 ≠ 1 := by
    intro h
    apply hω_ne1
    calc ω = ω * ω ^ 2 := by rw [h]; ring
      _ = ω ^ 3 := by ring
      _ = 1 := hω3
  rcases k328dpuo_eigenvalue_exists T hω hω3 hT3 hTne with h | h
  · exact ⟨ω, hω_ne1, h, hbound ω⟩
  · exact ⟨ω ^ 2, hω2_ne1, h, hbound (ω ^ 2)⟩

private theorem k328dpuo_sl_lift_gl (K : Type) [Field K] (n : ℕ)
    (H : Subgroup (GL (Fin n) K)) (hH : H ≤ StatedSL n K) :
    ∃ (Hsl : Subgroup (Matrix.SpecialLinearGroup (Fin n) K)) (e : H ≃* Hsl),
      ∀ h : H, ((e h : Hsl) : Matrix.SpecialLinearGroup (Fin n) K) =
        (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL n K).symm
          (⟨(h : GL (Fin n) K), hH h.2⟩ : StatedSL n K) := by
  let eSL := CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL n K
  let Hst : Subgroup (StatedSL n K) := H.subgroupOf (StatedSL n K)
  let Hsl : Subgroup (Matrix.SpecialLinearGroup (Fin n) K) := Hst.map eSL.symm.toMonoidHom
  let e1 : H ≃* Hst := (Subgroup.subgroupOfEquivOfLe hH).symm
  let e2 : Hst ≃* Hsl := Subgroup.equivMapOfInjective Hst eSL.symm.toMonoidHom eSL.symm.injective
  refine ⟨Hsl, e1.trans e2, ?_⟩
  intro h
  rfl

private theorem k328dpuo_central_kernel_transport {A B C : Type} [Group A] [Group B] [Group C]
    (e : A ≃* B) (φ : A →* C) (hφ : Function.Surjective φ) (hk : φ.ker ≤ Subgroup.center A) :
    Function.Surjective (φ.comp e.symm.toMonoidHom) ∧
      (φ.comp e.symm.toMonoidHom).ker ≤ Subgroup.center B := by
  constructor
  · exact hφ.comp e.symm.surjective
  · intro y hy
    have hy' : e.symm y ∈ φ.ker := hy
    have hcent : e.symm y ∈ Subgroup.center A := hk hy'
    have hmap : e (e.symm y) ∈ (Subgroup.center A).map e.toMonoidHom :=
      Subgroup.mem_map_of_mem e.toMonoidHom hcent
    have hmapcenter : Subgroup.map e.toMonoidHom (Subgroup.center A) = Subgroup.center B :=
      Subgroup.map_center_eq e
    rwa [e.apply_symm_apply, hmapcenter] at hmap

private theorem k328dpuo_sl_lift (K : Type) [Field K] (n q : ℕ)
    (H : Subgroup (StatedSU n q K)) :
    ∃ (Hsl : Subgroup (Matrix.SpecialLinearGroup (Fin n) K)) (e : H ≃* Hsl),
      ∀ h : H, ((e h : Hsl) : Matrix (Fin n) (Fin n) K) =
        (((h : StatedSU n q K) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
  let eSL := CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL n K
  let Hgl : Subgroup (GL (Fin n) K) := H.map (StatedSU n q K).subtype
  have hHgl : Hgl ≤ StatedSL n K := by
    rintro x ⟨h, hx, rfl⟩
    exact CFSG.Open.StatedAPI.statedSU_le_statedSL n q K h.2
  obtain ⟨Hsl, eH, hEH⟩ := k328dpuo_sl_lift_gl K n Hgl hHgl
  let eYH : H ≃* Hgl := Subgroup.equivMapOfInjective H (StatedSU n q K).subtype
    (StatedSU n q K).subtype_injective
  refine ⟨Hsl, eYH.trans eH, ?_⟩
  intro h
  have h1 := hEH (eYH h)
  have hcoe : ∀ X : StatedSL n K,
      ((eSL.symm X : Matrix.SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) =
        (X : GL (Fin n) K) := by
    intro X
    have h2 := CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL_coe n K (eSL.symm X)
    rw [MulEquiv.apply_symm_apply] at h2
    exact h2.symm
  change ((eH (eYH h) : Hsl) : Matrix (Fin n) (Fin n) K) =
    (((h : StatedSU n q K) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)
  rw [h1, hcoe]
  rfl

private theorem k328dpuo_perfect_congr {A B : Type} [Group A] [Group B] (e : A ≃* B)
    (hA : commutator A = ⊤) : commutator B = ⊤ := by
  rw [commutator_def] at hA ⊢
  have h := congrArg (Subgroup.map e.toMonoidHom) hA
  rw [Subgroup.map_commutator, Subgroup.map_top_of_surjective _ e.surjective] at h
  exact h

private theorem k328dpuo_no_pos_model (K : Type) [Field K] [Finite K]
    (n p f : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f)
    (hcard : Nat.card K = (p ^ f) ^ 2)
    (hcond : n ≤ 4 ∨ ((n = 5 ∨ n = 6 ∨ n = 7) ∧ p ^ f % 3 = 1))
    (hn1 : 1 ≤ n)
    (Z X : Subgroup (StatedProj (StatedSU n (p ^ f) K)))
    (hpos : Pos (StatedProj (StatedSU n (p ^ f) K)) Z X) : False := by
  classical
  obtain ⟨Y, ψ, hYperf, hψ, hker, hmapc⟩ := k328dpuo_lift_center K n (p ^ f) Z X hpos
  have hcenterX : Nat.card (Subgroup.center ↥X) = 3 := hpos.2.2.2.2.2.1
  have hdvd : 3 ∣ Nat.card (Subgroup.center Y) := by
    rw [← hcenterX, ← hmapc]
    exact Subgroup.card_map_dvd (H := Subgroup.center Y) ψ
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := Subgroup.center Y) 3 hdvd
  let zY : Y := z.val
  have hzYmem : zY ∈ Subgroup.center Y := z.2
  have hzYorder : orderOf zY = 3 := by
    dsimp [zY]
    rw [Subgroup.orderOf_coe]
    exact hz
  let A : Matrix (Fin n) (Fin n) K :=
    (((zY : Y) : StatedSU n (p ^ f) K) : GL (Fin n) K)
  have hzY3 : zY ^ 3 = 1 := by
    have := pow_orderOf_eq_one zY
    rwa [hzYorder] at this
  have hA3 : A ^ 3 = 1 := by
    have h := congrArg (fun y : Y =>
      (((y : StatedSU n (p ^ f) K) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) hzY3
    simpa [A] using h
  have _ : Fintype K := Fintype.ofFinite K
  have hkerSU := (CFSG.LinearGroups.unitary_scalar_kernel hp hcard (n := n) hn1).1
  have huni : (A.map (· ^ (p ^ f)))ᵀ * A = 1 := by
    have hmem : (((zY : Y) : StatedSU n (p ^ f) K) : GL (Fin n) K) ∈
        StatedSU n (p ^ f) K := ((zY : Y) : StatedSU n (p ^ f) K).2
    have h := (Set.ext_iff.mp hkerSU _).mp hmem
    simpa [A] using h.2
  have hinj : Function.Injective (fun y : Y =>
      (((y : StatedSU n (p ^ f) K) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) := by
    intro a b h
    apply Subtype.ext
    apply Subtype.ext
    ext i j
    exact congrFun (congrFun h i) j
  have hAne : A ≠ 1 := by
    intro h
    have hz1 : zY = 1 := hinj (by simpa [A] using h)
    rw [hz1, orderOf_one] at hzYorder
    norm_num at hzYorder
  obtain ⟨Ysl, e, he⟩ := k328dpuo_sl_lift K n (p ^ f) Y
  have hzmat : ((e zY : Ysl) : Matrix (Fin n) (Fin n) K) = A := he zY
  have hperfY : commutator ↥Y = ⊤ :=
    Group.isPerfect_def.mp (Subgroup.isPerfect_iff.mpr hYperf)
  have hperfYsl : commutator ↥Ysl = ⊤ := k328dpuo_perfect_congr e hperfY
  have hYsl_comm : ⁅Ysl, Ysl⁆ = Ysl :=
    Subgroup.isPerfect_iff.mp (Group.isPerfect_def.mpr hperfYsl)
  have hzSLmem : (((e zY : Ysl) : Matrix.SpecialLinearGroup (Fin n) K)) ∈ Ysl := (e zY).2
  have hzSLorder : orderOf (((e zY : Ysl) : Matrix.SpecialLinearGroup (Fin n) K)) = 3 := by
    calc orderOf (((e zY : Ysl) : Matrix.SpecialLinearGroup (Fin n) K)) =
        orderOf (e zY : Ysl) := Subgroup.orderOf_coe _
      _ = orderOf zY := MulEquiv.orderOf_eq e zY
      _ = 3 := hzYorder
  have hzSLcenter : (e zY : Ysl) ∈ Subgroup.center Ysl := by
    have h := Subgroup.mem_map_of_mem e.toMonoidHom hzYmem
    have hmapcenter : Subgroup.map e.toMonoidHom (Subgroup.center Y) = Subgroup.center Ysl :=
      Subgroup.map_center_eq e
    rwa [hmapcenter] at h
  have hzSLcentral : ∀ y ∈ Ysl,
      Commute (((e zY : Ysl) : Matrix.SpecialLinearGroup (Fin n) K)) y := by
    intro y hy
    have h := Subgroup.mem_center_iff.mp hzSLcenter ⟨y, hy⟩
    change ((e zY : Ysl) : Matrix.SpecialLinearGroup (Fin n) K) * y =
      y * ((e zY : Ysl) : Matrix.SpecialLinearGroup (Fin n) K)
    exact congrArg (fun w : Ysl => (w : Matrix.SpecialLinearGroup (Fin n) K)) h.symm
  let W := ↥X ⧸ Subgroup.center ↥X
  let φY : Y →* W := (QuotientGroup.mk' (Subgroup.center ↥X)).comp ψ
  have hφYsurj : Function.Surjective φY :=
    (QuotientGroup.mk'_surjective (Subgroup.center ↥X)).comp hψ
  have hcomap := CFSG.HardMathSupport.Solomon.Coordinator.LieComp.comap_center_of_surjective
    (Group.isPerfect_def.mp (Subgroup.isPerfect_iff.mpr hYperf)) ψ hψ hker
  have hkerφY : φY.ker ≤ Subgroup.center Y := by
    intro y hy
    have hy' : ψ y ∈ Subgroup.center ↥X := by
      have h : QuotientGroup.mk (ψ y) = (1 : W) := hy
      exact (QuotientGroup.eq_one_iff (ψ y)).mp h
    have hy'' : y ∈ (Subgroup.center ↥X).comap ψ := hy'
    rwa [hcomap] at hy''
  let φSL : Ysl →* W := φY.comp e.symm.toMonoidHom
  obtain ⟨hφSLsurj, hφSLker⟩ :=
    k328dpuo_central_kernel_transport e φY hφYsurj hkerφY
  have : Fact p.Prime := ⟨hp⟩
  have hcharP : CharP K p := charP_of_card_eq_prime_pow (f := 2 * f) (by
    rw [← Nat.card_eq_fintype_card, hcard, ← pow_mul, mul_comm])
  by_cases hp3 : p = 3
  · have hchar3 : ringChar K = 3 := by rw [ringChar.eq K p, hp3]
    have hn4 : n ≤ 4 := by
      rcases hcond with h | ⟨h, hq1⟩
      · exact h
      · exfalso
        have hq0 : p ^ f % 3 = 0 := by
          rw [hp3]
          obtain ⟨g, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : f ≠ 0)
          rw [pow_succ]
          simp
        omega
    exact (k328det_charThreeBlock K hchar3 n hn4 Ysl hYsl_comm
      (((e zY : Ysl) : Matrix.SpecialLinearGroup (Fin n) K)) hzSLmem hzSLcentral hzSLorder
      W φSL hφSLsurj hφSLker) hpos.2.2.2.2.2.2
  · have hqne : p ^ f % 3 ≠ 0 := by
      intro h0
      have h3dvd : 3 ∣ p ^ f := Nat.dvd_iff_mod_eq_zero.mpr h0
      have h3p : 3 ∣ p := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3dvd
      have hp3' : p = 3 := by
        have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).mp h3p
        omega
      exact hp3 hp3'
    have h3dvd : 3 ∣ Nat.card K - 1 := k328dpuo_three_dvd_card_sub_one hcard hqne
    have hrc : ringChar K ≠ 2 := by rw [ringChar.eq K p]; exact hp2
    by_cases hn4 : n ≤ 4
    · obtain ⟨μ, hμne, hμeig, hμdim⟩ := k328dpuo_small_bound hn4 h3dvd A hA3 hAne
      have heig : Module.End.eigenspace
          (Matrix.toLin' (((e zY : Ysl) : Matrix.SpecialLinearGroup (Fin n) K) :
            Matrix (Fin n) (Fin n) K)) μ ≠ ⊥ := by
        rwa [hzmat]
      have hdim : Module.finrank K (Module.End.eigenspace
          (Matrix.toLin' (((e zY : Ysl) : Matrix.SpecialLinearGroup (Fin n) K) :
            Matrix (Fin n) (Fin n) K)) μ) ≤ 4 := by
        rwa [hzmat]
      exact (k328det_oddEigenblock K hrc n Ysl hYsl_comm
        (((e zY : Ysl) : Matrix.SpecialLinearGroup (Fin n) K)) hzSLmem hzSLcentral hzSLorder
        μ hμne heig hdim W φSL hφSLsurj hφSLker) hpos.2.2.2.2.2.2
    · have hn5 : n = 5 ∨ n = 6 ∨ n = 7 := by
        rcases hcond with h | ⟨h, -⟩
        · exact absurd h hn4
        · exact h
      have hq1 : p ^ f % 3 = 1 := by
        rcases hcond with h | ⟨-, h⟩
        · exact absurd h hn4
        · exact h
      have hn7 : n ≤ 7 := by omega
      obtain ⟨μ, hμne, hμeig, hμdim⟩ :=
        k328dpuo_mid_bound hp hn7 hcard hq1 A hA3 huni hAne
      have heig : Module.End.eigenspace
          (Matrix.toLin' (((e zY : Ysl) : Matrix.SpecialLinearGroup (Fin n) K) :
            Matrix (Fin n) (Fin n) K)) μ ≠ ⊥ := by
        rwa [hzmat]
      have hdim : Module.finrank K (Module.End.eigenspace
          (Matrix.toLin' (((e zY : Ysl) : Matrix.SpecialLinearGroup (Fin n) K) :
            Matrix (Fin n) (Fin n) K)) μ) ≤ 4 := by
        rwa [hzmat]
      exact (k328det_oddEigenblock K hrc n Ysl hYsl_comm
        (((e zY : Ysl) : Matrix.SpecialLinearGroup (Fin n) K)) hzSLmem hzSLcentral hzSLorder
        μ hμne heig hdim W φSL hφSLsurj hφSLker) hpos.2.2.2.2.2.2

private theorem k328dpso_exists_omega (K : Type) [Field K] [Finite K]
    (hchar : ringChar K ≠ 2) (hmod : Nat.card K % 3 = 2) :
    ∃ (E : Type) (_ : Field E) (_ : Finite E) (ι : K →+* E) (ω : E),
      Function.Injective ι ∧ ringChar E ≠ 2 ∧ ω ≠ 1 ∧ ω ^ 2 + ω + 1 = 0 := by
  have : Fintype K := Fintype.ofFinite K
  let f : K[X] := X ^ 2 + X + 1
  have h3 : (3 : K) ≠ 0 := by
    intro h3zero
    obtain ⟨n, hp, hcard⟩ := FiniteField.card K (ringChar K)
    have hdvd : ringChar K ∣ 3 := ringChar.dvd h3zero
    have hp3 : ringChar K = 3 := by
      rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h | h
      · exact absurd h hp.ne_one
      · exact h
    have hcardK : Fintype.card K = 3 ^ (n : ℕ) := by rw [← hp3, hcard]
    have h3dvd : 3 ∣ Nat.card K := by
      rw [Nat.card_eq_fintype_card, hcardK]
      exact dvd_pow_self 3 n.pos.ne'
    have hmod0 : Nat.card K % 3 = 0 := Nat.mod_eq_zero_of_dvd h3dvd
    omega
  have hf : f = X ^ 2 + (X + C (1 : K)) := by
    simp only [f, C_1]
    ring
  have hdeg_lt' : (X + C (1 : K)).degree < ((2 : ℕ) : WithBot ℕ) := by
    rw [Polynomial.degree_X_add_C]
    norm_num
  have hdeg_lt : (X + C (1 : K)).degree < (X ^ 2 : K[X]).degree := by
    rw [Polynomial.degree_X_pow]
    exact hdeg_lt'
  have hf_monic : f.Monic := by
    rw [hf]
    exact Polynomial.monic_X_pow_add hdeg_lt'
  have hf_nat : f.natDegree = 2 := by
    have hlt : (X + C (1 : K)).natDegree < (X ^ 2 : K[X]).natDegree := by
      rw [Polynomial.natDegree_X_add_C, Polynomial.natDegree_X_pow]
      norm_num
    rw [hf, Polynomial.natDegree_add_eq_left_of_natDegree_lt hlt, Polynomial.natDegree_X_pow]
  have hf_degpos : 0 < f.degree := by
    rw [hf, Polynomial.degree_add_eq_left_of_degree_lt hdeg_lt, Polynomial.degree_X_pow]
    norm_num
  have hnotroot : ∀ x : K, ¬ IsRoot f x := by
    intro x hx
    rw [IsRoot.def] at hx
    have hxeq : x ^ 2 + x + 1 = 0 := by
      simpa [f] using hx
    by_cases hx1 : x = 1
    · rw [hx1] at hxeq
      norm_num at hxeq
      exact h3 hxeq
    · have hx0 : x ≠ 0 := by
        intro hx0
        rw [hx0] at hxeq
        norm_num at hxeq
      let u : Kˣ := Units.mk0 x hx0
      have hu_ne : u ≠ 1 := by
        intro h
        apply hx1
        have := congrArg (fun u : Kˣ => (u : K)) h
        simpa [u] using this
      have hu3 : u ^ 3 = 1 := by
        apply Units.ext
        have h : x ^ 3 = 1 := by
          have h' : (x - 1) * (x ^ 2 + x + 1) = 0 := by rw [hxeq, mul_zero]
          have e : (x - 1) * (x ^ 2 + x + 1) = x ^ 3 - 1 := by ring
          rw [e, sub_eq_zero] at h'
          exact h'
        simpa [u] using h
      have horder : orderOf u = 3 := by
        have hdvd : orderOf u ∣ 3 := orderOf_dvd_iff_pow_eq_one.mpr hu3
        rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h1 | h3'
        · exact absurd (orderOf_eq_one_iff.mp h1) hu_ne
        · exact h3'
      have h3units : 3 ∣ Nat.card Kˣ := by
        rw [← horder]
        exact orderOf_dvd_natCard u
      have hnotdvd : ¬ 3 ∣ Nat.card Kˣ := by
        intro hd
        have hmod0 : Nat.card Kˣ % 3 = 0 := Nat.mod_eq_zero_of_dvd hd
        have hKu : Nat.card K = Nat.card Kˣ + 1 := Nat.card_eq_card_units_add_one K
        have : Nat.card K % 3 = (Nat.card Kˣ + 1) % 3 := by rw [hKu]
        rw [this, Nat.add_mod, hmod0] at hmod
        norm_num at hmod
      exact hnotdvd h3units
  have hf_irr : Irreducible f := by
    apply Polynomial.irreducible_of_degree_le_three_of_not_isRoot
    · rw [hf_nat]; norm_num
    · exact hnotroot
  have : Fact (Irreducible f) := ⟨hf_irr⟩
  have : Finite (AdjoinRoot f) := by
    have : Module.Finite K (AdjoinRoot f) := Polynomial.Monic.finite_adjoinRoot hf_monic
    exact Module.finite_of_finite K
  have hrooteq : (AdjoinRoot.root f) ^ 2 + AdjoinRoot.root f + 1 = 0 := by
    have := AdjoinRoot.eval₂_root f
    simpa [f] using this
  have hinj : Function.Injective (AdjoinRoot.of f) :=
    AdjoinRoot.of.injective_of_monic_of_degree_pos hf_monic hf_degpos
  refine ⟨AdjoinRoot f, inferInstance, inferInstance, AdjoinRoot.of f, AdjoinRoot.root f, ?_, ?_, ?_, ?_⟩
  · exact hinj
  · have hcharE : ringChar (AdjoinRoot f) = ringChar K := by
      rw [ringChar.eq_iff]
      exact charP_of_injective_ringHom hinj (ringChar K)
    rw [hcharE]; exact hchar
  · intro hroot1
    rw [hroot1] at hrooteq
    norm_num at hrooteq
    exact h3 ((AdjoinRoot.of f).injective (by
      calc (AdjoinRoot.of f) (3 : K) = (3 : AdjoinRoot f) := map_ofNat (AdjoinRoot.of f) 3
        _ = 0 := hrooteq
        _ = (AdjoinRoot.of f) (0 : K) := (map_zero (AdjoinRoot.of f)).symm))
  · exact hrooteq

open Matrix Module
open scoped commutatorElement

private theorem k328dpso_mem_center_of_commutator_mem_center {P : Type*} [Group P]
    (hP : Group.IsPerfect P) {q : P} (hc : ∀ y : P, ⁅q, y⁆ ∈ Subgroup.center P) :
    q ∈ Subgroup.center P := by
  rw [Subgroup.mem_center_iff]
  intro g
  have hθeq : ⁅q, g⁆ = 1 := by
    let θ : P →* Subgroup.center P :=
      { toFun := fun y => ⟨⁅q, y⁆, hc y⟩
        map_one' := by ext; simp
        map_mul' := by
          intro y z
          ext
          simp only [Subgroup.coe_mul]
          calc ⁅q, y * z⁆ = ⁅q, y⁆ * y * ⁅q, z⁆ * y⁻¹ :=
                commutatorElement_mul_right_eq_mul_conj q y z
            _ = ⁅q, y⁆ * (y * ⁅q, z⁆) * y⁻¹ := by group
            _ = ⁅q, y⁆ * (⁅q, z⁆ * y) * y⁻¹ := by
                  rw [show y * ⁅q, z⁆ = ⁅q, z⁆ * y from
                    Subgroup.mem_center_iff.mp (hc z) y]
            _ = ⁅q, y⁆ * ⁅q, z⁆ := by group }
    have : IsMulCommutative θ.range :=
      isMulCommutative_iff.mpr fun (a b : θ.range) => Subtype.ext (Subtype.ext
        (Subgroup.mem_center_iff.mp (b.1.2) (a.1)))
    have hperf : Group.IsPerfect θ.range := by
      have : Group.IsPerfect P := hP
      exact Group.IsPerfect.range θ
    have : Subsingleton θ.range :=
      Group.IsPerfect.subsingleton_of_isMulCommutative
    have h1 : (⟨θ g, MonoidHom.mem_range.mpr ⟨g, rfl⟩⟩ : θ.range) = 1 :=
      Subsingleton.elim _ _
    exact congrArg Subtype.val (congrArg Subtype.val h1)
  exact (commutatorElement_eq_one_iff_mul_comm.mp hθeq).symm

private theorem k328dpso_center_map_eq {P X : Type*} [Group P] [Group X] (π : P →* X)
    (hπ : Function.Surjective π) (hker : π.ker ≤ Subgroup.center P) (hP : Group.IsPerfect P) :
    (Subgroup.center P).map π = Subgroup.center X := by
  apply le_antisymm
  · exact Subgroup.map_center_le_center (f := π) hπ
  · intro x hx
    obtain ⟨p, rfl⟩ := hπ x
    have hp : p ∈ Subgroup.center P :=
      k328dpso_mem_center_of_commutator_mem_center hP fun y =>
        hker (by
          rw [MonoidHom.mem_ker, map_commutatorElement]
          exact commutatorElement_eq_one_iff_mul_comm.mpr
            (Subgroup.mem_center_iff.mp hx (π y)).symm)
    exact Subgroup.mem_map_of_mem π hp

private theorem k328dpso_comap_center_le_center {P X : Type*} [Group P] [Group X] (π : P →* X)
    (hker : π.ker ≤ Subgroup.center P) (hP : Group.IsPerfect P) :
    (Subgroup.center X).comap π ≤ Subgroup.center P := by
  intro q hq
  rw [Subgroup.mem_comap] at hq
  exact k328dpso_mem_center_of_commutator_mem_center hP fun y =>
    hker (by
      rw [MonoidHom.mem_ker, map_commutatorElement]
      exact commutatorElement_eq_one_iff_mul_comm.mpr
        (Subgroup.mem_center_iff.mp hq (π y)).symm)

private theorem k328dpso_center_order_three {P X : Type*} [Group P] [Group X] [Finite P] [Finite X]
    (π : P →* X) (hπ : Function.Surjective π) (hker : π.ker ≤ Subgroup.center P)
    (hP : Group.IsPerfect P) (hX : Nat.card (Subgroup.center X) = 3) :
    ∃ z : P, z ∈ Subgroup.center P ∧ orderOf z = 3 := by
  have hmap := k328dpso_center_map_eq π hπ hker hP
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨x, hx3⟩ := exists_prime_orderOf_dvd_card' (G := ↥(Subgroup.center X)) 3 (by rw [hX])
  have hxmem : (x : X) ∈ (Subgroup.center P).map π := by
    rw [hmap]
    exact x.2
  obtain ⟨z, hzP, hzπ⟩ := Subgroup.mem_map.mp hxmem
  have h3dvd : 3 ∣ Nat.card (Subgroup.center P) := by
    have h1 : orderOf (x : X) ∣ orderOf z := by
      rw [← hzπ]
      exact orderOf_map_dvd π z
    have hx3' : orderOf (x : X) = 3 := by
      rw [Subgroup.orderOf_coe]
      exact hx3
    rw [hx3'] at h1
    exact h1.trans (Subgroup.orderOf_dvd_natCard (Subgroup.center P) hzP)
  obtain ⟨w, hw⟩ := exists_prime_orderOf_dvd_card' (G := ↥(Subgroup.center P)) 3 h3dvd
  exact ⟨(w : P), w.2, by rw [Subgroup.orderOf_coe]; exact hw⟩

private theorem k328dpso_monoidHom_eq_one_of_isPerfect {G A : Type*} [Group G] [Group A]
    [IsMulCommutative A] (hG : Group.IsPerfect G) (f : G →* A) (g : G) : f g = 1 := by
  have : Group.IsPerfect f.range := by
    have : Group.IsPerfect G := hG
    exact Group.IsPerfect.range f
  have : Subsingleton f.range := Group.IsPerfect.subsingleton_of_isMulCommutative
  exact congrArg Subtype.val
    (Subsingleton.elim (⟨f g, MonoidHom.mem_range.mpr ⟨g, rfl⟩⟩ : f.range) 1)

private theorem k328dpso_det_eq_one_of_perfect {K : Type} [Field K] {n : ℕ}
    (P : Subgroup (CFSG.Open.StatedSp n K)) (hP : Group.IsPerfect ↥P) (p : ↥P) :
    (((p : CFSG.Open.StatedSp n K) : GL (Fin n ⊕ Fin n) K) :
      Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K).det = 1 := by
  let f : ↥P →* Kˣ :=
    (Matrix.GeneralLinearGroup.det).comp
      ((CFSG.Open.StatedSp n K).subtype.comp P.subtype)
  have h := k328dpso_monoidHom_eq_one_of_isPerfect hP f p
  have h1 : ((f p : Kˣ) : K) = 1 := by rw [h]; rfl
  simpa [f, Matrix.GeneralLinearGroup.det] using h1

private theorem k328dpso_det_reindex_map {K E : Type} [Field K] [Field E] (φ : K →+* E)
    (n : ℕ) (M : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) (hM : M.det = 1) :
    (Matrix.reindex finSumFinEquiv finSumFinEquiv (φ.mapMatrix M)).det = 1 := by
  rw [Matrix.det_reindex_self, ← RingHom.map_det, hM, map_one]

private noncomputable def k328dpso_matHom {K E : Type} [Field K] [Field E] (φ : K →+* E)
    (n : ℕ) :
    Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K →+* Matrix (Fin (n+n)) (Fin (n+n)) E :=
  (Matrix.reindexRingEquiv E finSumFinEquiv).toRingHom.comp (φ.mapMatrix)

open CFSG.Open in
private noncomputable def k328dpso_slHomSp {K E : Type} [Field K] [Field E] (φ : K →+* E)
    (n : ℕ) (hdet : ∀ g : CFSG.Open.StatedSp n K,
      ((g : GL (Fin n ⊕ Fin n) K) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K).det = 1) :
    CFSG.Open.StatedSp n K →* Matrix.SpecialLinearGroup (Fin (n+n)) E where
  toFun g := ⟨k328dpso_matHom φ n ((g : GL (Fin n ⊕ Fin n) K) :
    Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K), by
      change (Matrix.reindex finSumFinEquiv finSumFinEquiv
        (φ.mapMatrix ((g : GL (Fin n ⊕ Fin n) K) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K))).det = 1
      exact k328dpso_det_reindex_map φ n _ (hdet g)⟩
  map_one' := by
    apply Subtype.ext
    ext i j
    simp [k328dpso_matHom, Units.val_one, Matrix.one_apply,
      finSumFinEquiv.symm.injective.eq_iff]
  map_mul' := by
    intro g h
    apply Subtype.ext
    exact map_mul (k328dpso_matHom φ n) _ _

private noncomputable def k328dpso_slHomP {K E : Type} [Field K] [Field E] (φ : K →+* E)
    (n : ℕ) (P : Subgroup (CFSG.Open.StatedSp n K)) (hP : Group.IsPerfect ↥P) :
    ↥P →* Matrix.SpecialLinearGroup (Fin (n+n)) E where
  toFun p := ⟨k328dpso_matHom φ n (((p : CFSG.Open.StatedSp n K) : GL (Fin n ⊕ Fin n) K) :
      Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K), by
    change (Matrix.reindex finSumFinEquiv finSumFinEquiv
      (φ.mapMatrix ((((p : CFSG.Open.StatedSp n K) : GL (Fin n ⊕ Fin n) K) :
        Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K)))).det = 1
    rw [Matrix.det_reindex_self, ← RingHom.map_det]
    rw [k328dpso_det_eq_one_of_perfect P hP p, map_one]⟩
  map_one' := by
    apply Subtype.ext
    exact map_one (k328dpso_matHom φ n)
  map_mul' := by
    intro p q
    apply Subtype.ext
    exact map_mul (k328dpso_matHom φ n) _ _

private theorem k328dpso_slHomP_injective {K E : Type} [Field K] [Field E] (φ : K →+* E)
    (hφ : Function.Injective φ) (n : ℕ) (P : Subgroup (CFSG.Open.StatedSp n K))
    (hP : Group.IsPerfect ↥P) : Function.Injective (k328dpso_slHomP φ n P hP) := by
  have hmatInj : Function.Injective (k328dpso_matHom φ n) := by
    intro A B h
    have h1 : (Matrix.reindexRingEquiv E finSumFinEquiv) (φ.mapMatrix A) =
        (Matrix.reindexRingEquiv E finSumFinEquiv) (φ.mapMatrix B) := h
    have h2 : φ.mapMatrix A = φ.mapMatrix B :=
      (Matrix.reindexRingEquiv E finSumFinEquiv).injective h1
    ext i j
    exact hφ (congr_fun (congr_fun h2 i) j)
  intro p q hpq
  have hval := congrArg (fun x : Matrix.SpecialLinearGroup (Fin (n+n)) E =>
    (x : Matrix (Fin (n+n)) (Fin (n+n)) E)) hpq
  have hM : (((p : CFSG.Open.StatedSp n K) : GL (Fin n ⊕ Fin n) K)) =
      (((q : CFSG.Open.StatedSp n K) : GL (Fin n ⊕ Fin n) K)) := by
    apply Units.ext
    exact hmatInj hval
  exact Subtype.ext (Subtype.ext hM)

private noncomputable def k328dpso_J (n : ℕ) (E : Type) [Field E] :
    Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) E :=
  fromBlocks 0 1 (-1) 0

private theorem k328dpso_J_mul_self (n : ℕ) (E : Type) [Field E] :
    k328dpso_J n E * k328dpso_J n E = -1 := by
  rw [k328dpso_J, fromBlocks_multiply]
  ext i j
  rcases i with i | i <;> rcases j with j | j <;>
    simp [Matrix.neg_apply, Matrix.one_apply]

private theorem k328dpso_negJ_mul_J (n : ℕ) (E : Type) [Field E] :
    (-k328dpso_J n E) * k328dpso_J n E = 1 := by
  rw [Matrix.neg_mul, k328dpso_J_mul_self, neg_neg]

private theorem k328dpso_J_det_ne_zero (n : ℕ) (E : Type) [Field E] :
    (k328dpso_J n E).det ≠ 0 :=
  Matrix.det_ne_zero_of_left_inverse (k328dpso_negJ_mul_J n E)

private noncomputable def k328dpso_form (n : ℕ) (E : Type) [Field E] :
    LinearMap.BilinForm E (Fin n ⊕ Fin n → E) :=
  Matrix.toBilin' (k328dpso_J n E)

private theorem k328dpso_form_nondegenerate (n : ℕ) (E : Type) [Field E] :
    (k328dpso_form n E).Nondegenerate :=
  LinearMap.BilinForm.nondegenerate_toBilin'_of_det_ne_zero' (k328dpso_J n E)
    (k328dpso_J_det_ne_zero n E)

private theorem k328dpso_form_isometry {E : Type} [Field E] (n : ℕ)
    (z : GL (Fin n ⊕ Fin n) E) (hz : z ∈ CFSG.Open.StatedSp n E) (v w : Fin n ⊕ Fin n → E) :
    k328dpso_form n E ((z : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) E) *ᵥ v)
        ((z : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) E) *ᵥ w)
      = k328dpso_form n E v w := by
  have hJ : (z : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) E)ᵀ * k328dpso_J n E *
        (z : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) E) = k328dpso_J n E :=
    CFSG.Open.StatedAPI.mem_statedSp_iff.mp hz
  have h := Matrix.toBilin'_comp (k328dpso_J n E)
    (z : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) E)
    (z : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) E)
  rw [hJ] at h
  have := congrArg (fun (F : LinearMap.BilinForm E (Fin n ⊕ Fin n → E)) => F v w) h
  simpa [k328dpso_form, LinearMap.BilinForm.comp_apply, Matrix.toLin'_apply] using this

private theorem k328dpso_form_eigen_zero {E : Type} [Field E] (n : ℕ)
    (z : GL (Fin n ⊕ Fin n) E) (hz : z ∈ CFSG.Open.StatedSp n E)
    {μ : E} (hμ2 : μ ^ 2 ≠ 1) {v w : Fin n ⊕ Fin n → E}
    (hv : v ∈ Module.End.eigenspace
      (Matrix.toLin' (z : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) E)) μ)
    (hw : w ∈ Module.End.eigenspace
      (Matrix.toLin' (z : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) E)) μ) :
    k328dpso_form n E v w = 0 := by
  have hv' : (z : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) E) *ᵥ v = μ • v := by
    simpa [Matrix.toLin'_apply] using (Module.End.mem_eigenspace_iff.mp hv)
  have hw' : (z : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) E) *ᵥ w = μ • w := by
    simpa [Matrix.toLin'_apply] using (Module.End.mem_eigenspace_iff.mp hw)
  have hinv := k328dpso_form_isometry n z hz v w
  have h2 : k328dpso_form n E ((z : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) E) *ᵥ v)
        ((z : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) E) *ᵥ w)
      = μ ^ 2 * k328dpso_form n E v w := by
    rw [hv', hw']
    simp only [map_smul, LinearMap.smul_apply, smul_eq_mul, pow_two]
    ring
  have heq : k328dpso_form n E v w = μ ^ 2 * k328dpso_form n E v w := hinv.symm.trans h2
  have hzero : (μ ^ 2 - 1) * k328dpso_form n E v w = 0 := by
    rw [sub_mul, one_mul]
    exact sub_eq_zero.mpr heq.symm
  exact (mul_eq_zero.mp hzero).resolve_left (sub_ne_zero.mpr hμ2)

private theorem k328dpso_eigenspace_le_orthogonal {E : Type} [Field E] (n : ℕ)
    (z : GL (Fin n ⊕ Fin n) E) (hz : z ∈ CFSG.Open.StatedSp n E) {μ : E}
    (hμ2 : μ ^ 2 ≠ 1) :
    Module.End.eigenspace (Matrix.toLin' (z : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) E)) μ ≤
      (k328dpso_form n E).orthogonal
        (Module.End.eigenspace (Matrix.toLin' (z : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) E)) μ) := by
  intro v hv
  change v ∈ Submodule.orthogonalBilin (k328dpso_form n E)
    (Module.End.eigenspace (Matrix.toLin' (z : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) E)) μ)
  rw [Submodule.mem_orthogonalBilin]
  intro w hw
  exact k328dpso_form_eigen_zero n z hz hμ2 hw hv

private theorem k328dpso_eigenspace_finrank_le_n {E : Type} [Field E] (n : ℕ)
    (z : GL (Fin n ⊕ Fin n) E) (hz : z ∈ CFSG.Open.StatedSp n E) {μ : E}
    (hμ2 : μ ^ 2 ≠ 1) :
    Module.finrank E
        (Module.End.eigenspace (Matrix.toLin' (z : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) E)) μ)
      ≤ n := by
  let W := Module.End.eigenspace
    (Matrix.toLin' (z : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) E)) μ
  change Module.finrank E W ≤ n
  have hWle : W ≤ (k328dpso_form n E).orthogonal W :=
    k328dpso_eigenspace_le_orthogonal n z hz hμ2
  have hfin := LinearMap.BilinForm.finrank_orthogonal (k328dpso_form_nondegenerate n E) W
  have hle : Module.finrank E W ≤ Module.finrank E ((k328dpso_form n E).orthogonal W) :=
    Submodule.finrank_mono hWle
  have hdim : Module.finrank E (Fin n ⊕ Fin n → E) = 2 * n := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum]
    simp [Fintype.card_fin, two_mul]
  rw [hfin, hdim] at hle
  omega

private theorem k328dpso_mu_sq_ne_one {E : Type} [Field E] {μ : E}
    (hμ : μ ^ 2 + μ + 1 = 0) (hμ1 : μ ≠ 1) : μ ^ 2 ≠ 1 := by
  intro h
  have hfac : (μ - 1) * (μ + 1) = 0 := by linear_combination h
  rcases mul_eq_zero.mp hfac with h1 | h1
  · exact hμ1 (sub_eq_zero.mp h1)
  · have hμeq : μ = -1 := by linear_combination h1
    rw [hμeq] at hμ
    have h10 : (1 : E) = 0 := by simp at hμ
    exact one_ne_zero h10

private theorem k328dpso_eigenspace_finrank_le {E : Type} [Field E] (_hE2 : ringChar E ≠ 2)
    (n : ℕ) (hn : n ≤ 3) (z : GL (Fin n ⊕ Fin n) E) (hz : z ∈ CFSG.Open.StatedSp n E)
    {μ : E} (hμ : μ ^ 2 + μ + 1 = 0) (hμ1 : μ ≠ 1) :
    Module.finrank E
        (Module.End.eigenspace (Matrix.toLin' (z : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) E)) μ)
      ≤ 4 := by
  have hμ2 : μ ^ 2 ≠ 1 := k328dpso_mu_sq_ne_one hμ hμ1
  have hle := k328dpso_eigenspace_finrank_le_n n z hz hμ2
  omega

private theorem k328dpso_eigenspace_reindex {E : Type} [Field E] {n : ℕ}
    (M : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) E) (μ : E) :
    (Module.End.eigenspace (Matrix.toLin' M) μ).map
        (LinearEquiv.funCongrLeft E E finSumFinEquiv.symm).toLinearMap
      = Module.End.eigenspace
          (Matrix.toLin' (Matrix.reindex finSumFinEquiv finSumFinEquiv M)) μ := by
  let G : (Fin n ⊕ Fin n → E) ≃ₗ[E] (Fin (n + n) → E) :=
    LinearEquiv.funCongrLeft E E finSumFinEquiv.symm
  have hcomp : ∀ w : Fin n ⊕ Fin n → E,
      G (Matrix.toLin' M w) =
        Matrix.toLin' (Matrix.reindex finSumFinEquiv finSumFinEquiv M) (G w) := by
    intro w
    have h := Matrix.toLin'_reindex (R := E) (e₁ := finSumFinEquiv) (e₂ := finSumFinEquiv) M
    have h3 := LinearMap.congr_fun h ((LinearEquiv.funCongrLeft E E finSumFinEquiv).symm w)
    simp only [LinearMap.comp_apply] at h3
    simp only [LinearEquiv.coe_toLinearMap] at h3
    rw [LinearEquiv.apply_symm_apply] at h3
    exact h3.symm
  ext v
  constructor
  · intro hv
    obtain ⟨w, hw, rfl⟩ := Submodule.mem_map.mp hv
    exact Module.End.mem_eigenspace_iff.mpr (by
      change Matrix.toLin' (Matrix.reindex finSumFinEquiv finSumFinEquiv M) (G w) = μ • G w
      rw [← hcomp, Module.End.mem_eigenspace_iff.mp hw, map_smul])
  · intro hv
    refine Submodule.mem_map.mpr ⟨G.symm v, Module.End.mem_eigenspace_iff.mpr ?_,
      G.apply_symm_apply v⟩
    apply G.injective
    rw [hcomp, G.apply_symm_apply, Module.End.mem_eigenspace_iff.mp hv, map_smul,
      G.apply_symm_apply]

private theorem k328dpso_eigenspace_ne_bot_or {E : Type} [Field E]
    (d : ℕ) (z : GL (Fin d) E) (hz3 : z ^ 3 = 1) (hz1 : z ≠ 1) {μ : E}
    (hμ : μ ^ 2 + μ + 1 = 0) :
    Module.End.eigenspace (Matrix.toLin' (z : Matrix (Fin d) (Fin d) E)) μ ≠ ⊥ ∨
      Module.End.eigenspace (Matrix.toLin' (z : Matrix (Fin d) (Fin d) E)) (μ ^ 2) ≠ ⊥ := by
  let T : Module.End E (Fin d → E) := Matrix.toLin' (z : Matrix (Fin d) (Fin d) E)
  have hz3mat : ((z : Matrix (Fin d) (Fin d) E)) ^ 3 = 1 := by
    rw [← Units.val_pow_eq_pow_val, hz3, Units.val_one]
  have hT3 : T ^ 3 = 1 := by
    dsimp [T]
    rw [← Matrix.toLin'_pow, hz3mat, Matrix.toLin'_one]
    exact Module.End.one_eq_id.symm
  have hT1 : T ≠ 1 := by
    intro hT
    apply hz1
    apply Units.ext
    refine Matrix.toLin'.injective ?_
    simpa [T, Module.End.one_eq_id, Matrix.toLin'_one] using hT
  have hμ3 : μ ^ 3 = 1 := by
    have h1 : (μ - 1) * (μ ^ 2 + μ + 1) = μ ^ 3 - 1 := by ring
    have h0 : μ ^ 3 - 1 = 0 := by rw [← h1, hμ, mul_zero]
    exact sub_eq_zero.mp h0
  have hμsum : μ ^ 2 + μ = -1 := by linear_combination hμ
  have hpoly : (Polynomial.X - Polynomial.C μ) * (Polynomial.X - Polynomial.C (μ^2)) =
      Polynomial.X^2 + Polynomial.X + Polynomial.C (1:E) := by
    have h3 : Polynomial.C μ * Polynomial.C (μ^2) = Polynomial.C (1:E) := by
      rw [← map_mul, show μ * μ^2 = 1 by linear_combination hμ3]
    have h1 : Polynomial.C μ + Polynomial.C (μ^2) = -Polynomial.C (1:E) := by
      rw [← map_add, show μ + μ^2 = -1 by linear_combination hμsum, map_neg, map_one]
    rw [show (Polynomial.X - Polynomial.C μ) * (Polynomial.X - Polynomial.C (μ^2)) =
        Polynomial.X^2 - (Polynomial.C μ + Polynomial.C (μ^2)) * Polynomial.X +
          Polynomial.C μ * Polynomial.C (μ^2) by ring, h1, h3]
    simp only [Polynomial.C_1]
    ring
  have hBC : (T - μ • 1) * (T - μ ^ 2 • 1) = T ^ 2 + T + 1 := by
    calc
      (T - μ • 1) * (T - μ ^ 2 • 1)
          = Polynomial.aeval T ((Polynomial.X - Polynomial.C μ) *
              (Polynomial.X - Polynomial.C (μ^2))) := by
            simp only [aeval_mul, aeval_sub, aeval_X, aeval_C,
              Module.algebraMap_end_eq_smul_id, Module.End.one_eq_id]
      _ = Polynomial.aeval T (Polynomial.X^2 + Polynomial.X + Polynomial.C (1:E)) := by
            rw [hpoly]
      _ = T ^ 2 + T + 1 := by
            simp only [aeval_add, aeval_X_pow, aeval_X, aeval_C,
              Module.algebraMap_end_eq_smul_id, Module.End.one_eq_id, one_smul]
  have hpoly2 : (Polynomial.X - Polynomial.C (1:E)) *
      (Polynomial.X^2 + Polynomial.X + Polynomial.C (1:E)) =
      Polynomial.X^3 - Polynomial.C (1:E) := by
    simp only [Polynomial.C_1]
    ring
  have hA : (T - 1) * (T ^ 2 + T + 1) = 0 := by
    have h1 : (T - 1) * (T ^ 2 + T + 1) =
        Polynomial.aeval T ((Polynomial.X - Polynomial.C (1:E)) *
          (Polynomial.X^2 + Polynomial.X + Polynomial.C (1:E))) := by
      simp only [aeval_mul, aeval_add, aeval_sub, aeval_X_pow, aeval_X, aeval_C,
        Module.algebraMap_end_eq_smul_id, Module.End.one_eq_id, one_smul]
    rw [h1, hpoly2]
    simp only [aeval_sub, aeval_X_pow, map_one, Module.End.one_eq_id]
    rw [hT3, Module.End.one_eq_id, sub_self]
  by_contra hcon
  rw [not_or] at hcon
  obtain ⟨h1, h2⟩ := hcon
  simp only [ne_eq, not_not] at h1 h2
  have hker1 : LinearMap.ker (T - μ • 1) = ⊥ := by
    rw [← Module.End.eigenspace_def]
    exact h1
  have hker2 : LinearMap.ker (T - μ ^ 2 • 1) = ⊥ := by
    rw [← Module.End.eigenspace_def]
    exact h2
  have hBtop : LinearMap.range (T - μ • 1) = ⊤ :=
    (LinearMap.ker_eq_bot_iff_range_eq_top).mp hker1
  have hCtop : LinearMap.range (T - μ ^ 2 • 1) = ⊤ :=
    (LinearMap.ker_eq_bot_iff_range_eq_top).mp hker2
  have hprod : (T - 1) * ((T - μ • 1) * (T - μ ^ 2 • 1)) = 0 := by
    rw [hBC]
    exact hA
  have hA0 : T - 1 = 0 := by
    apply LinearMap.ext
    intro w
    have hw : w ∈ LinearMap.range (T - μ • 1) := by rw [hBtop]; exact Submodule.mem_top
    obtain ⟨x, hx⟩ := hw
    have hx' : x ∈ LinearMap.range (T - μ ^ 2 • 1) := by rw [hCtop]; exact Submodule.mem_top
    obtain ⟨u, hu⟩ := hx'
    have h : (T - 1) w = 0 := by
      calc (T - 1) w = (T - 1) ((T - μ • 1) x) := by rw [← hx]
           _ = (T - 1) ((T - μ • 1) ((T - μ ^ 2 • 1) u)) := by rw [← hu]
           _ = ((T - 1) * ((T - μ • 1) * (T - μ ^ 2 • 1))) u := by
                 rw [Module.End.mul_apply, Module.End.mul_apply]
           _ = 0 := by rw [hprod, LinearMap.zero_apply]
    simpa using h
  exact hT1 (sub_eq_zero.mp hA0)

private theorem k328dpso_charP {K : Type} [Field K] [Finite K] {p f : ℕ} (hp : p.Prime)
    (_hf : 1 ≤ f) (hcard : Nat.card K = p ^ f) : CharP K p := by
  have : Fintype K := Fintype.ofFinite K
  obtain ⟨s, hs, m, hsp, hm⟩ := FiniteField.card' (K := K)
  rw [← Nat.card_eq_fintype_card, hcard] at hm
  have hsr : s = p := by
    have h1 : s ∣ p ^ f := by rw [hm]; exact dvd_pow_self s m.ne_zero
    exact (Nat.prime_dvd_prime_iff_eq hsp hp).mp (hsp.dvd_of_dvd_pow h1)
  rw [hsr] at hs
  exact hs

private theorem k328dpso_exists_omega_self {K : Type} [Field K] [Finite K]
    (hmod : Nat.card K % 3 = 1) :
    ∃ ω : K, ω ≠ 1 ∧ ω ^ 2 + ω + 1 = 0 := by
  have : Fintype K := Fintype.ofFinite K
  have h3dvdK : 3 ∣ Nat.card K - 1 := by
    have hdecomp : Nat.card K = 3 * (Nat.card K / 3) + 1 := by
      have := Nat.div_add_mod (Nat.card K) 3
      omega
    rw [hdecomp]
    have : 3 * (Nat.card K / 3) + 1 - 1 = 3 * (Nat.card K / 3) := by omega
    rw [this]
    exact dvd_mul_right 3 _
  have hunits : Nat.card Kˣ = Nat.card K - 1 := by
    have := Nat.card_eq_card_units_add_one K
    omega
  have h3dvd : 3 ∣ Nat.card Kˣ := by rw [hunits]; exact h3dvdK
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨u, hu⟩ := exists_prime_orderOf_dvd_card' (G := Kˣ) 3 h3dvd
  refine ⟨(u : K), ?_, ?_⟩
  · intro h1
    have : u = 1 := Units.ext h1
    rw [this, orderOf_one] at hu
    exact absurd hu (by norm_num)
  · have hu3 : u ^ 3 = 1 := orderOf_dvd_iff_pow_eq_one.mp (by rw [hu])
    have hω3 : (u : K) ^ 3 = 1 := by
      rw [← Units.val_pow_eq_pow_val, hu3, Units.val_one]
    have h : ((u : K) - 1) * ((u : K) ^ 2 + (u : K) + 1) = 0 := by
      have he : ((u : K) - 1) * ((u : K) ^ 2 + (u : K) + 1) = (u : K) ^ 3 - 1 := by ring
      rw [he, hω3, sub_self]
    exact (mul_eq_zero.mp h).resolve_left (sub_ne_zero.mpr (by
      intro h1
      have : u = 1 := Units.ext h1
      rw [this, orderOf_one] at hu
      exact absurd hu (by norm_num)))

private theorem k328dpso_lift_range {P W E : Type} [Group P] [Group W] [Field E] {m : ℕ}
    (SLhom : P →* Matrix.SpecialLinearGroup (Fin m) E) (φW : P →* W)
    (hφWsurj : Function.Surjective φW) (hφWker : φW.ker ≤ Subgroup.center P)
    (hle : SLhom.ker ≤ φW.ker) :
    ∃ φY : ↥SLhom.range →* W, Function.Surjective φY ∧
      φY.ker ≤ Subgroup.center ↥SLhom.range := by
  classical
  have hle' : SLhom.rangeRestrict.ker ≤ φW.ker := by
    rwa [MonoidHom.ker_rangeRestrict]
  set φY := SLhom.rangeRestrict.liftOfSurjective (MonoidHom.rangeRestrict_surjective _)
    ⟨φW, hle'⟩ with hφY
  have hcomp : ∀ p : P, φY (SLhom.rangeRestrict p) = φW p := fun p =>
    MonoidHom.liftOfRightInverse_comp_apply _ _ _ _ _
  refine ⟨φY, ?_, ?_⟩
  · intro w
    obtain ⟨p, hp⟩ := hφWsurj w
    exact ⟨SLhom.rangeRestrict p, by rw [hcomp, hp]⟩
  · intro y hy
    rw [Subgroup.mem_center_iff]
    intro y'
    obtain ⟨p, rfl⟩ := MonoidHom.rangeRestrict_surjective SLhom y
    have hp : p ∈ φW.ker := by
      rw [MonoidHom.mem_ker, ← hcomp p]
      exact hy
    obtain ⟨p', rfl⟩ := MonoidHom.rangeRestrict_surjective SLhom y'
    rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.1 (hφWker hp) p']

private theorem k328dpso_core
    (hEig : ∀ (E : Type) [Field E] [Finite E], ringChar E ≠ 2 → ∀ (n : ℕ)
      (Y : Subgroup (Matrix.SpecialLinearGroup (Fin n) E)), ⁅Y, Y⁆ = Y →
      ∀ z ∈ Y, (∀ y ∈ Y, Commute z y) → orderOf z = 3 → ∀ μ : E, μ ≠ 1 →
        Module.End.eigenspace (Matrix.toLin' (z : Matrix (Fin n) (Fin n) E)) μ ≠ ⊥ →
        Module.finrank E
            (Module.End.eigenspace (Matrix.toLin' (z : Matrix (Fin n) (Fin n) E)) μ) ≤ 4 →
        ∀ (W : Type) [Group W] (φ : ↥Y →* W), Function.Surjective φ →
          φ.ker ≤ Subgroup.center ↥Y → ¬ (LieModel W .PSL 3 2 2 ∨ LieModel W .PSU 3 2 3))
    (hChar3 : ∀ (E : Type) [Field E] [Finite E], ringChar E = 3 → ∀ (n : ℕ), n ≤ 4 →
      ∀ (Y : Subgroup (Matrix.SpecialLinearGroup (Fin n) E)), ⁅Y, Y⁆ = Y →
      ∀ z ∈ Y, (∀ y ∈ Y, Commute z y) → orderOf z = 3 →
        ∀ (W : Type) [Group W] (φ : ↥Y →* W), Function.Surjective φ →
          φ.ker ≤ Subgroup.center ↥Y → ¬ (LieModel W .PSL 3 2 2 ∨ LieModel W .PSU 3 2 3)) :
    ∀ (S : Type) [Group S] [Finite S], IsSimpleGroup S → ∀ n p f : ℕ, p ≠ 2 →
      (n = 2 ∨ (n = 3 ∧ p ≠ 3)) → LieModel S .PSp n p f → ¬ K328DetPosIn S := by
  intro S _ _ hS n p f hp2 hn hL
  rintro ⟨Z, X, hPos, hXne⟩
  have hn0 : n ≠ 0 := by rcases hn with h | ⟨h, _⟩ <;> omega
  obtain ⟨hadm, K, hfield, hfinite, hKcard, ⟨e⟩⟩ := hL.statedClassicalModel_of_ne_zero hn0
  let : Field K := hfield
  let : Finite K := hfinite
  have hp_prime : p.Prime := hadm.1
  have hf : 1 ≤ f := hadm.2.1
  have hPosG : Pos (StatedProj (StatedSp n K)) (Z.map e.toMonoidHom) (X.map e.toMonoidHom) :=
    pos_map e hPos
  let U := StatedSp n K
  let G := StatedProj U
  let π : U →* G := QuotientGroup.mk' ((StatedScalars (Fin n ⊕ Fin n) K).subgroupOf U)
  have hπ : Function.Surjective π := QuotientGroup.mk'_surjective _
  have hker : π.ker ≤ Subgroup.center U := by
    change (QuotientGroup.mk' ((StatedScalars (Fin n ⊕ Fin n) K).subgroupOf U)).ker ≤
      Subgroup.center U
    rw [QuotientGroup.ker_mk']
    exact statedScalars_subgroupOf_le_center U
  let Xbar : Subgroup G := X.map e.toMonoidHom
  have hqs : CFSG.Open.IsQuasisimple ↥Xbar := hPosG.2.2.2.2.1
  have hcenXbar : Nat.card (Subgroup.center ↥Xbar) = 3 := hPosG.2.2.2.2.2.1
  have hLieX : LieModel (↥Xbar ⧸ Subgroup.center ↥Xbar) .PSL 3 2 2 ∨
      LieModel (↥Xbar ⧸ Subgroup.center ↥Xbar) .PSU 3 2 3 := hPosG.2.2.2.2.2.2
  have hLperf : ⁅Xbar, Xbar⁆ = Xbar := by
    have : Group.IsPerfect ↥Xbar := ⟨hqs.1⟩
    exact Subgroup.commutator_eq_self
  let P : Subgroup U := ⁅Xbar.comap π, Xbar.comap π⁆
  have hP : Group.IsPerfect ↥P :=
    CFSG.GroupTheory.PerfectCover.isPerfect_commutator_comap π hπ hker hLperf
  have hmapP : P.map π = Xbar := CFSG.GroupTheory.PerfectCover.map_commutator_comap π hπ hLperf
  let πP : ↥P →* ↥Xbar := (π.comp P.subtype).codRestrict Xbar (fun q => by
    have hq : π (q : U) ∈ P.map π := Subgroup.mem_map_of_mem π q.2
    rwa [hmapP] at hq)
  have hπP : Function.Surjective πP := by
    intro x
    have hx : (x : G) ∈ P.map π := by rw [hmapP]; exact x.2
    obtain ⟨q, hq, hqx⟩ := Subgroup.mem_map.mp hx
    refine ⟨⟨q, hq⟩, ?_⟩
    apply Subtype.ext
    exact hqx
  have hkerP : πP.ker ≤ Subgroup.center ↥P := by
    intro q hq
    rw [Subgroup.mem_center_iff]
    intro r
    apply Subtype.ext
    have hqU : (q : U) ∈ Subgroup.center U := by
      apply hker
      rw [MonoidHom.mem_ker]
      exact congrArg (fun y : ↥Xbar => (y : G)) (MonoidHom.mem_ker.mp hq)
    exact Subgroup.mem_center_iff.mp hqU (r : U)
  obtain ⟨z, hzcenter, hzord⟩ := k328dpso_center_order_three πP hπP hkerP hP hcenXbar
  let W : Type := ↥Xbar ⧸ Subgroup.center ↥Xbar
  let φW : ↥P →* W := (QuotientGroup.mk' (Subgroup.center ↥Xbar)).comp πP
  have hφWsurj : Function.Surjective φW :=
    (QuotientGroup.mk'_surjective _).comp hπP
  have hφWker : φW.ker ≤ Subgroup.center ↥P := by
    have h := k328dpso_comap_center_le_center πP hkerP hP
    intro q hq
    exact h (Subgroup.mem_comap.mpr ((QuotientGroup.eq_one_iff _).mp hq))
  by_cases hp3eq : p = 3
  ·
    have hn2 : n = 2 := by
      rcases hn with h | ⟨h, hpne⟩
      · exact h
      · exact absurd hp3eq hpne
    have hcharK : CharP K 3 := k328dpso_charP (K := K) Nat.prime_three hf (by
      rw [← hp3eq]; exact hKcard)
    have hring3 : ringChar K = 3 := ringChar.eq_iff.mpr hcharK
    let SLhom : ↥P →* Matrix.SpecialLinearGroup (Fin (n+n)) K :=
      k328dpso_slHomP (RingHom.id K) n P hP
    let Y : Subgroup (Matrix.SpecialLinearGroup (Fin (n+n)) K) := SLhom.range
    have hSLinj : Function.Injective SLhom :=
      k328dpso_slHomP_injective (RingHom.id K) Function.injective_id n P hP
    have hY : ⁅Y, Y⁆ = Y := by
      have : Group.IsPerfect ↥P := hP
      have : Group.IsPerfect Y := Group.IsPerfect.range SLhom
      exact Subgroup.commutator_eq_self
    let zY : Matrix.SpecialLinearGroup (Fin (n+n)) K := SLhom z
    have hzYmem : zY ∈ Y := MonoidHom.mem_range.mpr ⟨z, rfl⟩
    have hzYne : zY ≠ 1 := by
      intro h
      have hz1 : z = 1 := hSLinj (h.trans (map_one SLhom).symm)
      rw [hz1, orderOf_one] at hzord
      exact absurd hzord (by norm_num)
    have hzYord : orderOf zY = 3 := by
      have hdvd : orderOf zY ∣ 3 := by
        have h1 : orderOf zY ∣ orderOf z := orderOf_map_dvd SLhom z
        rwa [hzord] at h1
      rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h1 | h3
      · exact absurd (orderOf_eq_one_iff.mp h1) hzYne
      · exact h3
    have hzYcomm : ∀ y ∈ Y, Commute zY y := by
      rintro y ⟨q, rfl⟩
      show zY * SLhom q = SLhom q * zY
      rw [← map_mul, ← map_mul]
      congr 1
      exact (Subgroup.mem_center_iff.mp hzcenter q).symm
    have hSLker : SLhom.ker ≤ φW.ker := by
      have hbot : SLhom.ker = ⊥ := (MonoidHom.ker_eq_bot_iff SLhom).mpr hSLinj
      rw [hbot]; exact bot_le
    obtain ⟨φY, hφYsurj, hφYker⟩ := k328dpso_lift_range SLhom φW hφWsurj hφWker hSLker
    exact hChar3 K hring3 (n+n) (by omega) Y hY zY hzYmem hzYcomm hzYord
      W φY hφYsurj hφYker hLieX
  ·
    have hp3 : p ≠ 3 := fun h => hp3eq h
    have hn3 : n ≤ 3 := by rcases hn with h | ⟨h, _⟩ <;> omega
    have hdata : ∃ (E : Type) (_ : Field E) (_ : Finite E) (ι : K →+* E) (ω : E),
        Function.Injective ι ∧ ringChar E ≠ 2 ∧ ω ≠ 1 ∧ ω ^ 2 + ω + 1 = 0 := by
      by_cases hmod1 : Nat.card K % 3 = 1
      · obtain ⟨ω, hω1, hωeq⟩ := k328dpso_exists_omega_self hmod1
        have hcharK : CharP K p := k328dpso_charP (K := K) hp_prime hf hKcard
        have hringp : ringChar K = p := ringChar.eq_iff.mpr hcharK
        exact ⟨K, hfield, hfinite, RingHom.id K, ω, Function.injective_id, by rw [hringp]; exact hp2,
          hω1, hωeq⟩
      · have hmod2 : Nat.card K % 3 = 2 := by
          have hlt : Nat.card K % 3 < 3 := Nat.mod_lt _ (by norm_num)
          have hne0 : Nat.card K % 3 ≠ 0 := by
            intro h0
            have hdvd : 3 ∣ Nat.card K := (Nat.dvd_iff_mod_eq_zero).mpr h0
            rw [hKcard] at hdvd
            have h3p : 3 ∣ p := Nat.prime_three.dvd_of_dvd_pow hdvd
            exact hp3 ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hp_prime).mp h3p).symm
          omega
        exact k328dpso_exists_omega K (by
          have hcharK : CharP K p := k328dpso_charP (K := K) hp_prime hf hKcard
          have hringp : ringChar K = p := ringChar.eq_iff.mpr hcharK
          rw [hringp]; exact hp2) hmod2
    obtain ⟨E, hEfield, hEfinite, ι, ω, hιinj, hEchar, hω1, hωeq⟩ := hdata
    let : Field E := hEfield
    let : Finite E := hEfinite
    let SLhom : ↥P →* Matrix.SpecialLinearGroup (Fin (n+n)) E := k328dpso_slHomP ι n P hP
    let Y : Subgroup (Matrix.SpecialLinearGroup (Fin (n+n)) E) := SLhom.range
    have hSLinj : Function.Injective SLhom := k328dpso_slHomP_injective ι hιinj n P hP
    have hY : ⁅Y, Y⁆ = Y := by
      have : Group.IsPerfect ↥P := hP
      have : Group.IsPerfect Y := Group.IsPerfect.range SLhom
      exact Subgroup.commutator_eq_self
    let zY : Matrix.SpecialLinearGroup (Fin (n+n)) E := SLhom z
    have hzYmem : zY ∈ Y := MonoidHom.mem_range.mpr ⟨z, rfl⟩
    have hzYne : zY ≠ 1 := by
      intro h
      have hz1 : z = 1 := hSLinj (h.trans (map_one SLhom).symm)
      rw [hz1, orderOf_one] at hzord
      exact absurd hzord (by norm_num)
    have hzYord : orderOf zY = 3 := by
      have hdvd : orderOf zY ∣ 3 := by
        have h1 : orderOf zY ∣ orderOf z := orderOf_map_dvd SLhom z
        rwa [hzord] at h1
      rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h1 | h3
      · exact absurd (orderOf_eq_one_iff.mp h1) hzYne
      · exact h3
    have hzYcomm : ∀ y ∈ Y, Commute zY y := by
      rintro y ⟨q, rfl⟩
      show zY * SLhom q = SLhom q * zY
      rw [← map_mul, ← map_mul]
      congr 1
      exact (Subgroup.mem_center_iff.mp hzcenter q).symm
    have hSLker : SLhom.ker ≤ φW.ker := by
      have hbot : SLhom.ker = ⊥ := (MonoidHom.ker_eq_bot_iff SLhom).mpr hSLinj
      rw [hbot]; exact bot_le
    obtain ⟨φY, hφYsurj, hφYker⟩ := k328dpso_lift_range SLhom φW hφWsurj hφWker hSLker
    let zE : GL (Fin n ⊕ Fin n) E :=
      Matrix.GeneralLinearGroup.map ι ((z : U) : GL (Fin n ⊕ Fin n) K)
    have hzE_mem : zE ∈ StatedSp n E :=
      CFSG.Open.StatedAPI.map_mem_statedSp ι (z : U).2
    have hzYmat : (zY : Matrix (Fin (n+n)) (Fin (n+n)) E) =
        Matrix.reindex finSumFinEquiv finSumFinEquiv
          (zE : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) E) := rfl
    have hzY3 : zY ^ 3 = 1 := orderOf_dvd_iff_pow_eq_one.mp (by rw [hzYord])
    have hzYglne : (zY : GL (Fin (n+n)) E) ≠ 1 := by
      intro h
      apply hzYne
      apply Subtype.ext
      have h' := congrArg (fun x : GL (Fin (n+n)) E =>
        (x : Matrix (Fin (n+n)) (Fin (n+n)) E)) h
      simpa using h'
    have hzY3gl : (zY : GL (Fin (n+n)) E) ^ 3 = 1 := by
      have h := congrArg (fun x : Matrix.SpecialLinearGroup (Fin (n+n)) E =>
        (x : GL (Fin (n+n)) E)) hzY3
      simpa using h
    have hnz := k328dpso_eigenspace_ne_bot_or (n+n) (zY : GL (Fin (n+n)) E) hzY3gl hzYglne
      (μ := ω) hωeq
    have hω2ne1 : ω ^ 2 ≠ 1 := k328dpso_mu_sq_ne_one hωeq hω1
    have hω2eq : (ω ^ 2) ^ 2 + ω ^ 2 + 1 = 0 := by
      have hω3 : ω ^ 3 = 1 := by linear_combination (ω - 1) * hωeq
      linear_combination hωeq + ω * hω3
    rcases hnz with hbot | hbot
    · have heig : Module.End.eigenspace (Matrix.toLin' (zY : Matrix (Fin (n+n)) (Fin (n+n)) E)) ω ≠ ⊥ :=
        hbot
      have hfin : Module.finrank E
          (Module.End.eigenspace (Matrix.toLin' (zY : Matrix (Fin (n+n)) (Fin (n+n)) E)) ω) ≤ 4 := by
        rw [hzYmat, ← k328dpso_eigenspace_reindex (n := n)
          (M := (zE : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) E)) ω]
        rw [LinearEquiv.finrank_map_eq]
        exact k328dpso_eigenspace_finrank_le hEchar n hn3 zE hzE_mem hωeq hω1
      exact hEig E hEchar (n+n) Y hY zY hzYmem hzYcomm hzYord ω hω1 heig hfin
        W φY hφYsurj hφYker hLieX
    · have heig : Module.End.eigenspace (Matrix.toLin' (zY : Matrix (Fin (n+n)) (Fin (n+n)) E)) (ω^2) ≠ ⊥ :=
        hbot
      have hfin : Module.finrank E
          (Module.End.eigenspace (Matrix.toLin' (zY : Matrix (Fin (n+n)) (Fin (n+n)) E)) (ω^2)) ≤ 4 := by
        rw [hzYmat, ← k328dpso_eigenspace_reindex (n := n)
          (M := (zE : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) E)) (ω^2)]
        rw [LinearEquiv.finrank_map_eq]
        exact k328dpso_eigenspace_finrank_le hEchar n hn3 zE hzE_mem hω2eq hω2ne1
      exact hEig E hEchar (n+n) Y hY zY hzYmem hzYcomm hzYord (ω^2) hω2ne1 heig hfin
        W φY hφYsurj hφYker hLieX

private theorem k328dplo_mem_center_of_commutator_mem_center {H : Type*} [Group H]
    (hH : commutator H = ⊤) {x : H}
    (hx : ∀ y : H, x * y * x⁻¹ * y⁻¹ ∈ Subgroup.center H) : x ∈ Subgroup.center H := by
  let φ : H →* Subgroup.center H :=
    { toFun := fun y => ⟨x * y * x⁻¹ * y⁻¹, hx y⟩
      map_one' := by
        apply Subtype.ext
        simp
      map_mul' := fun y z => by
        apply Subtype.ext
        have hb := (Subgroup.mem_center_iff.1 (hx z)) y⁻¹
        change x * (y * z) * x⁻¹ * (y * z)⁻¹ =
          (x * y * x⁻¹ * y⁻¹) * (x * z * x⁻¹ * z⁻¹)
        calc x * (y * z) * x⁻¹ * (y * z)⁻¹
            = x * y * x⁻¹ * ((x * z * x⁻¹ * z⁻¹) * y⁻¹) := by group
          _ = x * y * x⁻¹ * (y⁻¹ * (x * z * x⁻¹ * z⁻¹)) := by rw [← hb]
          _ = (x * y * x⁻¹ * y⁻¹) * (x * z * x⁻¹ * z⁻¹) := by group }
  have hle : commutator H ≤ φ.ker := Abelianization.commutator_subset_ker φ
  rw [hH] at hle
  rw [Subgroup.mem_center_iff]
  intro y
  have h1 : φ y = 1 := hle (Subgroup.mem_top y)
  have h2 := congrArg Subtype.val h1
  change x * y * x⁻¹ * y⁻¹ = 1 at h2
  calc y * x = (x * y * x⁻¹ * y⁻¹)⁻¹ * (x * y) := by group
    _ = x * y := by rw [h2]; simp

private theorem k328dplo_comap_center_of_surjective {H H' : Type*} [Group H] [Group H']
    (hH : commutator H = ⊤) (ψ : H →* H') (hψ : Function.Surjective ψ)
    (hk : ψ.ker ≤ Subgroup.center H) :
    (Subgroup.center H').comap ψ = Subgroup.center H := by
  ext x
  rw [Subgroup.mem_comap]
  constructor
  · intro hx
    refine k328dplo_mem_center_of_commutator_mem_center hH fun y => hk ?_
    have hc : ψ y * ψ x = ψ x * ψ y := (Subgroup.mem_center_iff.1 hx) (ψ y)
    rw [MonoidHom.mem_ker, map_mul, map_mul, map_mul, map_inv, map_inv, ← hc]
    group
  · intro hx
    rw [Subgroup.mem_center_iff]
    intro z
    obtain ⟨y, rfl⟩ := hψ z
    rw [← map_mul, ← map_mul, (Subgroup.mem_center_iff.1 hx) y]

private theorem k328dplo_descent
    {U S : Type} [Group U] [Group S] [Finite U]
    (π : U →* S) (hπ : Function.Surjective π) (hker : π.ker ≤ Subgroup.center U)
    {X : Subgroup S} (hX : commutator ↥X = ⊤) :
    ∃ (Y : Subgroup U) (ψ : Y →* X), (⁅Y, Y⁆ = Y) ∧ Y.map π = X ∧
      Function.Surjective ψ ∧ ψ.ker ≤ Subgroup.center ↥Y := by
  classical
  have : Group.IsPerfect ↥X := ⟨hX⟩
  let P : Subgroup U := X.comap π
  have hPmap : P.map π = X := by
    change (X.comap π).map π = X
    rw [Subgroup.map_comap_eq, MonoidHom.range_eq_top.mpr hπ, top_inf_eq]
  let φ : P →* X := (π.comp P.subtype).codRestrict X (fun p => p.2)
  have hφ : Function.Surjective φ := by
    intro x
    obtain ⟨u, hu⟩ := hπ (x : S)
    refine ⟨⟨u, ?_⟩, ?_⟩
    · rw [Subgroup.mem_comap]; rw [hu]; exact x.2
    · apply Subtype.ext; exact hu
  let Y : Subgroup U := (CFSG.RankThreeCoreUniqueness.Helpers.perfectResidual P).map P.subtype
  have : Group.IsPerfect ↥(CFSG.RankThreeCoreUniqueness.Helpers.perfectResidual P) :=
    CFSG.RankThreeCoreUniqueness.Helpers.finite_perfectResidual_isPerfect (G := P)
  have hYperf : ⁅Y, Y⁆ = Y :=
    Subgroup.isPerfect_iff.mp (show Group.IsPerfect ↥Y from Group.IsPerfect.map P.subtype)
  have hYmap : Y.map π = X := by
    have h1 : Y.map π = (CFSG.RankThreeCoreUniqueness.Helpers.perfectResidual P).map
        (π.comp P.subtype) := by
      change ((CFSG.RankThreeCoreUniqueness.Helpers.perfectResidual P).map P.subtype).map π = _
      rw [Subgroup.map_map]
    rw [h1]
    have h2 : π.comp P.subtype = X.subtype.comp φ := by ext; rfl
    rw [h2, ← Subgroup.map_map]
    have h3 : (CFSG.RankThreeCoreUniqueness.Helpers.perfectResidual P).map φ = ⊤ :=
      CFSG.RankThreeCoreUniqueness.Helpers.finite_perfectResidual_surjects_to_perfect_image φ hφ
    rw [h3]
    ext x
    simp only [Subgroup.mem_map, Subgroup.mem_top, true_and]
    exact ⟨fun ⟨y, hy⟩ => hy ▸ y.2, fun hx => ⟨⟨x, hx⟩, rfl⟩⟩
  let ψ : Y →* X := (π.comp Y.subtype).codRestrict X (fun y => by
    have : π (Y.subtype y) ∈ Y.map π := Subgroup.mem_map_of_mem π y.2
    rwa [hYmap] at this)
  have hψ : Function.Surjective ψ := by
    intro x
    have hx : (x : S) ∈ Y.map π := by rw [hYmap]; exact x.2
    obtain ⟨y, hy, hxy⟩ := Subgroup.mem_map.mp hx
    exact ⟨⟨y, hy⟩, Subtype.ext hxy⟩
  have hψker : ψ.ker ≤ Subgroup.center ↥Y := by
    intro y hy
    have hyker : (y : U) ∈ π.ker := by
      rw [MonoidHom.mem_ker]
      exact congrArg Subtype.val (MonoidHom.mem_ker.mp hy)
    have hcen : (y : U) ∈ Subgroup.center U := hker hyker
    rw [Subgroup.mem_center_iff]
    intro z
    apply Subtype.ext
    exact Subgroup.mem_center_iff.mp hcen (z : U)
  exact ⟨Y, ψ, hYperf, hYmap, hψ, hψker⟩

private theorem k328dplo_charP_of_card {K : Type} [Field K] [Finite K] {p f : ℕ}
    (hp : p.Prime) (hK : Nat.card K = p ^ f) : CharP K p := by
  let : Fintype K := Fintype.ofFinite K
  obtain ⟨q, hq, ⟨m, hqprime, hcard⟩⟩ := FiniteField.card' K
  have hqf : q ^ (m : ℕ) = p ^ f := by
    rw [← hcard, ← Nat.card_eq_fintype_card, hK]
  have hq_dvd : q ∣ p ^ f := by rw [← hqf]; exact dvd_pow_self q m.ne_zero
  have hq_eq_p : q = p :=
    (Nat.prime_dvd_prime_iff_eq hqprime hp).1 (hqprime.dvd_of_dvd_pow hq_dvd)
  rwa [hq_eq_p] at hq

private theorem k328dplo_omega (K : Type) [Field K] [Finite K] (p : ℕ) [Fact p.Prime]
    [CharP K p] (hp3 : p ≠ 3) :
    ∃ ω : FiniteField.Extension K p 2, ω ^ 2 + ω + 1 = 0 := by
  let : Fintype K := Fintype.ofFinite K
  have hEcard : Nat.card (FiniteField.Extension K p 2) = Nat.card K ^ 2 := FiniteField.natCard_extension K p 2
  obtain ⟨n, _hpn, hcard⟩ := FiniteField.card p (K := K)
  have hKcard : Nat.card K = p ^ (n : ℕ) := by rw [Nat.card_eq_fintype_card, hcard]
  have h3dvd : 3 ∣ Nat.card (FiniteField.Extension K p 2) - 1 := by
    rw [hEcard, hKcard]
    have hpmod : p % 3 = 1 ∨ p % 3 = 2 := by
      have h3 : p % 3 ≠ 0 := by
        intro h
        have hdiv : 3 ∣ p := Nat.dvd_of_mod_eq_zero h
        have h3p : 3 = p := (Nat.prime_dvd_prime_iff_eq Nat.prime_three Fact.out).1 hdiv
        exact hp3 h3p.symm
      omega
    have hp2 : p ^ 2 % 3 = 1 := by
      rcases hpmod with h | h
      · simp [show p ^ 2 = p * p by ring, Nat.mul_mod, h]
      · simp [show p ^ 2 = p * p by ring, Nat.mul_mod, h]
    have hmod : (p ^ (n : ℕ)) ^ 2 % 3 = 1 := by
      rw [show (p ^ (n : ℕ)) ^ 2 = (p ^ 2) ^ (n : ℕ) by ring, Nat.pow_mod, hp2, one_pow,
        Nat.mod_eq_of_lt (by norm_num)]
    omega
  have h3dvd' : 3 ∣ Nat.card (FiniteField.Extension K p 2)ˣ := by rwa [Nat.card_units]
  obtain ⟨ω, hω⟩ := exists_prime_orderOf_dvd_card' (G := (FiniteField.Extension K p 2)ˣ) 3 h3dvd'
  have hω3 : (ω : (FiniteField.Extension K p 2)) ^ 3 = 1 := by
    have hω3' : ω ^ 3 = 1 := by simpa only [hω] using pow_orderOf_eq_one ω
    calc (ω : (FiniteField.Extension K p 2)) ^ 3 = ((ω ^ 3 : (FiniteField.Extension K p 2)ˣ) : (FiniteField.Extension K p 2)) := (Units.val_pow_eq_pow_val ω 3).symm
      _ = ((1 : (FiniteField.Extension K p 2)ˣ) : (FiniteField.Extension K p 2)) := by rw [hω3']
      _ = 1 := rfl
  have hω1 : (ω : (FiniteField.Extension K p 2)) ≠ 1 := by
    intro h
    have h1 : ω = 1 := Units.ext h
    rw [h1, orderOf_one] at hω
    norm_num at hω
  refine ⟨(ω : (FiniteField.Extension K p 2)), ?_⟩
  have hprod : ((ω : (FiniteField.Extension K p 2)) - 1) * ((ω : (FiniteField.Extension K p 2)) ^ 2 + (ω : (FiniteField.Extension K p 2)) + 1) = 0 := by
    have : ((ω : (FiniteField.Extension K p 2)) - 1) * ((ω : (FiniteField.Extension K p 2)) ^ 2 + (ω : (FiniteField.Extension K p 2)) + 1) = (ω : (FiniteField.Extension K p 2)) ^ 3 - 1 := by ring
    rw [this, hω3]; ring
  rcases mul_eq_zero.mp hprod with h | h
  · exact absurd (sub_eq_zero.mp h) hω1
  · exact h

private theorem k328dplo_frob_omega {K : Type} [Field K] [Finite K] (p : ℕ) [Fact p.Prime]
    [CharP K p] {ω : FiniteField.Extension K p 2} (hω : ω ^ 2 + ω + 1 = 0)
    (hq : Nat.card K % 3 = 2) :
    FiniteField.Extension.frob K p 2 ω = ω ^ 2 := by
  rw [FiniteField.Extension.frob_apply]
  have hω3 : ω ^ 3 = 1 := by
    have h : ω ^ 3 - 1 = 0 := by
      calc ω ^ 3 - 1 = (ω - 1) * (ω ^ 2 + ω + 1) := by ring
        _ = (ω - 1) * 0 := by rw [hω]
        _ = 0 := by ring
    linear_combination h
  have hpow : ω ^ Nat.card K = ω ^ (Nat.card K % 3) := by
    conv_lhs => rw [← Nat.mod_add_div (Nat.card K) 3]
    rw [pow_add, pow_mul, hω3, one_pow, mul_one]
  rw [hpow, hq]

private noncomputable def k328dplo_phi {K E : Type} [Field K] [Field E] [Algebra K E]
    (n : ℕ) (σ : E ≃ₐ[K] E) : (Fin n → E) ≃ₗ[K] (Fin n → E) :=
  LinearEquiv.piCongrRight (fun _ : Fin n => σ.toLinearEquiv)

private theorem k328dplo_phi_apply {K E : Type} [Field K] [Field E] [Algebra K E]
    (n : ℕ) (σ : E ≃ₐ[K] E) (v : Fin n → E) :
    k328dplo_phi n σ v = fun i => σ (v i) := rfl

private theorem k328dplo_phi_smul {K E : Type} [Field K] [Field E] [Algebra K E]
    (n : ℕ) (σ : E ≃ₐ[K] E) (ω : E) (v : Fin n → E) :
    k328dplo_phi n σ (ω • v) = σ ω • k328dplo_phi n σ v := by
  ext i
  simp [k328dplo_phi_apply]

private theorem k328dplo_phi_mulVec {K E : Type} [Field K] [Field E] [Algebra K E]
    (n : ℕ) (σ : E ≃ₐ[K] E) {z : Matrix (Fin n) (Fin n) K} (v : Fin n → E) :
    k328dplo_phi n σ ((z.map (algebraMap K E)) *ᵥ v) =
      (z.map (algebraMap K E)) *ᵥ (k328dplo_phi n σ v) := by
  ext i
  simp only [k328dplo_phi_apply, Matrix.mulVec, dotProduct, Matrix.map_apply]
  rw [map_sum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [map_mul, σ.commutes]

private theorem k328dplo_eigen_bound {K E : Type} [Field K] [Field E] [Algebra K E]
    [Module.Finite K E] {n : ℕ}
    (hfin : Module.finrank K E = 2) (σ : E ≃ₐ[K] E) (p : ℕ) [Fact p.Prime] [CharP E p]
    (hp3 : p ≠ 3) {ω : E} (hσω : σ ω = ω ^ 2) (hω : ω ^ 2 + ω + 1 = 0)
    (z : Matrix (Fin n) (Fin n) K) :
    2 * Module.finrank E
        (Module.End.eigenspace (Matrix.toLin' (z.map (algebraMap K E))) ω) ≤ n := by
  classical
  have hωne : ω ≠ ω ^ 2 := by
    intro h
    have h1 : ω * (ω - 1) = 0 := by
      calc ω * (ω - 1) = ω ^ 2 - ω := by ring
        _ = 0 := by rw [← h, sub_self]
    rcases mul_eq_zero.mp h1 with h0 | h1
    · rw [h0] at hω; norm_num at hω
    · have hω1 : ω = 1 := sub_eq_zero.mp h1
      rw [hω1] at hω
      have h3 : (3 : E) = 0 := by norm_num at hω ⊢; exact hω
      have hpdvd : p ∣ 3 := (CharP.cast_eq_zero_iff E p 3).mp h3
      have hp_eq : p = 3 := (Nat.prime_dvd_prime_iff_eq Fact.out Nat.prime_three).1 hpdvd
      exact hp3 hp_eq
  set M : Matrix (Fin n) (Fin n) E := z.map (algebraMap K E) with hM
  set T : Module.End E (Fin n → E) := Matrix.toLin' M with hT
  set Vω : Submodule E (Fin n → E) := T.eigenspace ω with hVωdef
  set Vω2 : Submodule E (Fin n → E) := T.eigenspace (ω ^ 2) with hVω2def
  have hmap : (Vω.restrictScalars K).map (k328dplo_phi n σ).toLinearMap ≤
      Vω2.restrictScalars K := by
    rintro w ⟨v, hv, rfl⟩
    rw [hVωdef] at hv
    rw [hVω2def]
    change v ∈ T.eigenspace ω at hv
    change k328dplo_phi n σ v ∈ T.eigenspace (ω ^ 2)
    rw [Module.End.mem_eigenspace_iff] at hv ⊢
    have hv' : z.map (algebraMap K E) *ᵥ v = ω • v := by
      rw [← hM, ← Matrix.toLin'_apply, ← hT]; exact hv
    exact (k328dplo_phi_mulVec n σ v).symm.trans (by rw [hv', k328dplo_phi_smul, hσω])
  have hσω' : σ.symm (ω ^ 2) = ω := by
    apply σ.injective
    rw [σ.apply_symm_apply, hσω]
  have hmap' : (Vω2.restrictScalars K).map (k328dplo_phi n σ.symm).toLinearMap ≤
      Vω.restrictScalars K := by
    rintro w ⟨v, hv, rfl⟩
    rw [hVω2def] at hv
    rw [hVωdef]
    change v ∈ T.eigenspace (ω ^ 2) at hv
    change k328dplo_phi n σ.symm v ∈ T.eigenspace ω
    rw [Module.End.mem_eigenspace_iff] at hv ⊢
    have hv' : z.map (algebraMap K E) *ᵥ v = ω ^ 2 • v := by
      rw [← hM, ← Matrix.toLin'_apply, ← hT]; exact hv
    exact (k328dplo_phi_mulVec n σ.symm v).symm.trans (by rw [hv', k328dplo_phi_smul, hσω'])
  have hfin_eq : Module.finrank K (Vω.restrictScalars K) =
      Module.finrank K (Vω2.restrictScalars K) := by
    apply le_antisymm
    · calc Module.finrank K (Vω.restrictScalars K)
          = Module.finrank K ((Vω.restrictScalars K).map (k328dplo_phi n σ).toLinearMap) :=
            (LinearEquiv.finrank_map_eq _ _).symm
        _ ≤ Module.finrank K (Vω2.restrictScalars K) := Submodule.finrank_mono hmap
    · calc Module.finrank K (Vω2.restrictScalars K)
          = Module.finrank K ((Vω2.restrictScalars K).map (k328dplo_phi n σ.symm).toLinearMap) :=
            (LinearEquiv.finrank_map_eq _ _).symm
        _ ≤ Module.finrank K (Vω.restrictScalars K) := Submodule.finrank_mono hmap'
  have hVω : Module.finrank K (Vω.restrictScalars K) = 2 * Module.finrank E Vω := by
    change Module.finrank K (↥Vω) = 2 * Module.finrank E (↥Vω)
    rw [← Module.finrank_mul_finrank K E (↥Vω), hfin]
  have hVω2 : Module.finrank K (Vω2.restrictScalars K) = 2 * Module.finrank E Vω2 := by
    change Module.finrank K (↥Vω2) = 2 * Module.finrank E (↥Vω2)
    rw [← Module.finrank_mul_finrank K E (↥Vω2), hfin]
  have hdisj : Disjoint (Vω.restrictScalars K) (Vω2.restrictScalars K) := by
    rw [disjoint_iff]
    rw [eq_bot_iff]
    rintro v hv
    rw [Submodule.mem_inf] at hv
    obtain ⟨hv1, hv2⟩ := hv
    rw [hVωdef] at hv1
    rw [hVω2def] at hv2
    change v ∈ T.eigenspace ω at hv1
    change v ∈ T.eigenspace (ω ^ 2) at hv2
    rw [Module.End.mem_eigenspace_iff] at hv1 hv2
    rw [Submodule.mem_bot]
    have h : (ω - ω ^ 2) • v = 0 := by rw [sub_smul, ← hv1, hv2, sub_self]
    rcases smul_eq_zero.mp h with h0 | h0
    · exact absurd (sub_eq_zero.mp h0) hωne
    · exact h0
  let W : Submodule K (Fin n → E) := Vω.restrictScalars K ⊔ Vω2.restrictScalars K
  have hsup : Module.finrank K W ≤ 2 * n := by
    calc Module.finrank K W
        ≤ Module.finrank K (⊤ : Submodule K (Fin n → E)) := Submodule.finrank_mono le_top
      _ = Module.finrank K (Fin n → E) := finrank_top K (Fin n → E)
      _ = 2 * n := by
        rw [Module.finrank_pi_fintype, Finset.sum_const, Finset.card_fin, hfin]
        simp [Nat.mul_comm]
  have hsum : Module.finrank K W =
      Module.finrank K (Vω.restrictScalars K) + Module.finrank K (Vω2.restrictScalars K) := by
    have h := Submodule.finrank_sup_add_finrank_inf_eq (Vω.restrictScalars K) (Vω2.restrictScalars K)
    rw [hdisj.eq_bot, finrank_bot, add_zero] at h
    exact h
  rw [hVω, hVω2] at hsum
  rw [← hfin_eq] at hVω2
  omega

private theorem k328domo_omega_in_K (K : Type) [Field K] [Finite K] (_h3 : (3 : K) ≠ 0)
    (hmod : Nat.card K % 3 = 1) : ∃ ω : K, ω ≠ 1 ∧ ω ^ 2 + ω + 1 = 0 := by
  have : Fintype K := Fintype.ofFinite K
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hq : Nat.card K = 3 * (Nat.card K / 3) + 1 := by
    have h := Nat.mod_add_div (Nat.card K) 3
    omega
  have hunits : Nat.card Kˣ = 3 * (Nat.card K / 3) := by
    rw [Nat.card_units, hq]
    omega
  have h3dvd : 3 ∣ Nat.card Kˣ := ⟨Nat.card K / 3, hunits⟩
  obtain ⟨u, hu⟩ := exists_prime_orderOf_dvd_card' (G := Kˣ) 3 h3dvd
  have hu3 : u ^ 3 = 1 := orderOf_dvd_iff_pow_eq_one.mp (hu ▸ dvd_rfl)
  have hu1 : u ≠ 1 := by
    intro h; rw [h, orderOf_one] at hu; omega
  refine ⟨(u : K), ?_, ?_⟩
  · intro h
    exact hu1 (Units.ext h)
  · have hval : ((u : K)) ^ 3 = 1 := by
      rw [← Units.val_pow_eq_pow_val, hu3, Units.val_one]
    have hfac : ((u : K) - 1) * (((u : K)) ^ 2 + (u : K) + 1) = 0 := by
      have h : ((u : K)) ^ 3 - 1 = ((u : K) - 1) * (((u : K)) ^ 2 + (u : K) + 1) := by ring
      rw [hval, sub_self] at h
      exact h.symm
    rcases mul_eq_zero.mp hfac with h | h
    · exact absurd (sub_eq_zero.mp h) (fun hh => hu1 (Units.ext hh))
    · exact h

private theorem k328domo_irreducible_cubePoly (K : Type) [Field K] [Finite K]
    (h3 : (3 : K) ≠ 0) (hmod : Nat.card K % 3 = 2) :
    Irreducible (Polynomial.X ^ 2 + Polynomial.X + 1 : Polynomial K) := by
  have : Fintype K := Fintype.ofFinite K
  refine Polynomial.irreducible_of_degree_le_three_of_not_isRoot ?_ ?_
  · have hdeg : (Polynomial.X ^ 2 + Polynomial.X + 1 : Polynomial K).natDegree = 2 := by
      compute_degree!
    rw [hdeg]; decide
  · rintro x hx
    simp only [Polynomial.IsRoot, Polynomial.eval_add, Polynomial.eval_pow, Polynomial.eval_X,
      Polynomial.eval_one] at hx
    have hx0 : x ≠ 0 := by rintro rfl; simp at hx
    have hx3 : x ^ 3 = 1 := by linear_combination (x - 1) * hx
    let u : Kˣ := Units.mk0 x hx0
    have hu3 : u ^ 3 = 1 := by ext; simpa [u] using hx3
    have hu1 : u ≠ 1 := by
      intro h
      have hx1 : x = 1 := congrArg Units.val h
      rw [hx1] at hx
      exact h3 (by linear_combination hx)
    have hord : orderOf u = 3 := orderOf_eq_prime hu3 hu1
    have hdvd : 3 ∣ Nat.card Kˣ := hord ▸ orderOf_dvd_natCard u
    rw [Nat.card_units] at hdvd
    have hq : Nat.card K % 3 = 1 := by
      have h1 : Nat.card K = Nat.card Kˣ + 1 := Nat.card_eq_card_units_add_one K
      have h2 : 0 < Nat.card K := Nat.card_pos
      omega
    omega

private theorem k328domo_exists_omega (K : Type) [Field K] [Finite K] {p f : ℕ}
    [Fact p.Prime] (hp2 : p ≠ 2) (hp3 : p ≠ 3) (hcard : Nat.card K = p ^ f) :
    ∃ (E : Type) (_ : Field E) (_ : Finite E) (ι : K →+* E) (ω : E),
      Function.Injective ι ∧ ringChar E ≠ 2 ∧ ω ≠ 1 ∧ ω ^ 2 + ω + 1 = 0 := by
  have : Fintype K := Fintype.ofFinite K
  have : CharP K p := charP_of_card_eq_prime_pow (p := p) (f := f)
    (by rw [← Nat.card_eq_fintype_card]; exact hcard)
  have hp : p.Prime := Fact.out
  have hchar : ringChar K ≠ 2 := by
    have hrc : ringChar K = p := ringChar.eq K p
    rw [hrc]; exact hp2
  have h3 : (3 : K) ≠ 0 := by
    intro h0
    have hdvd : p ∣ 3 := (CharP.cast_eq_zero_iff K p 3).mp h0
    rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h | h
    · exact hp.ne_one h
    · exact hp3 h
  have hres : Nat.card K % 3 = 1 ∨ Nat.card K % 3 = 2 := by
    have hne0 : Nat.card K % 3 ≠ 0 := by
      rw [hcard]
      intro h0
      have h3dvd : 3 ∣ p ^ f := Nat.dvd_of_mod_eq_zero h0
      have h3p : 3 ∣ p := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3dvd
      exact hp3 ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).mp h3p).symm
    have hlt : Nat.card K % 3 < 3 := Nat.mod_lt _ (by norm_num)
    omega
  rcases hres with hmod | hmod
  · obtain ⟨ω, hω1, hω2⟩ := k328domo_omega_in_K K h3 hmod
    exact ⟨K, inferInstance, inferInstance, RingHom.id K, ω, fun _ _ h => h, hchar, hω1, hω2⟩
  · let fpoly : Polynomial K := Polynomial.X ^ 2 + Polynomial.X + 1
    have hf_irr : Irreducible fpoly := k328domo_irreducible_cubePoly K h3 hmod
    have hmonic : fpoly.Monic := by
      show (Polynomial.X ^ 2 + Polynomial.X + 1 : Polynomial K).Monic
      have hdeg : (Polynomial.X + (1 : Polynomial K)).degree < (2 : WithBot ℕ) := by
        have h : (Polynomial.X + (1 : Polynomial K)).degree = 1 := by
          simpa using Polynomial.degree_X_add_C (1 : K)
        rw [h]; norm_num
      rw [add_assoc]
      exact Polynomial.monic_X_pow_add (n := 2) hdeg
    have hdeg2 : fpoly.natDegree = 2 := by
      show (Polynomial.X ^ 2 + Polynomial.X + 1 : Polynomial K).natDegree = 2
      compute_degree!
    have hdegpos : 0 < fpoly.degree := by
      rw [Polynomial.degree_eq_natDegree hmonic.ne_zero, hdeg2]; norm_num
    have : Fact (Irreducible fpoly) := ⟨hf_irr⟩
    have : Finite (AdjoinRoot fpoly) := by
      have : Module.Finite K (AdjoinRoot fpoly) :=
        Polynomial.Monic.finite_adjoinRoot hmonic
      exact Module.finite_of_finite K
    have hroot : (AdjoinRoot.root fpoly) ^ 2 + AdjoinRoot.root fpoly + 1 = 0 := by
      have := AdjoinRoot.eval₂_root fpoly
      simpa [fpoly] using this
    have hinj : Function.Injective (AdjoinRoot.of fpoly) :=
      AdjoinRoot.of.injective_of_monic_of_degree_pos hmonic hdegpos
    have : CharP (AdjoinRoot fpoly) p := charP_of_injective_ringHom hinj p
    have hcharE : ringChar (AdjoinRoot fpoly) = p := ringChar.eq _ p
    refine ⟨AdjoinRoot fpoly, inferInstance, inferInstance, AdjoinRoot.of fpoly,
      AdjoinRoot.root fpoly, hinj, ?_, ?_, hroot⟩
    · rw [hcharE]; exact hp2
    · intro hroot1
      rw [hroot1] at hroot
      norm_num at hroot
      exact h3 ((AdjoinRoot.of fpoly).injective (by
        calc (AdjoinRoot.of fpoly) (3 : K) = (3 : AdjoinRoot fpoly) := map_ofNat (AdjoinRoot.of fpoly) 3
          _ = 0 := hroot
          _ = (AdjoinRoot.of fpoly) (0 : K) := (map_zero (AdjoinRoot.of fpoly)).symm))

private theorem k328domo_mem_center_of_commutator_mem_center {P : Type*} [Group P]
    (hP : Group.IsPerfect P) {q : P} (hc : ∀ y : P, ⁅q, y⁆ ∈ Subgroup.center P) :
    q ∈ Subgroup.center P := by
  rw [Subgroup.mem_center_iff]
  intro g
  have hθeq : ⁅q, g⁆ = 1 := by
    let θ : P →* Subgroup.center P :=
      { toFun := fun y => ⟨⁅q, y⁆, hc y⟩
        map_one' := by ext; simp
        map_mul' := by
          intro y z
          ext
          simp only [Subgroup.coe_mul]
          calc ⁅q, y * z⁆ = ⁅q, y⁆ * y * ⁅q, z⁆ * y⁻¹ :=
                commutatorElement_mul_right_eq_mul_conj q y z
            _ = ⁅q, y⁆ * (y * ⁅q, z⁆) * y⁻¹ := by group
            _ = ⁅q, y⁆ * (⁅q, z⁆ * y) * y⁻¹ := by
                  rw [show y * ⁅q, z⁆ = ⁅q, z⁆ * y from
                    Subgroup.mem_center_iff.mp (hc z) y]
            _ = ⁅q, y⁆ * ⁅q, z⁆ := by group }
    have : IsMulCommutative θ.range :=
      isMulCommutative_iff.mpr fun (a b : θ.range) => Subtype.ext (Subtype.ext
        (Subgroup.mem_center_iff.mp (b.1.2) (a.1)))
    have hperf : Group.IsPerfect θ.range := by
      have : Group.IsPerfect P := hP
      exact Group.IsPerfect.range θ
    have : Subsingleton θ.range :=
      Group.IsPerfect.subsingleton_of_isMulCommutative
    have h1 : (⟨θ g, MonoidHom.mem_range.mpr ⟨g, rfl⟩⟩ : θ.range) = 1 :=
      Subsingleton.elim _ _
    exact congrArg Subtype.val (congrArg Subtype.val h1)
  exact (commutatorElement_eq_one_iff_mul_comm.mp hθeq).symm

private theorem k328domo_center_map_eq {P X : Type*} [Group P] [Group X] (π : P →* X)
    (hπ : Function.Surjective π) (hker : π.ker ≤ Subgroup.center P) (hP : Group.IsPerfect P) :
    (Subgroup.center P).map π = Subgroup.center X := by
  apply le_antisymm
  · exact Subgroup.map_center_le_center (f := π) hπ
  · intro x hx
    obtain ⟨p, rfl⟩ := hπ x
    have hp : p ∈ Subgroup.center P :=
      k328domo_mem_center_of_commutator_mem_center hP fun y =>
        hker (by
          rw [MonoidHom.mem_ker, map_commutatorElement]
          exact commutatorElement_eq_one_iff_mul_comm.mpr
            (Subgroup.mem_center_iff.mp hx (π y)).symm)
    exact Subgroup.mem_map_of_mem π hp

private theorem k328domo_comap_center_le_center {P X : Type*} [Group P] [Group X] (π : P →* X)
    (hker : π.ker ≤ Subgroup.center P) (hP : Group.IsPerfect P) :
    (Subgroup.center X).comap π ≤ Subgroup.center P := by
  intro q hq
  rw [Subgroup.mem_comap] at hq
  exact k328domo_mem_center_of_commutator_mem_center hP fun y =>
    hker (by
      rw [MonoidHom.mem_ker, map_commutatorElement]
      exact commutatorElement_eq_one_iff_mul_comm.mpr
        (Subgroup.mem_center_iff.mp hq (π y)).symm)

private theorem k328domo_center_order_three {P X : Type*} [Group P] [Group X] [Finite P] [Finite X]
    (π : P →* X) (hπ : Function.Surjective π) (hker : π.ker ≤ Subgroup.center P)
    (hP : Group.IsPerfect P) (hX : Nat.card (Subgroup.center X) = 3) :
    ∃ z : P, z ∈ Subgroup.center P ∧ orderOf z = 3 := by
  have hmap := k328domo_center_map_eq π hπ hker hP
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨x, hx3⟩ := exists_prime_orderOf_dvd_card' (G := ↥(Subgroup.center X)) 3 (by rw [hX])
  have hxmem : (x : X) ∈ (Subgroup.center P).map π := by
    rw [hmap]
    exact x.2
  obtain ⟨z, hzP, hzπ⟩ := Subgroup.mem_map.mp hxmem
  have h3dvd : 3 ∣ Nat.card (Subgroup.center P) := by
    have h1 : orderOf (x : X) ∣ orderOf z := by
      rw [← hzπ]
      exact orderOf_map_dvd π z
    have hx3' : orderOf (x : X) = 3 := by
      rw [Subgroup.orderOf_coe]
      exact hx3
    rw [hx3'] at h1
    exact h1.trans (Subgroup.orderOf_dvd_natCard (Subgroup.center P) hzP)
  obtain ⟨w, hw⟩ := exists_prime_orderOf_dvd_card' (G := ↥(Subgroup.center P)) 3 h3dvd
  exact ⟨(w : P), w.2, by rw [Subgroup.orderOf_coe]; exact hw⟩

private abbrev k328domo_ι : Type := Fin (4 - 1) ⊕ Fin (4 - 1) ⊕ Fin 2

private abbrev k328domo_ee : k328domo_ι ≃ Fin 8 :=
  (Equiv.sumCongr (Equiv.refl (Fin (4 - 1)))
      (finSumFinEquiv : Fin (4 - 1) ⊕ Fin 2 ≃ Fin ((4 - 1) + 2))).trans
    (finSumFinEquiv : Fin (4 - 1) ⊕ Fin ((4 - 1) + 2) ≃ Fin ((4 - 1) + ((4 - 1) + 2)))

private theorem k328domo_det_eq_one {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K]
    (Q : (ι → K) → K) {g : GL ι K} (hg : g ∈ CFSG.Open.StatedOmega Q) :
    (g : Matrix ι ι K).det = 1 := by
  have hle : ⁅CFSG.MatrixModel.isometryCore Q, CFSG.MatrixModel.isometryCore Q⁆ ≤
      (Matrix.GeneralLinearGroup.det : GL ι K →* Kˣ).ker := by
    rw [Subgroup.commutator_le]
    intro a _ b _
    rw [MonoidHom.mem_ker, map_commutatorElement]
    exact commutatorElement_eq_one_iff_mul_comm.mpr (mul_comm _ _)
  have hg' : g ∈ ⁅CFSG.MatrixModel.isometryCore Q, CFSG.MatrixModel.isometryCore Q⁆ := hg
  have h1 : Matrix.GeneralLinearGroup.det g = 1 := MonoidHom.mem_ker.mp (hle hg')
  have h2 : (Matrix.GeneralLinearGroup.det g : K) = 1 := by rw [h1]; rfl
  rwa [Matrix.GeneralLinearGroup.val_det_apply] at h2

private noncomputable abbrev k328domo_matHom {K E : Type} [Field K] [Field E] (φ : K →+* E) :
    Matrix k328domo_ι k328domo_ι K →+* Matrix (Fin 8) (Fin 8) E :=
  (Matrix.reindexRingEquiv E k328domo_ee).toRingHom.comp (φ.mapMatrix)

private theorem k328domo_matHom_det {K E : Type} [Field K] [Field E] (φ : K →+* E)
    (M : Matrix k328domo_ι k328domo_ι K) (hM : M.det = 1) :
    ((k328domo_matHom φ) M).det = 1 := by
  show (Matrix.reindex k328domo_ee k328domo_ee (φ.mapMatrix M)).det = 1
  rw [Matrix.det_reindex_self, ← RingHom.map_det, hM, RingHom.map_one]

private noncomputable def k328domo_slHom {K E : Type} [Field K] [Field E] (φ : K →+* E)
    (b c : K) :
    CFSG.Open.StatedOmega (CFSG.Open.StatedQuadMinus 4 K b c) →*
      Matrix.SpecialLinearGroup (Fin 8) E where
  toFun g := ⟨k328domo_matHom φ (g.1 : Matrix k328domo_ι k328domo_ι K),
    k328domo_matHom_det φ (g.1 : Matrix k328domo_ι k328domo_ι K)
      (k328domo_det_eq_one (CFSG.Open.StatedQuadMinus 4 K b c) g.2)⟩
  map_one' := by
    apply Subtype.ext
    exact map_one (k328domo_matHom φ)
  map_mul' := by
    intro g h
    apply Subtype.ext
    exact map_mul (k328domo_matHom φ) _ _

private theorem k328domo_matHom_injective {K E : Type} [Field K] [Field E] {φ : K →+* E}
    (hφ : Function.Injective φ) : Function.Injective (k328domo_matHom φ) := by
  intro A B h
  apply Matrix.ext
  intro i j
  have h2 := congrFun (congrFun h (k328domo_ee i)) (k328domo_ee j)
  have h3 : φ (A i j) = φ (B i j) := by
    simpa [k328domo_matHom, RingHom.mapMatrix_apply, Matrix.reindex_apply] using h2
  exact hφ h3

private theorem k328domo_slHom_injective {K E : Type} [Field K] [Field E] {φ : K →+* E}
    (hφ : Function.Injective φ) (b c : K) :
    Function.Injective (k328domo_slHom φ b c) := by
  intro g h hgh
  apply Subtype.ext
  apply Units.ext
  apply k328domo_matHom_injective hφ
  exact congrArg (fun x : Matrix.SpecialLinearGroup (Fin 8) E =>
    (x : Matrix (Fin 8) (Fin 8) E)) hgh

private noncomputable abbrev k328domo_B (K : Type) [Field K] (b c : K) :
    LinearMap.BilinForm K (k328domo_ι → K) :=
  (CFSG.LieType.Universal.Spin.quadMinus 4 K b c).polarBilin

private theorem k328domo_B_preserve {K : Type} [Field K] (b c : K) {g : GL k328domo_ι K}
    (hg : g ∈ CFSG.Open.StatedOmega (CFSG.Open.StatedQuadMinus 4 K b c))
    (v w : k328domo_ι → K) :
    k328domo_B K b c (g *ᵥ v) (g *ᵥ w) = k328domo_B K b c v w := by
  have hmem : g ∈ CFSG.MatrixModel.isometryCore (CFSG.Open.StatedQuadMinus 4 K b c) :=
    CFSG.GroupTheory.WeirSylow.statedOmega_le_isometryCore _ hg
  have hQ : ∀ u : k328domo_ι → K,
      (CFSG.LieType.Universal.Spin.quadMinus 4 K b c) (Matrix.mulVec g u) =
        (CFSG.LieType.Universal.Spin.quadMinus 4 K b c) u := by
    intro u
    have := CFSG.GroupTheory.WeirSylow.apply_mulVec_of_mem_isometryCore hmem u
    simpa only [CFSG.LieType.Universal.Spin.coe_quadMinus] using this
  let f : (k328domo_ι → K) →ₗ[K] (k328domo_ι → K) := Matrix.toLin' (g : Matrix k328domo_ι k328domo_ι K)
  have hf : (CFSG.LieType.Universal.Spin.quadMinus 4 K b c).comp f =
      CFSG.LieType.Universal.Spin.quadMinus 4 K b c := by
    ext u
    simpa [f, Matrix.toLin'_apply] using hQ u
  have hv : f v = g *ᵥ v := by simp [f, Matrix.toLin'_apply]
  have hw : f w = g *ᵥ w := by simp [f, Matrix.toLin'_apply]
  rw [← hv, ← hw]
  calc (CFSG.LieType.Universal.Spin.quadMinus 4 K b c).polarBilin (f v) (f w)
      = ((CFSG.LieType.Universal.Spin.quadMinus 4 K b c).polarBilin.compl₁₂ f f) v w := by
        rw [LinearMap.compl₁₂_apply]
    _ = ((CFSG.LieType.Universal.Spin.quadMinus 4 K b c).comp f).polarBilin v w := by
        rw [QuadraticMap.polarBilin_comp]
    _ = (CFSG.LieType.Universal.Spin.quadMinus 4 K b c).polarBilin v w := by rw [hf]

private noncomputable abbrev k328domo_BE (K E : Type) [Field K] [Field E] (φ : K →+* E)
    (b c : K) : LinearMap.BilinForm E (k328domo_ι → E) :=
  Matrix.toBilin' (φ.mapMatrix (k328domo_B K b c).toMatrix')

private theorem k328domo_B_toMatrix_preserve {K : Type} [Field K] (b c : K) {g : GL k328domo_ι K}
    (hg : g ∈ CFSG.Open.StatedOmega (CFSG.Open.StatedQuadMinus 4 K b c)) :
    (g : Matrix k328domo_ι k328domo_ι K)ᵀ * (k328domo_B K b c).toMatrix' *
      (g : Matrix k328domo_ι k328domo_ι K) = (k328domo_B K b c).toMatrix' := by
  have hcomp : (k328domo_B K b c).comp (Matrix.toLin' (g : Matrix k328domo_ι k328domo_ι K))
      (Matrix.toLin' (g : Matrix k328domo_ι k328domo_ι K)) = k328domo_B K b c := by
    apply LinearMap.ext
    intro v
    apply LinearMap.ext
    intro w
    simpa [LinearMap.BilinForm.comp_apply, Matrix.toLin'_apply] using
      k328domo_B_preserve b c hg v w
  rw [LinearMap.BilinForm.mul_toMatrix'_mul,
    show ((g : Matrix k328domo_ι k328domo_ι K)ᵀ)ᵀ = (g : Matrix k328domo_ι k328domo_ι K) from
      Matrix.transpose_transpose _, hcomp]

private theorem k328domo_BE_preserve {K E : Type} [Field K] [Field E] (φ : K →+* E) (b c : K)
    {g : GL k328domo_ι K}
    (hg : g ∈ CFSG.Open.StatedOmega (CFSG.Open.StatedQuadMinus 4 K b c))
    (v w : k328domo_ι → E) :
    k328domo_BE K E φ b c (Matrix.mulVec (φ.mapMatrix (g : Matrix k328domo_ι k328domo_ι K)) v)
        (Matrix.mulVec (φ.mapMatrix (g : Matrix k328domo_ι k328domo_ι K)) w) =
      k328domo_BE K E φ b c v w := by
  have hmat := k328domo_B_toMatrix_preserve b c hg
  have hmatE : (φ.mapMatrix (g : Matrix k328domo_ι k328domo_ι K))ᵀ *
        φ.mapMatrix (k328domo_B K b c).toMatrix' *
        φ.mapMatrix (g : Matrix k328domo_ι k328domo_ι K) =
      φ.mapMatrix (k328domo_B K b c).toMatrix' := by
    rw [show (φ.mapMatrix (g : Matrix k328domo_ι k328domo_ι K))ᵀ =
        φ.mapMatrix ((g : Matrix k328domo_ι k328domo_ι K)ᵀ) from by
      rw [RingHom.mapMatrix_apply, RingHom.mapMatrix_apply, Matrix.transpose_map]]
    rw [← map_mul, ← map_mul, hmat]
  have hcompE : (Matrix.toBilin' (φ.mapMatrix (k328domo_B K b c).toMatrix')).comp
      (Matrix.toLin' (φ.mapMatrix (g : Matrix k328domo_ι k328domo_ι K)))
      (Matrix.toLin' (φ.mapMatrix (g : Matrix k328domo_ι k328domo_ι K))) =
      Matrix.toBilin' (φ.mapMatrix (k328domo_B K b c).toMatrix') := by
    rw [Matrix.toBilin'_comp, hmatE]
  have := congrArg (fun B : LinearMap.BilinForm E (k328domo_ι → E) => B v w) hcompE
  simpa [k328domo_BE, LinearMap.BilinForm.comp_apply, Matrix.toLin'_apply] using this

private theorem k328domo_BE_nondegenerate {K E : Type} [Field K] [Field E] (φ : K →+* E)
    (hφ : Function.Injective φ) (b c : K) (hbc : b ^ 2 - 4 * c ≠ 0) :
    (k328domo_BE K E φ b c).Nondegenerate := by
  have hB : (k328domo_B K b c).Nondegenerate :=
    CFSG.LieType.Universal.Spin.nondegenerate_polarBilin_quadMinus 4 K hbc
  have hJ : (k328domo_B K b c).toMatrix'.det ≠ 0 := by
    have h := hB
    rw [← Matrix.toBilin'_toMatrix' (B := k328domo_B K b c)] at h
    exact (LinearMap.BilinForm.nondegenerate_toBilin'_iff_det_ne_zero
      (M := (k328domo_B K b c).toMatrix')).mp h
  have hdet : (φ.mapMatrix (k328domo_B K b c).toMatrix').det ≠ 0 := by
    rw [← RingHom.map_det]
    intro h
    exact hJ (hφ (by simpa using h))
  exact LinearMap.BilinForm.nondegenerate_toBilin'_of_det_ne_zero' _ hdet

private theorem k328domo_omega_sq_ne_one {E : Type} [Field E] {ω : E}
    (hω : ω ^ 2 + ω + 1 = 0) (hω1 : ω ≠ 1) : ω ^ 2 ≠ 1 := by
  intro h
  have hfac : (ω - 1) * (ω + 1) = 0 := by linear_combination h
  rcases mul_eq_zero.mp hfac with h1 | h1
  · exact hω1 (sub_eq_zero.mp h1)
  · have hωeq : ω = -1 := by linear_combination h1
    rw [hωeq] at hω
    norm_num at hω

private theorem k328domo_BE_eigen_zero {K E : Type} [Field K] [Field E] (φ : K →+* E) (b c : K)
    {g : GL k328domo_ι K}
    (hg : g ∈ CFSG.Open.StatedOmega (CFSG.Open.StatedQuadMinus 4 K b c))
    {ω : E} (hω : ω ^ 2 + ω + 1 = 0) (hω1 : ω ≠ 1)
    {v w : k328domo_ι → E}
    (hv : v ∈ Module.End.eigenspace
      (Matrix.toLin' (φ.mapMatrix (g : Matrix k328domo_ι k328domo_ι K))) ω)
    (hw : w ∈ Module.End.eigenspace
      (Matrix.toLin' (φ.mapMatrix (g : Matrix k328domo_ι k328domo_ι K))) ω) :
    k328domo_BE K E φ b c v w = 0 := by
  have hμ2 : ω ^ 2 ≠ 1 := k328domo_omega_sq_ne_one hω hω1
  have hv' : Matrix.mulVec (φ.mapMatrix (g : Matrix k328domo_ι k328domo_ι K)) v = ω • v := by
    simpa [Matrix.toLin'_apply] using (Module.End.mem_eigenspace_iff.mp hv)
  have hw' : Matrix.mulVec (φ.mapMatrix (g : Matrix k328domo_ι k328domo_ι K)) w = ω • w := by
    simpa [Matrix.toLin'_apply] using (Module.End.mem_eigenspace_iff.mp hw)
  have hpres := k328domo_BE_preserve φ b c hg v w
  have h2 : k328domo_BE K E φ b c
        (Matrix.mulVec (φ.mapMatrix (g : Matrix k328domo_ι k328domo_ι K)) v)
        (Matrix.mulVec (φ.mapMatrix (g : Matrix k328domo_ι k328domo_ι K)) w) =
      ω ^ 2 * k328domo_BE K E φ b c v w := by
    rw [hv', hw']
    simp only [map_smul, LinearMap.smul_apply, smul_eq_mul, pow_two]
    ring
  have heq : k328domo_BE K E φ b c v w = ω ^ 2 * k328domo_BE K E φ b c v w :=
    hpres.symm.trans h2
  have hzero : (ω ^ 2 - 1) * k328domo_BE K E φ b c v w = 0 := by
    rw [sub_mul, one_mul]
    exact sub_eq_zero.mpr heq.symm
  exact (mul_eq_zero.mp hzero).resolve_left (sub_ne_zero.mpr hμ2)

private theorem k328domo_eigenspace_le_orthogonal {K E : Type} [Field K] [Field E]
    (φ : K →+* E) (b c : K) {g : GL k328domo_ι K}
    (hg : g ∈ CFSG.Open.StatedOmega (CFSG.Open.StatedQuadMinus 4 K b c))
    {ω : E} (hω : ω ^ 2 + ω + 1 = 0) (hω1 : ω ≠ 1) :
    Module.End.eigenspace
        (Matrix.toLin' (φ.mapMatrix (g : Matrix k328domo_ι k328domo_ι K))) ω ≤
      (k328domo_BE K E φ b c).orthogonal
        (Module.End.eigenspace
          (Matrix.toLin' (φ.mapMatrix (g : Matrix k328domo_ι k328domo_ι K))) ω) := by
  intro v hv
  change v ∈ Submodule.orthogonalBilin (k328domo_BE K E φ b c)
    (Module.End.eigenspace
      (Matrix.toLin' (φ.mapMatrix (g : Matrix k328domo_ι k328domo_ι K))) ω)
  rw [Submodule.mem_orthogonalBilin]
  intro w hw
  exact k328domo_BE_eigen_zero φ b c hg hω hω1 hw hv

private theorem k328domo_eigenspace_finrank_le_four {K E : Type} [Field K] [Field E]
    (φ : K →+* E) (hφ : Function.Injective φ) (b c : K) (hbc : b ^ 2 - 4 * c ≠ 0)
    {g : GL k328domo_ι K}
    (hg : g ∈ CFSG.Open.StatedOmega (CFSG.Open.StatedQuadMinus 4 K b c))
    {ω : E} (hω : ω ^ 2 + ω + 1 = 0) (hω1 : ω ≠ 1) :
    Module.finrank E (Module.End.eigenspace
        (Matrix.toLin' (φ.mapMatrix (g : Matrix k328domo_ι k328domo_ι K))) ω) ≤ 4 := by
  have hnd := k328domo_BE_nondegenerate φ hφ b c hbc
  have hle : Module.End.eigenspace
        (Matrix.toLin' (φ.mapMatrix (g : Matrix k328domo_ι k328domo_ι K))) ω ≤
      (k328domo_BE K E φ b c).orthogonal (Module.End.eigenspace
        (Matrix.toLin' (φ.mapMatrix (g : Matrix k328domo_ι k328domo_ι K))) ω) :=
    k328domo_eigenspace_le_orthogonal φ b c hg hω hω1
  have hfin := LinearMap.BilinForm.finrank_orthogonal hnd
    (Module.End.eigenspace
      (Matrix.toLin' (φ.mapMatrix (g : Matrix k328domo_ι k328domo_ι K))) ω)
  have hmono := Submodule.finrank_mono hle
  have hdim : Module.finrank E (k328domo_ι → E) = 8 := by
    rw [Module.finrank_fintype_fun_eq_card]
    decide
  rw [hfin, hdim] at hmono
  omega

private theorem k328domo_eigenspace_reindex_finrank {E : Type} [Field E]
    (M : Matrix k328domo_ι k328domo_ι E) (ω : E) :
    Module.finrank E (Module.End.eigenspace
        (Matrix.toLin' (Matrix.reindex k328domo_ee k328domo_ee M)) ω) =
      Module.finrank E (Module.End.eigenspace (Matrix.toLin' M) ω) := by
  let F : (k328domo_ι → E) ≃ₗ[E] (Fin 8 → E) := LinearEquiv.funCongrLeft E E k328domo_ee.symm
  have hlin : (Matrix.toLin' (Matrix.reindex k328domo_ee k328domo_ee M)) =
      F ∘ₗ (Matrix.toLin' M) ∘ₗ F.symm := by
    rw [Matrix.toLin'_reindex]
    rfl
  have hmap : Submodule.map (F : (k328domo_ι → E) →ₗ[E] (Fin 8 → E))
      (Module.End.eigenspace (Matrix.toLin' M) ω) =
      Module.End.eigenspace
        (Matrix.toLin' (Matrix.reindex k328domo_ee k328domo_ee M)) ω := by
    ext y
    simp only [Submodule.mem_map]
    constructor
    · rintro ⟨x, hx, rfl⟩
      rw [Module.End.mem_eigenspace_iff] at hx ⊢
      rw [hlin]
      simp only [LinearMap.comp_apply]
      change F (Matrix.toLin' M (F.symm (F x))) = ω • F x
      rw [F.symm_apply_apply, hx, map_smul]
    · intro hy
      refine ⟨F.symm y, ?_, F.apply_symm_apply y⟩
      rw [Module.End.mem_eigenspace_iff] at hy ⊢
      rw [hlin] at hy
      simp only [LinearMap.comp_apply] at hy
      change Matrix.toLin' M (F.symm y) = ω • F.symm y
      apply F.injective
      rw [map_smul, F.apply_symm_apply]
      exact hy
  rw [← hmap, LinearEquiv.finrank_map_eq]

private theorem k328domo_eigenspace_reindex_le_four {K E : Type} [Field K] [Field E]
    (φ : K →+* E) (hφ : Function.Injective φ) (b c : K) (hbc : b ^ 2 - 4 * c ≠ 0)
    {g : GL k328domo_ι K}
    (hg : g ∈ CFSG.Open.StatedOmega (CFSG.Open.StatedQuadMinus 4 K b c))
    {ω : E} (hω : ω ^ 2 + ω + 1 = 0) (hω1 : ω ≠ 1) :
    Module.finrank E (Module.End.eigenspace
        (Matrix.toLin' (Matrix.reindex k328domo_ee k328domo_ee
          (φ.mapMatrix (g : Matrix k328domo_ι k328domo_ι K)))) ω) ≤ 4 := by
  rw [k328domo_eigenspace_reindex_finrank]
  exact k328domo_eigenspace_finrank_le_four φ hφ b c hbc hg hω hω1

private abbrev k328domo_H (K : Type) [Field K] (b c : K) : Subgroup (GL k328domo_ι K) :=
  CFSG.Open.StatedOmega (CFSG.Open.StatedQuadMinus 4 K b c)

private theorem k328domo_ker_le_center {K : Type} [Field K] (b c : K) :
    (QuotientGroup.mk' ((CFSG.Open.StatedScalars k328domo_ι K).subgroupOf (k328domo_H K b c))).ker ≤
      Subgroup.center (k328domo_H K b c) := by
  intro x hx
  rw [QuotientGroup.ker_mk'] at hx
  rw [Subgroup.mem_center_iff]
  intro y
  apply Subtype.ext
  have hxZ : (x.1 : GL k328domo_ι K) ∈ Subgroup.center (GL k328domo_ι K) := by
    rw [← CFSG.Open.StatedAPI.statedScalars_eq_center]
    exact hx
  exact Subgroup.mem_center_iff.mp hxZ y.1

private theorem k328domo_discr_ne_zero {K : Type} [Field K] (h2 : (2 : K) ≠ 0)
    {b c : K} (hbc : ∀ s : K, s ^ 2 + b * s + c ≠ 0) : b ^ 2 - 4 * c ≠ 0 := by
  intro h
  have h4 : (4 : K) ≠ 0 := by
    have h42 : (4 : K) = 2 * 2 := by norm_num
    rw [h42]
    exact mul_ne_zero h2 h2
  have key : (4 : K) * ((-b / 2) ^ 2 + b * (-b / 2) + c) = -(b ^ 2 - 4 * c) := by
    field_simp
    ring
  rw [h, neg_zero] at key
  exact hbc (-b / 2) ((mul_eq_zero.mp key).resolve_left h4)

private theorem k328domo_eigenspace_or {E V : Type} [Field E] [AddCommGroup V] [Module E V]
    [FiniteDimensional E V] {f : Module.End E V} (hf3 : f ^ 3 = 1) (hne : f ≠ 1)
    {ω : E} (hω : ω ^ 2 + ω + 1 = 0) (_hω1 : ω ≠ 1) :
    f.eigenspace ω ≠ ⊥ ∨ f.eigenspace (ω ^ 2) ≠ ⊥ := by
  by_contra h
  push Not at h
  obtain ⟨h1, h2⟩ := h
  have hker1 : (f - ω • (1 : V →ₗ[E] V)).ker = f.eigenspace ω := by
    ext x
    simp only [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply,
      Module.End.mem_eigenspace_iff, sub_eq_zero]
  have hker2 : (f - ω ^ 2 • (1 : V →ₗ[E] V)).ker = f.eigenspace (ω ^ 2) := by
    ext x
    simp only [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply,
      Module.End.mem_eigenspace_iff, sub_eq_zero]
  have hinj1 : Function.Injective (f - ω • (1 : V →ₗ[E] V)) := by
    rw [← LinearMap.ker_eq_bot, hker1, h1]
  have hinj2 : Function.Injective (f - ω ^ 2 • (1 : V →ₗ[E] V)) := by
    rw [← LinearMap.ker_eq_bot, hker2, h2]
  have hsurj1 : Function.Surjective (f - ω • (1 : V →ₗ[E] V)) :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank rfl).mp hinj1
  have hsurj2 : Function.Surjective (f - ω ^ 2 • (1 : V →ₗ[E] V)) :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank rfl).mp hinj2
  have hsurjprod : Function.Surjective
      ((f - ω • (1 : V →ₗ[E] V)) * (f - ω ^ 2 • (1 : V →ₗ[E] V))) := by
    intro x
    obtain ⟨y, hy⟩ := hsurj1 x
    obtain ⟨z, hz⟩ := hsurj2 y
    exact ⟨z, by rw [Module.End.mul_apply, hz, hy]⟩
  have hsum : ω + ω ^ 2 = -1 := by linear_combination hω
  have hmul : ω * ω ^ 2 = 1 := by
    have h3 : ω ^ 3 = 1 := by linear_combination (ω - 1) * hω
    linear_combination h3
  have hprod : (f - ω • (1 : Module.End E V)) * (f - ω ^ 2 • (1 : Module.End E V)) =
      f ^ 2 + f + 1 := by
    ext x
    simp only [Module.End.mul_apply, LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply,
      LinearMap.add_apply, Module.End.pow_apply]
    rw [map_sub, map_smul, smul_sub, smul_smul, hmul, one_smul]
    rw [show (⇑f)^[2] x = f (f x) from rfl]
    have hω2 : ω ^ 2 = -1 - ω := by linear_combination hsum
    rw [hω2, sub_smul, neg_smul, one_smul]
    module
  have hcube : (f - 1) * (f ^ 2 + f + 1) = f ^ 3 - 1 := by
    ext x
    simp only [Module.End.mul_apply, LinearMap.sub_apply, Module.End.one_apply, LinearMap.add_apply,
      Module.End.pow_apply]
    rw [show (⇑f)^[2] x = f (f x) from rfl,
      show (⇑f)^[3] x = f (f (f x)) from rfl]
    rw [map_add, map_add]
    abel
  have hcomp : (f - 1) * ((f - ω • (1 : Module.End E V)) * (f - ω ^ 2 • (1 : Module.End E V))) = 0 := by
    rw [hprod, hcube, hf3, sub_self]
  have hf1 : f - 1 = 0 := by
    ext x
    obtain ⟨y, hy⟩ := hsurjprod x
    have := congrArg (fun (g : V →ₗ[E] V) => g y) hcomp
    rw [LinearMap.zero_apply, Module.End.mul_apply, hy] at this
    exact this
  exact hne (sub_eq_zero.mp hf1)

private theorem k328domo_H_contra {K : Type} [Field K] [Finite K] {p f : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) (hp3 : p ≠ 3) (hcard : Nat.card K = p ^ f)
    (b c : K) (hbc : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    {Zb Xb : Subgroup (CFSG.Open.StatedProj (k328domo_H K b c))}
    (hZb : Pos (CFSG.Open.StatedProj (k328domo_H K b c)) Zb Xb) (_hXbne : Xb ≠ ⊤)
    (hEig : ∀ (E : Type) [Field E] [Finite E], ringChar E ≠ 2 → ∀ (n : ℕ)
      (Y : Subgroup (Matrix.SpecialLinearGroup (Fin n) E)), ⁅Y, Y⁆ = Y →
      ∀ z ∈ Y, (∀ y ∈ Y, Commute z y) → orderOf z = 3 → ∀ μ : E, μ ≠ 1 →
        Module.End.eigenspace (Matrix.toLin' (z : Matrix (Fin n) (Fin n) E)) μ ≠ ⊥ →
        Module.finrank E
            (Module.End.eigenspace (Matrix.toLin' (z : Matrix (Fin n) (Fin n) E)) μ) ≤ 4 →
        ∀ (W : Type) [Group W] (φ : ↥Y →* W), Function.Surjective φ →
          φ.ker ≤ Subgroup.center ↥Y → ¬ (LieModel W .PSL 3 2 2 ∨ LieModel W .PSU 3 2 3)) :
    False := by
  classical
  let H := k328domo_H K b c
  let π : H →* CFSG.Open.StatedProj H :=
    QuotientGroup.mk' ((CFSG.Open.StatedScalars k328domo_ι K).subgroupOf H)
  let L : Subgroup (CFSG.Open.StatedProj H) := Xb
  let M : Subgroup H := ⁅L.comap π, L.comap π⁆
  have hπsurj : Function.Surjective π := QuotientGroup.mk'_surjective _
  have hcen : π.ker ≤ Subgroup.center H := k328domo_ker_le_center b c
  have hperfL : Group.IsPerfect ↥L := Group.isPerfect_def.mpr hZb.2.2.2.2.1.1
  have hLperf : ⁅L, L⁆ = L := Subgroup.isPerfect_iff.mp hperfL
  have hMperf : Group.IsPerfect ↥M :=
    CFSG.GroupTheory.PerfectCover.isPerfect_commutator_comap π hπsurj hcen hLperf
  have hmapM : M.map π = L :=
    CFSG.GroupTheory.PerfectCover.map_commutator_comap π hπsurj hLperf
  let φX : ↥M →* ↥L :=
    { toFun := fun m => ⟨π m.1, by rw [← hmapM]; exact Subgroup.mem_map_of_mem π m.2⟩
      map_one' := by apply Subtype.ext; exact map_one π
      map_mul' := by intro a b; apply Subtype.ext; exact map_mul π a.1 b.1 }
  have hφXsurj : Function.Surjective φX := by
    intro l
    obtain ⟨m, hmM, hm⟩ := Subgroup.mem_map.mp (by rw [hmapM]; exact l.2)
    exact ⟨⟨m, hmM⟩, Subtype.ext hm⟩
  have hφXker : φX.ker ≤ Subgroup.center ↥M := by
    intro k hk
    rw [Subgroup.mem_center_iff]
    intro m
    apply Subtype.ext
    have hkπ : π k.1 = 1 := congrArg Subtype.val (MonoidHom.mem_ker.mp hk)
    have hkZ : k.1 ∈ Subgroup.center H := hcen (MonoidHom.mem_ker.mpr hkπ)
    exact Subgroup.mem_center_iff.mp hkZ m.1
  obtain ⟨z, hzcent, hzord⟩ :=
    k328domo_center_order_three φX hφXsurj hφXker hMperf hZb.2.2.2.2.2.1
  let W : Type := ↥L ⧸ Subgroup.center ↥L
  let φW : ↥M →* W := (QuotientGroup.mk' (Subgroup.center ↥L)).comp φX
  have hφWsurj : Function.Surjective φW :=
    (QuotientGroup.mk'_surjective (Subgroup.center ↥L)).comp hφXsurj
  have hφWker : φW.ker ≤ Subgroup.center ↥M := by
    intro k hk
    have hk' : φX k ∈ Subgroup.center ↥L :=
      (QuotientGroup.eq_one_iff (N := Subgroup.center ↥L) (φX k)).mp (MonoidHom.mem_ker.mp hk)
    exact k328domo_comap_center_le_center φX hφXker hMperf hk'
  have hWlie : LieModel W .PSL 3 2 2 ∨ LieModel W .PSU 3 2 3 := hZb.2.2.2.2.2.2
  obtain ⟨E, hEfield, hEfin, ι, ω, hιinj, hEchar, hω1, hωsum⟩ :=
    k328domo_exists_omega K hp2 hp3 hcard
  let : Field E := hEfield
  let : Finite E := hEfin
  have : Fintype K := Fintype.ofFinite K
  have : CharP K p := charP_of_card_eq_prime_pow (p := p) (f := f)
    (by rw [← Nat.card_eq_fintype_card]; exact hcard)
  have h2K : (2 : K) ≠ 0 := by
    intro h
    have hdvd : p ∣ 2 := (CharP.cast_eq_zero_iff K p 2).mp h
    exact hp2 ((Nat.prime_dvd_prime_iff_eq Fact.out Nat.prime_two).mp hdvd)
  have hbc' : b ^ 2 - 4 * c ≠ 0 := k328domo_discr_ne_zero h2K hbc
  let gH : H := z.1
  let Y : Subgroup (Matrix.SpecialLinearGroup (Fin 8) E) := M.map (k328domo_slHom ι b c)
  let zY : Matrix.SpecialLinearGroup (Fin 8) E := k328domo_slHom ι b c gH
  have hYperf : ⁅Y, Y⁆ = Y := by
    show ⁅M.map (k328domo_slHom ι b c), M.map (k328domo_slHom ι b c)⁆ =
      M.map (k328domo_slHom ι b c)
    rw [← Subgroup.map_commutator M M (k328domo_slHom ι b c), Subgroup.isPerfect_iff.mp hMperf]
  have hzYmem : zY ∈ Y := Subgroup.mem_map_of_mem _ z.2
  have hzYcent : ∀ y ∈ Y, Commute zY y := by
    intro y hy
    obtain ⟨m, hmM, rfl⟩ := Subgroup.mem_map.mp hy
    rw [commute_iff_eq, ← map_mul, ← map_mul]
    congr 1
    exact congrArg Subtype.val (Subgroup.mem_center_iff.mp hzcent ⟨m, hmM⟩).symm
  have hzYord : orderOf zY = 3 := by
    change orderOf (k328domo_slHom ι b c gH) = 3
    rw [orderOf_injective (k328domo_slHom ι b c)
      (k328domo_slHom_injective hιinj b c) gH, Subgroup.orderOf_coe z, hzord]
  have hY3 : zY ^ 3 = 1 := by rw [← hzYord]; exact pow_orderOf_eq_one zY
  have hY3m : (zY : Matrix (Fin 8) (Fin 8) E) ^ 3 = 1 := congrArg Subtype.val hY3
  have hf3 : (Matrix.toLin' (zY : Matrix (Fin 8) (Fin 8) E)) ^ 3 = 1 := by
    rw [← Matrix.toLin'_pow, hY3m, Matrix.toLin'_one]; rfl
  have hne : Matrix.toLin' (zY : Matrix (Fin 8) (Fin 8) E) ≠ 1 := by
    intro h
    have h' : Matrix.toLin' (zY : Matrix (Fin 8) (Fin 8) E) =
        Matrix.toLin' (1 : Matrix (Fin 8) (Fin 8) E) := by
      rw [Matrix.toLin'_one, h]; rfl
    have hM : (zY : Matrix (Fin 8) (Fin 8) E) = 1 :=
      (LinearEquiv.injective (Matrix.toLin' : Matrix (Fin 8) (Fin 8) E ≃ₗ[E]
        ((Fin 8 → E) →ₗ[E] (Fin 8 → E)))) h'
    have hz1 : zY = 1 := Subtype.eq hM
    rw [hz1, orderOf_one] at hzYord
    omega
  have heig_ex : Module.End.eigenspace (Matrix.toLin' (zY : Matrix (Fin 8) (Fin 8) E)) ω ≠ ⊥ ∨
      Module.End.eigenspace (Matrix.toLin' (zY : Matrix (Fin 8) (Fin 8) E)) (ω ^ 2) ≠ ⊥ :=
    k328domo_eigenspace_or hf3 hne hωsum hω1
  have hVdim : ∀ μ : E, μ ^ 2 + μ + 1 = 0 → μ ≠ 1 →
      Module.finrank E (Module.End.eigenspace
        (Matrix.toLin' (zY : Matrix (Fin 8) (Fin 8) E)) μ) ≤ 4 := by
    intro μ hμ hμ1
    have h := k328domo_eigenspace_reindex_le_four ι hιinj b c hbc'
      (g := (gH : GL k328domo_ι K)) gH.2 hμ hμ1
    change Module.finrank E (Module.End.eigenspace
      (Matrix.toLin' (Matrix.reindex k328domo_ee k328domo_ee
        (ι.mapMatrix ((gH : GL k328domo_ι K) : Matrix k328domo_ι k328domo_ι K)))) μ) ≤ 4
    exact h
  have hω2poly : (ω ^ 2) ^ 2 + ω ^ 2 + 1 = 0 := by
    have h3 : ω ^ 3 = 1 := by linear_combination (ω - 1) * hωsum
    linear_combination ω * h3 + hωsum
  have hω2ne : ω ^ 2 ≠ 1 := k328domo_omega_sq_ne_one hωsum hω1
  let eMY := Subgroup.equivMapOfInjective M (k328domo_slHom ι b c)
    (k328domo_slHom_injective hιinj b c)
  let φWY : ↥Y →* W := φW.comp (eMY.symm : ↥Y →* ↥M)
  have hφWYsurj : Function.Surjective φWY := by
    intro w
    obtain ⟨m, hm⟩ := hφWsurj w
    exact ⟨eMY m, by show φW (eMY.symm (eMY m)) = w; rw [MulEquiv.symm_apply_apply]; exact hm⟩
  have hφWYker : φWY.ker ≤ Subgroup.center ↥Y := by
    have hker : φWY.ker = (φW.ker).map eMY := by
      ext y
      rw [MonoidHom.mem_ker, Subgroup.mem_map]
      constructor
      · intro hy
        obtain ⟨m, rfl⟩ := eMY.surjective y
        exact ⟨m, by simpa [φWY] using hy, rfl⟩
      · rintro ⟨m, hm, rfl⟩
        simpa [φWY] using hm
    rw [hker]
    calc (φW.ker).map eMY ≤ (Subgroup.center ↥M).map eMY := Subgroup.map_mono hφWker
      _ = Subgroup.center ↥Y := Subgroup.map_center_eq eMY
  cases heig_ex with
  | inl hωne =>
    exact hEig E hEchar 8 Y hYperf zY hzYmem hzYcent hzYord ω hω1 hωne (hVdim ω hωsum hω1)
      W φWY hφWYsurj hφWYker hWlie
  | inr hV2ne =>
    exact hEig E hEchar 8 Y hYperf zY hzYmem hzYcent hzYord (ω ^ 2) hω2ne hV2ne
      (hVdim (ω ^ 2) hω2poly hω2ne) W φWY hφWYsurj hφWYker hWlie

private theorem k328domo_core
    (hEig : ∀ (E : Type) [Field E] [Finite E], ringChar E ≠ 2 → ∀ (n : ℕ)
      (Y : Subgroup (Matrix.SpecialLinearGroup (Fin n) E)), ⁅Y, Y⁆ = Y →
      ∀ z ∈ Y, (∀ y ∈ Y, Commute z y) → orderOf z = 3 → ∀ μ : E, μ ≠ 1 →
        Module.End.eigenspace (Matrix.toLin' (z : Matrix (Fin n) (Fin n) E)) μ ≠ ⊥ →
        Module.finrank E
            (Module.End.eigenspace (Matrix.toLin' (z : Matrix (Fin n) (Fin n) E)) μ) ≤ 4 →
        ∀ (W : Type) [Group W] (φ : ↥Y →* W), Function.Surjective φ →
          φ.ker ≤ Subgroup.center ↥Y → ¬ (LieModel W .PSL 3 2 2 ∨ LieModel W .PSU 3 2 3)) :
    ∀ (S : Type) [Group S] [Finite S], IsSimpleGroup S → ∀ p f : ℕ, p ≠ 2 → p ≠ 3 →
      LieModel S .POmegaMinus 4 p f → ¬ K328DetPosIn S := by
  intro S _ _ hS p f hp2 hp3 hmodel hpos
  have hclass : CFSG.Open.StatedClassicalModel S .POmegaMinus 4 p f :=
    CFSG.Blueprint.LieModel.statedClassicalModel hmodel (by decide)
  unfold CFSG.Open.StatedClassicalModel at hclass
  obtain ⟨hadm, K, hKfield, hKfin, hKcard, b, c, hbc, ⟨e⟩⟩ := hclass
  let : Field K := hKfield
  let : Finite K := hKfin
  have : Fact p.Prime := ⟨hadm.1⟩
  obtain ⟨Z, X, hZ, hXne⟩ := hpos
  have hXbne : X.map e.toMonoidHom ≠ ⊤ := by
    intro h
    have h' : X.map e.toMonoidHom = (⊤ : Subgroup S).map e.toMonoidHom := by
      rw [Subgroup.map_top_of_surjective _ e.surjective]; exact h
    exact hXne (Subgroup.map_injective e.injective h')
  exact k328domo_H_contra hp2 hp3 hKcard b c hbc (pos_map e hZ) hXbne hEig

private theorem k328dplo_det_eq_one {K : Type} [Field K] (n : ℕ)
    (P : Subgroup (StatedSL n K)) (p : ↥P) :
    (((p : StatedSL n K) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).det = 1 :=
  mem_statedSL_iff.mp ((p : StatedSL n K)).2

private noncomputable def k328dplo_matMatrix {K E : Type} [Field K] [Field E] (φ : K →+* E)
    (n : ℕ) (P : Subgroup (StatedSL n K)) (p : ↥P) : Matrix (Fin n) (Fin n) E :=
  φ.mapMatrix (((p : StatedSL n K) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)

private noncomputable def k328dplo_slHom {K E : Type} [Field K] [Field E] (φ : K →+* E)
    (n : ℕ) (P : Subgroup (StatedSL n K)) :
    ↥P →* Matrix.SpecialLinearGroup (Fin n) E where
  toFun p := ⟨k328dplo_matMatrix φ n P p, by
    change (φ.mapMatrix (((p : StatedSL n K) : GL (Fin n) K) :
      Matrix (Fin n) (Fin n) K)).det = 1
    rw [← RingHom.map_det, k328dplo_det_eq_one n P p, map_one]⟩
  map_one' := by
    apply Subtype.ext
    change k328dplo_matMatrix φ n P 1 = 1
    simp [k328dplo_matMatrix]
  map_mul' p q := by
    apply Subtype.ext
    change k328dplo_matMatrix φ n P (p * q) =
      k328dplo_matMatrix φ n P p * k328dplo_matMatrix φ n P q
    simp [k328dplo_matMatrix, map_mul]

private theorem k328dplo_slHom_apply {K E : Type} [Field K] [Field E] (φ : K →+* E)
    (n : ℕ) (P : Subgroup (StatedSL n K)) (z : ↥P) :
    ((k328dplo_slHom φ n P z : Matrix.SpecialLinearGroup (Fin n) E) :
      Matrix (Fin n) (Fin n) E) =
      φ.mapMatrix (((z : StatedSL n K) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := rfl

private theorem k328dplo_slHom_injective {K E : Type} [Field K] [Field E] (φ : K →+* E)
    (hφ : Function.Injective φ) (n : ℕ) (P : Subgroup (StatedSL n K)) :
    Function.Injective (k328dplo_slHom φ n P) := by
  intro p q hpq
  have hval : (((p : StatedSL n K) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      (((q : StatedSL n K) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
    have h := congrArg (fun x : Matrix.SpecialLinearGroup (Fin n) E =>
      (x : Matrix (Fin n) (Fin n) E)) hpq
    rw [k328dplo_slHom_apply, k328dplo_slHom_apply] at h
    ext i j
    exact hφ (by simpa using congr_fun (congr_fun h i) j)
  exact Subtype.ext (Subtype.ext (Units.ext hval))

private theorem k328dplo_eigenspace_finrank_le_n {E : Type} [Field E] {n : ℕ}
    (z : Matrix (Fin n) (Fin n) E) (μ : E) :
    Module.finrank E (Module.End.eigenspace (Matrix.toLin' z) μ) ≤ n := by
  calc Module.finrank E (Module.End.eigenspace (Matrix.toLin' z) μ)
      ≤ Module.finrank E (⊤ : Submodule E (Fin n → E)) := Submodule.finrank_mono le_top
    _ = Module.finrank E (Fin n → E) := finrank_top E (Fin n → E)
    _ = n := by rw [Module.finrank_fintype_fun_eq_card, Fintype.card_fin]

private theorem k328dplo_eigen_finrank_le_three {K E : Type} [Field K] [Field E] [Algebra K E]
    [Module.Finite K E] {n : ℕ} (hn : n ≤ 7)
    (hfin : Module.finrank K E = 2) (σ : E ≃ₐ[K] E) (p : ℕ) [Fact p.Prime] [CharP E p]
    (hp3 : p ≠ 3) {ω : E} (hσω : σ ω = ω ^ 2) (hω : ω ^ 2 + ω + 1 = 0)
    (z : Matrix (Fin n) (Fin n) K) :
    Module.finrank E
      (Module.End.eigenspace (Matrix.toLin' (z.map (algebraMap K E))) ω) ≤ 3 := by
  have h := k328dplo_eigen_bound hfin σ p hp3 hσω hω z
  omega

private theorem k328dplo_omega_ne_one {E : Type} [Field E] {p : ℕ} [Fact p.Prime] [CharP E p]
    (hp3 : p ≠ 3) {ω : E} (hω : ω ^ 2 + ω + 1 = 0) : ω ≠ 1 := by
  intro h
  have h3 : (3 : E) = 0 := by
    rw [h] at hω
    norm_num at hω ⊢
    exact hω
  have hpdvd : p ∣ 3 := (CharP.cast_eq_zero_iff E p 3).mp h3
  exact hp3 ((Nat.prime_dvd_prime_iff_eq Fact.out Nat.prime_three).1 hpdvd)

private theorem k328dplo_core
    (hEig : ∀ (E : Type) [Field E] [Finite E], ringChar E ≠ 2 → ∀ (n : ℕ)
      (Y : Subgroup (Matrix.SpecialLinearGroup (Fin n) E)), ⁅Y, Y⁆ = Y →
      ∀ z ∈ Y, (∀ y ∈ Y, Commute z y) → orderOf z = 3 → ∀ μ : E, μ ≠ 1 →
        Module.End.eigenspace (Matrix.toLin' (z : Matrix (Fin n) (Fin n) E)) μ ≠ ⊥ →
        Module.finrank E
            (Module.End.eigenspace (Matrix.toLin' (z : Matrix (Fin n) (Fin n) E)) μ) ≤ 4 →
        ∀ (W : Type) [Group W] (φ : ↥Y →* W), Function.Surjective φ →
          φ.ker ≤ Subgroup.center ↥Y → ¬ (LieModel W .PSL 3 2 2 ∨ LieModel W .PSU 3 2 3))
    (hChar3 : ∀ (E : Type) [Field E] [Finite E], ringChar E = 3 → ∀ (n : ℕ), n ≤ 4 →
      ∀ (Y : Subgroup (Matrix.SpecialLinearGroup (Fin n) E)), ⁅Y, Y⁆ = Y →
      ∀ z ∈ Y, (∀ y ∈ Y, Commute z y) → orderOf z = 3 →
        ∀ (W : Type) [Group W] (φ : ↥Y →* W), Function.Surjective φ →
          φ.ker ≤ Subgroup.center ↥Y → ¬ (LieModel W .PSL 3 2 2 ∨ LieModel W .PSU 3 2 3)) :
    ∀ (S : Type) [Group S] [Finite S], IsSimpleGroup S → ∀ n p f : ℕ, p ≠ 2 →
      (n ≤ 4 ∨ ((n = 5 ∨ n = 6 ∨ n = 7) ∧ p ^ f % 3 = 2)) → LieModel S .PSL n p f →
        ¬ K328DetPosIn S := by
  intro S _ _ hS n p f hp2 hn hL
  rintro ⟨Z, X, hPos, hXne⟩
  have hclass := hL.statedClassicalModel (t := .PSL) (by decide)
  obtain ⟨hadm, hmodel⟩ := hclass
  obtain ⟨K, hfield, hfinite, hKcard, ⟨e⟩⟩ := hmodel
  let : Field K := hfield
  let : Finite K := hfinite
  have hp_prime : p.Prime := hadm.1
  have hf : 1 ≤ f := hadm.2.1
  have hPosG : Pos (StatedProj (StatedSL n K)) (Z.map e.toMonoidHom)
      (X.map e.toMonoidHom) := pos_map e hPos
  let U := StatedSL n K
  let G := StatedProj U
  let π : U →* G := QuotientGroup.mk' ((StatedScalars (Fin n) K).subgroupOf U)
  have hπ : Function.Surjective π := QuotientGroup.mk'_surjective _
  have hker : π.ker ≤ Subgroup.center U := by
    change (QuotientGroup.mk' ((StatedScalars (Fin n) K).subgroupOf U)).ker ≤
      Subgroup.center U
    rw [QuotientGroup.ker_mk']
    exact statedScalars_subgroupOf_le_center U
  let Xbar : Subgroup G := X.map e.toMonoidHom
  have hqs : CFSG.Open.IsQuasisimple ↥Xbar := hPosG.2.2.2.2.1
  have hcenXbar : Nat.card (Subgroup.center ↥Xbar) = 3 := hPosG.2.2.2.2.2.1
  have hLieX : LieModel (↥Xbar ⧸ Subgroup.center ↥Xbar) .PSL 3 2 2 ∨
      LieModel (↥Xbar ⧸ Subgroup.center ↥Xbar) .PSU 3 2 3 := hPosG.2.2.2.2.2.2
  have hLperf : ⁅Xbar, Xbar⁆ = Xbar := by
    have : Group.IsPerfect ↥Xbar := ⟨hqs.1⟩
    exact Subgroup.commutator_eq_self
  have hXtop : commutator ↥Xbar = ⊤ :=
    Group.isPerfect_def.mp (Subgroup.isPerfect_iff.mpr hLperf)
  obtain ⟨Y, ψ, hYperf, hYmap, hψ, hψker⟩ := k328dplo_descent π hπ hker hXtop
  have hYtop : commutator ↥Y = ⊤ :=
    Group.isPerfect_def.mp (Subgroup.isPerfect_iff.mpr hYperf)
  obtain ⟨z, hzcenter, hzord⟩ := k328dpso_center_order_three ψ hψ hψker
    (Subgroup.isPerfect_iff.mpr hYperf) hcenXbar
  let W : Type := ↥Xbar ⧸ Subgroup.center ↥Xbar
  let φW : ↥Y →* W := (QuotientGroup.mk' (Subgroup.center ↥Xbar)).comp ψ
  have hφWsurj : Function.Surjective φW :=
    (QuotientGroup.mk'_surjective _).comp hψ
  have hφWker : φW.ker ≤ Subgroup.center ↥Y := by
    have hcomap := k328dplo_comap_center_of_surjective hYtop ψ hψ hψker
    intro y hy
    rw [← hcomap]
    exact Subgroup.mem_comap.mpr ((QuotientGroup.eq_one_iff _).mp hy)
  by_cases hp3eq : p = 3
  · have hn4 : n ≤ 4 := by
      rcases hn with h | ⟨-, hmod⟩
      · exact h
      · exfalso
        have hdiv : 3 ∣ p ^ f := by rw [hp3eq]; exact dvd_pow_self 3 (by omega)
        have h0 : p ^ f % 3 = 0 := Nat.mod_eq_zero_of_dvd hdiv
        omega
    have hcharK : CharP K 3 := k328dplo_charP_of_card (K := K) Nat.prime_three (by
      rw [← hp3eq]; exact hKcard)
    have hring3 : ringChar K = 3 := ringChar.eq_iff.mpr hcharK
    let SLhom : ↥Y →* Matrix.SpecialLinearGroup (Fin n) K :=
      k328dplo_slHom (RingHom.id K) n Y
    have hSLinj : Function.Injective SLhom :=
      k328dplo_slHom_injective (RingHom.id K) Function.injective_id n Y
    let Ysl : Subgroup (Matrix.SpecialLinearGroup (Fin n) K) := SLhom.range
    have hYsl : ⁅Ysl, Ysl⁆ = Ysl := by
      have : Group.IsPerfect ↥Y := Subgroup.isPerfect_iff.mpr hYperf
      have : Group.IsPerfect Ysl := Group.IsPerfect.range SLhom
      exact Subgroup.commutator_eq_self
    let zY : Matrix.SpecialLinearGroup (Fin n) K := SLhom z
    have hzYmem : zY ∈ Ysl := MonoidHom.mem_range.mpr ⟨z, rfl⟩
    have hzYne : zY ≠ 1 := by
      intro h
      have hz1 : z = 1 := hSLinj (h.trans (map_one SLhom).symm)
      rw [hz1, orderOf_one] at hzord
      exact absurd hzord (by norm_num)
    have hzYord : orderOf zY = 3 := by
      have hdvd : orderOf zY ∣ 3 := by
        have h1 : orderOf zY ∣ orderOf z := orderOf_map_dvd SLhom z
        rwa [hzord] at h1
      rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h1 | h3
      · exact absurd (orderOf_eq_one_iff.mp h1) hzYne
      · exact h3
    have hzYcomm : ∀ y ∈ Ysl, Commute zY y := by
      rintro y ⟨q, rfl⟩
      show zY * SLhom q = SLhom q * zY
      rw [← map_mul, ← map_mul]
      congr 1
      exact (Subgroup.mem_center_iff.mp hzcenter q).symm
    have hSLker : SLhom.ker ≤ φW.ker := by
      have hbot : SLhom.ker = ⊥ := (MonoidHom.ker_eq_bot_iff SLhom).mpr hSLinj
      rw [hbot]; exact bot_le
    obtain ⟨φY, hφYsurj, hφYker⟩ := k328dpso_lift_range SLhom φW hφWsurj hφWker hSLker
    exact hChar3 K hring3 n hn4 Ysl hYsl zY hzYmem hzYcomm hzYord W φY hφYsurj hφYker hLieX
  · have hp3 : p ≠ 3 := fun h => hp3eq h
    have hcharK : CharP K p := k328dplo_charP_of_card hp_prime hKcard
    have hfact : Fact p.Prime := ⟨hp_prime⟩
    let E := FiniteField.Extension K p 2
    obtain ⟨ω, hωeq⟩ := k328dplo_omega K p hp3
    have hEcard : Nat.card E = p ^ (f * 2) := by
      change Nat.card (FiniteField.Extension K p 2) = p ^ (f * 2)
      rw [FiniteField.natCard_extension, hKcard, ← pow_mul]
    have hcharE : CharP E p := k328dplo_charP_of_card hp_prime hEcard
    have hErchar : ringChar E ≠ 2 := by
      have h : ringChar E = p := ringChar.eq_iff.mpr hcharE
      rw [h]; exact hp2
    have hfinE : Module.finrank K E = 2 := by
      change Module.finrank K (FiniteField.Extension K p 2) = 2
      exact FiniteField.finrank_extension K p 2
    let σ : E ≃ₐ[K] E := FiniteField.Extension.frob K p 2
    let SLhom : ↥Y →* Matrix.SpecialLinearGroup (Fin n) E :=
      k328dplo_slHom (algebraMap K E) n Y
    have hSLinj : Function.Injective SLhom :=
      k328dplo_slHom_injective (algebraMap K E) (FaithfulSMul.algebraMap_injective K E) n Y
    let Ysl : Subgroup (Matrix.SpecialLinearGroup (Fin n) E) := SLhom.range
    have hYsl : ⁅Ysl, Ysl⁆ = Ysl := by
      have : Group.IsPerfect ↥Y := Subgroup.isPerfect_iff.mpr hYperf
      have : Group.IsPerfect Ysl := Group.IsPerfect.range SLhom
      exact Subgroup.commutator_eq_self
    let zY : Matrix.SpecialLinearGroup (Fin n) E := SLhom z
    have hzYmem : zY ∈ Ysl := MonoidHom.mem_range.mpr ⟨z, rfl⟩
    have hzYne : zY ≠ 1 := by
      intro h
      have hz1 : z = 1 := hSLinj (h.trans (map_one SLhom).symm)
      rw [hz1, orderOf_one] at hzord
      exact absurd hzord (by norm_num)
    have hzYord : orderOf zY = 3 := by
      have hdvd : orderOf zY ∣ 3 := by
        have h1 : orderOf zY ∣ orderOf z := orderOf_map_dvd SLhom z
        rwa [hzord] at h1
      rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h1 | h3
      · exact absurd (orderOf_eq_one_iff.mp h1) hzYne
      · exact h3
    have hzYcomm : ∀ y ∈ Ysl, Commute zY y := by
      rintro y ⟨q, rfl⟩
      show zY * SLhom q = SLhom q * zY
      rw [← map_mul, ← map_mul]
      congr 1
      exact (Subgroup.mem_center_iff.mp hzcenter q).symm
    have hSLker : SLhom.ker ≤ φW.ker := by
      have hbot : SLhom.ker = ⊥ := (MonoidHom.ker_eq_bot_iff SLhom).mpr hSLinj
      rw [hbot]; exact bot_le
    obtain ⟨φY, hφYsurj, hφYker⟩ := k328dpso_lift_range SLhom φW hφWsurj hφWker hSLker
    have hzY3 : zY ^ 3 = 1 := orderOf_dvd_iff_pow_eq_one.mp (by rw [hzYord])
    have hzYglne : (zY : GL (Fin n) E) ≠ 1 := by
      intro h
      apply hzYne
      apply Subtype.ext
      have h' := congrArg (fun x : GL (Fin n) E => (x : Matrix (Fin n) (Fin n) E)) h
      simpa using h'
    have hzY3gl : (zY : GL (Fin n) E) ^ 3 = 1 := by
      have h := congrArg (fun x : Matrix.SpecialLinearGroup (Fin n) E =>
        (x : GL (Fin n) E)) hzY3
      simpa using h
    let zmat : Matrix (Fin n) (Fin n) K :=
      (((z : StatedSL n K) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)
    have hzYmat : (zY : Matrix (Fin n) (Fin n) E) = zmat.map (algebraMap K E) := by
      show ((k328dplo_slHom (algebraMap K E) n Y z :
        Matrix.SpecialLinearGroup (Fin n) E) : Matrix (Fin n) (Fin n) E) =
        zmat.map (algebraMap K E)
      rw [k328dplo_slHom_apply]
      rfl
    have hω1 : ω ≠ 1 := k328dplo_omega_ne_one hp3 hωeq
    have hω2ne : ω ^ 2 ≠ 1 := k328dpso_mu_sq_ne_one hωeq hω1
    have hnz := k328dpso_eigenspace_ne_bot_or n (zY : GL (Fin n) E) hzY3gl hzYglne
      (μ := ω) hωeq
    rcases hn with hn4 | ⟨hn567, hmod⟩
    · have hbound : ∀ μ : E, Module.finrank E
          (Module.End.eigenspace (Matrix.toLin' (zY : Matrix (Fin n) (Fin n) E)) μ) ≤ 4 := by
        intro μ
        have hb := k328dplo_eigenspace_finrank_le_n (zY : Matrix (Fin n) (Fin n) E) μ
        omega
      rcases hnz with hbot | hbot
      · exact hEig E hErchar n Ysl hYsl zY hzYmem hzYcomm hzYord ω hω1 hbot (hbound ω)
          W φY hφYsurj hφYker hLieX
      · exact hEig E hErchar n Ysl hYsl zY hzYmem hzYcomm hzYord (ω ^ 2) hω2ne hbot
          (hbound (ω ^ 2)) W φY hφYsurj hφYker hLieX
    · have hn7 : n ≤ 7 := by rcases hn567 with h | h | h <;> omega
      have hmodK : Nat.card K % 3 = 2 := by rw [hKcard]; exact hmod
      have hσω : σ ω = ω ^ 2 := k328dplo_frob_omega (K := K) p hωeq hmodK
      have hσω2 : σ (ω ^ 2) = (ω ^ 2) ^ 2 := by
        rw [map_pow, hσω]
      have hω2poly : (ω ^ 2) ^ 2 + ω ^ 2 + 1 = 0 := by
        have hω3 : ω ^ 3 = 1 := by linear_combination (ω - 1) * hωeq
        linear_combination hωeq + ω * hω3
      have hfinω : Module.finrank E
          (Module.End.eigenspace (Matrix.toLin' (zY : Matrix (Fin n) (Fin n) E)) ω) ≤ 4 := by
        have hb := k328dplo_eigen_finrank_le_three hn7 hfinE σ p hp3 hσω hωeq zmat
        rw [hzYmat]
        omega
      have hfinω2 : Module.finrank E
          (Module.End.eigenspace (Matrix.toLin' (zY : Matrix (Fin n) (Fin n) E)) (ω ^ 2)) ≤ 4 := by
        have hb := k328dplo_eigen_finrank_le_three hn7 hfinE σ p hp3 hσω2 hω2poly zmat
        rw [hzYmat]
        omega
      rcases hnz with hbot | hbot
      · exact hEig E hErchar n Ysl hYsl zY hzYmem hzYcomm hzYord ω hω1 hbot hfinω
          W φY hφYsurj hφYker hLieX
      · exact hEig E hErchar n Ysl hYsl zY hzYmem hzYcomm hzYord (ω ^ 2) hω2ne hbot hfinω2
          W φY hφYsurj hφYker hLieX

theorem k328det_famPSLOdd :
    ∀ (S : Type) [Group S] [Finite S], IsSimpleGroup S → ∀ n p f : ℕ, p ≠ 2 →
      (n ≤ 4 ∨ ((n = 5 ∨ n = 6 ∨ n = 7) ∧ p ^ f % 3 = 2)) → LieModel S .PSL n p f →
        ¬ K328DetPosIn S :=
  k328dplo_core k328det_oddEigenblock k328det_charThreeBlock

private theorem k328dpuo_final {S : Type} [Group S] [Finite S]
    (K : Type) [Field K] [Finite K] (n p f : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f)
    (hcard : Nat.card K = (p ^ f) ^ 2)
    (hcond : n ≤ 4 ∨ ((n = 5 ∨ n = 6 ∨ n = 7) ∧ p ^ f % 3 = 1)) (hn1 : 1 ≤ n)
    (e : S ≃* StatedProj (StatedSU n (p ^ f) K)) (hpos : K328DetPosIn S) : False := by
  have hposT : K328DetPosIn (StatedProj (StatedSU n (p ^ f) K)) :=
    k328dpuo_pos_transport K n (p ^ f) e hpos
  obtain ⟨Z, X, hposZX, -⟩ := hposT
  exact k328dpuo_no_pos_model K n p f hp hp2 hf hcard hcond hn1 Z X hposZX

theorem k328det_famPSUOdd :
    ∀ (S : Type) [Group S] [Finite S], IsSimpleGroup S → ∀ n p f : ℕ, p ≠ 2 →
      (n ≤ 4 ∨ ((n = 5 ∨ n = 6 ∨ n = 7) ∧ p ^ f % 3 = 1)) → LieModel S .PSU n p f →
        ¬ K328DetPosIn S := by
  intro S _ _ hS n p f hp2 hcond hmodel hpos
  obtain ⟨K, hfield, hfinite, hcard, ⟨e⟩⟩ := k328dpuo_model_unpack (S := S) hmodel
  have hadm : StatedLieAdmissible .PSU n p f := hmodel.admissible
  obtain ⟨hp, hf, hn3, -⟩ := hadm
  exact @k328dpuo_final S _ _ K hfield hfinite n p f hp hp2 hf hcard hcond (by omega) e hpos

theorem k328det_famPSpOdd :
    ∀ (S : Type) [Group S] [Finite S], IsSimpleGroup S → ∀ n p f : ℕ, p ≠ 2 →
      (n = 2 ∨ (n = 3 ∧ p ≠ 3)) → LieModel S .PSp n p f → ¬ K328DetPosIn S :=
  k328dpso_core k328det_oddEigenblock k328det_charThreeBlock

theorem k328det_famPOmegaMinusOdd :
    ∀ (S : Type) [Group S] [Finite S], IsSimpleGroup S → ∀ p f : ℕ, p ≠ 2 → p ≠ 3 →
      LieModel S .POmegaMinus 4 p f → ¬ K328DetPosIn S := by
  exact k328domo_core k328det_oddEigenblock

private abbrev k328dom7_ι : Type := Fin 3 ⊕ Fin 3 ⊕ Unit

private abbrev k328dom7_H (K : Type) [Field K] : Subgroup (GL k328dom7_ι K) :=
  CFSG.Open.StatedOmega (CFSG.Open.StatedQuadOdd 3 K)

private noncomputable def k328dom7_e7 : k328dom7_ι ≃ Fin 7 :=
  (Fintype.equivFin k328dom7_ι).trans (finCongr (by simp [k328dom7_ι]))

open CFSG.LieType.Universal.Spin in
private theorem k328dom7_polar_map {K E : Type} [Field K] [Field E] (φ : K →+* E)
    (x y : k328dom7_ι → K) :
    QuadraticMap.polar (quadOdd 3 E) (φ ∘ x) (φ ∘ y) =
      φ (QuadraticMap.polar (quadOdd 3 K) x y) := by
  rw [polar_quadOdd, polar_quadOdd]
  simp only [Function.comp_apply]
  rw [map_add, map_sum]
  congr 1
  · exact Finset.sum_congr rfl fun i _ => by rw [map_add, map_mul, map_mul]
  · simp only [map_mul, map_ofNat]

open CFSG.LieType.Universal.Spin in
private theorem k328dom7_isometry_baseChange {K E : Type} [Field K] [Field E] (φ : K →+* E)
    (A : GL k328dom7_ι K)
    (hA : ∀ v : k328dom7_ι → K,
      quadOdd 3 K ((A : Matrix k328dom7_ι k328dom7_ι K) *ᵥ v) = quadOdd 3 K v) :
    ∀ u v : k328dom7_ι → E,
      QuadraticMap.polar (quadOdd 3 E) ((Matrix.GeneralLinearGroup.map φ A) *ᵥ u)
          ((Matrix.GeneralLinearGroup.map φ A) *ᵥ v) =
        QuadraticMap.polar (quadOdd 3 E) u v := by
  classical
  let BK : LinearMap.BilinForm K (k328dom7_ι → K) := QuadraticMap.polarBilin (quadOdd 3 K)
  let BE : LinearMap.BilinForm E (k328dom7_ι → E) := QuadraticMap.polarBilin (quadOdd 3 E)
  let JK : Matrix k328dom7_ι k328dom7_ι K := LinearMap.BilinForm.toMatrix' BK
  let JE : Matrix k328dom7_ι k328dom7_ι E := LinearMap.BilinForm.toMatrix' BE
  have hpolK : ∀ x y : k328dom7_ι → K,
      QuadraticMap.polar (quadOdd 3 K) ((A : Matrix k328dom7_ι k328dom7_ι K) *ᵥ x)
          ((A : Matrix k328dom7_ι k328dom7_ι K) *ᵥ y) =
        QuadraticMap.polar (quadOdd 3 K) x y := by
    intro x y
    simp only [QuadraticMap.polar]
    rw [← Matrix.mulVec_add, hA, hA, hA]
  have hcompK : BK.comp (Matrix.toLin' (A : Matrix k328dom7_ι k328dom7_ι K))
      (Matrix.toLin' (A : Matrix k328dom7_ι k328dom7_ι K)) = BK := by
    apply LinearMap.BilinForm.ext
    intro x y
    simpa [BK, LinearMap.BilinForm.comp_apply, Matrix.toLin'_apply] using hpolK x y
  have hmatK : (A : Matrix k328dom7_ι k328dom7_ι K)ᵀ * JK *
      (A : Matrix k328dom7_ι k328dom7_ι K) = JK := by
    have h := congrArg (LinearMap.BilinForm.toMatrix' (R₁ := K) (n := k328dom7_ι)) hcompK
    simpa [LinearMap.BilinForm.toMatrix'_comp, LinearMap.toMatrix'_toLin'] using h
  have hJE : JE = JK.map φ := by
    dsimp only [JE, JK]
    apply Matrix.ext
    intro i j
    simp only [Matrix.map_apply, LinearMap.BilinForm.toMatrix'_apply]
    have hsingle : (Pi.single i (1 : E)) = φ ∘ (Pi.single i (1 : K)) := by
      ext k; simp only [Function.comp_apply, Pi.single_apply]; split_ifs <;> simp
    have hsingle' : (Pi.single j (1 : E)) = φ ∘ (Pi.single j (1 : K)) := by
      ext k; simp only [Function.comp_apply, Pi.single_apply]; split_ifs <;> simp
    rw [hsingle, hsingle']
    exact k328dom7_polar_map φ (Pi.single i (1 : K)) (Pi.single j (1 : K))
  have hmatE : ((A : Matrix k328dom7_ι k328dom7_ι K).map φ)ᵀ * JE *
      (A : Matrix k328dom7_ι k328dom7_ι K).map φ = JE := by
    rw [hJE]
    rw [← Matrix.transpose_map, ← Matrix.map_mul, ← Matrix.map_mul, hmatK]
  have hcompE : BE.comp (Matrix.toLin' ((A : Matrix k328dom7_ι k328dom7_ι K).map φ))
      (Matrix.toLin' ((A : Matrix k328dom7_ι k328dom7_ι K).map φ)) = BE := by
    apply LinearMap.BilinForm.toMatrix'.injective
    simpa [LinearMap.BilinForm.toMatrix'_comp, LinearMap.toMatrix'_toLin'] using hmatE
  intro u v
  have h := congrArg (fun B : LinearMap.BilinForm E (k328dom7_ι → E) => B u v) hcompE
  simpa [BE, LinearMap.BilinForm.comp_apply, Matrix.toLin'_apply,
    Matrix.GeneralLinearGroup.map_apply] using h

open CFSG.LieType.Universal.Spin in
private theorem k328dom7_eigenspace_finrank_le {E : Type} [Field E] (h2 : (2 : E) ≠ 0)
    (z : GL k328dom7_ι E)
    (hz : ∀ u v : k328dom7_ι → E,
      QuadraticMap.polar (quadOdd 3 E) ((z : Matrix k328dom7_ι k328dom7_ι E) *ᵥ u)
          ((z : Matrix k328dom7_ι k328dom7_ι E) *ᵥ v) = QuadraticMap.polar (quadOdd 3 E) u v)
    {μ : E} (hμ2 : μ ^ 2 ≠ 1) :
    Module.finrank E
        (Module.End.eigenspace (Matrix.toLin' ((z : Matrix k328dom7_ι k328dom7_ι E))) μ) ≤ 3 := by
  let B : LinearMap.BilinForm E (k328dom7_ι → E) := QuadraticMap.polarBilin (quadOdd 3 E)
  set W : Submodule E (k328dom7_ι → E) :=
    Module.End.eigenspace (Matrix.toLin' ((z : Matrix k328dom7_ι k328dom7_ι E))) μ with hWdef
  have hW : W ≤ B.orthogonal W := by
    intro v hv
    change v ∈ Submodule.orthogonalBilin B W
    rw [Submodule.mem_orthogonalBilin]
    intro w hw
    have hw' : (z : Matrix k328dom7_ι k328dom7_ι E) *ᵥ w = μ • w := by
      have h := Module.End.mem_eigenspace_iff.mp (hWdef ▸ hw)
      change (z : Matrix k328dom7_ι k328dom7_ι E) *ᵥ w = μ • w at h
      exact h
    have hv' : (z : Matrix k328dom7_ι k328dom7_ι E) *ᵥ v = μ • v := by
      have h := Module.End.mem_eigenspace_iff.mp (hWdef ▸ hv)
      change (z : Matrix k328dom7_ι k328dom7_ι E) *ᵥ v = μ • v at h
      exact h
    have hpres := hz w v
    rw [hw', hv'] at hpres
    have hthis : μ * (μ * B w v) = B w v := by
      simpa [B, map_smul, smul_eq_mul, mul_assoc] using hpres
    have hzero : (μ ^ 2 - 1) * B w v = 0 := by
      have h : μ ^ 2 * B w v = B w v := by
        calc μ ^ 2 * B w v = μ * (μ * B w v) := by ring
          _ = B w v := hthis
      rw [sub_mul, one_mul, h, sub_self]
    exact (mul_eq_zero.mp hzero).resolve_left (sub_ne_zero.mpr hμ2)
  have hfin := LinearMap.BilinForm.finrank_orthogonal
    (CFSG.LieType.Universal.Spin.nondegenerate_polarBilin_quadOdd 3 E h2) W
  have hle : Module.finrank E W ≤ Module.finrank E (B.orthogonal W) :=
    Submodule.finrank_mono hW
  have hdim : Module.finrank E (Fin 3 ⊕ Fin 3 ⊕ Unit → E) = 7 := by
    rw [Module.finrank_fintype_fun_eq_card]
    simp
  rw [hfin, hdim] at hle
  set n : ℕ := Module.finrank E W with hn
  have hle' : n ≤ 7 - n := by rw [hn]; exact hle
  have : n ≤ 3 := by omega
  rwa [hn] at this

private theorem k328dom7_eigenspace_reindex_finrank {E : Type} [Field E]
    (A : Matrix k328dom7_ι k328dom7_ι E) (μ : E) :
    Module.finrank E
        (Module.End.eigenspace
          (Matrix.toLin' (Matrix.reindex k328dom7_e7 k328dom7_e7 A)) μ) =
      Module.finrank E (Module.End.eigenspace (Matrix.toLin' A) μ) := by
  let F : (k328dom7_ι → E) ≃ₗ[E] (Fin 7 → E) := LinearEquiv.funCongrLeft E E k328dom7_e7.symm
  have hreindex : Matrix.toLin' (Matrix.reindex k328dom7_e7 k328dom7_e7 A) =
      (F : (k328dom7_ι → E) →ₗ[E] (Fin 7 → E)) ∘ₗ (Matrix.toLin' A) ∘ₗ
        ((F.symm : (Fin 7 → E) ≃ₗ[E] (k328dom7_ι → E)) :
          (Fin 7 → E) →ₗ[E] (k328dom7_ι → E)) := by
    rw [Matrix.toLin'_reindex]
    rfl
  have hmap : Module.End.eigenspace
        (Matrix.toLin' (Matrix.reindex k328dom7_e7 k328dom7_e7 A)) μ =
      (Module.End.eigenspace (Matrix.toLin' A) μ).map
        (F : (k328dom7_ι → E) →ₗ[E] (Fin 7 → E)) := by
    ext w
    rw [Submodule.mem_map]
    constructor
    · intro hw
      refine ⟨F.symm w, ?_, F.apply_symm_apply w⟩
      rw [Module.End.mem_eigenspace_iff] at hw ⊢
      rw [hreindex] at hw
      have := congrArg F.symm hw
      simpa [LinearMap.comp_apply] using this
    · rintro ⟨v, hv, rfl⟩
      rw [Module.End.mem_eigenspace_iff] at hv ⊢
      rw [hreindex]
      change F (Matrix.toLin' A (F.symm (F v))) = μ • F v
      rw [F.symm_apply_apply, hv, F.map_smul]
  rw [hmap, LinearEquiv.finrank_map_eq]

private noncomputable def k328dom7_matHom {K E : Type} [Field K] [Field E] (φ : K →+* E) :
    Matrix k328dom7_ι k328dom7_ι K →+* Matrix (Fin 7) (Fin 7) E :=
  (Matrix.reindexRingEquiv E k328dom7_e7).toRingHom.comp (φ.mapMatrix)

private theorem k328dom7_matHom_det {K E : Type} [Field K] [Field E] (φ : K →+* E)
    (M : Matrix k328dom7_ι k328dom7_ι K) (hM : M.det = 1) :
    ((k328dom7_matHom φ) M).det = 1 := by
  show (Matrix.reindex k328dom7_e7 k328dom7_e7 (φ.mapMatrix M)).det = 1
  rw [Matrix.det_reindex_self, ← RingHom.map_det, hM, RingHom.map_one]

private noncomputable def k328dom7_slHom {K E : Type} [Field K] [Field E] (φ : K →+* E) :
    k328dom7_H K →* Matrix.SpecialLinearGroup (Fin 7) E where
  toFun g := ⟨k328dom7_matHom φ (g.1 : Matrix k328dom7_ι k328dom7_ι K),
    k328dom7_matHom_det φ _ (k328domo_det_eq_one (CFSG.Open.StatedQuadOdd 3 K) g.2)⟩
  map_one' := by
    apply Subtype.ext
    exact map_one (k328dom7_matHom φ)
  map_mul' := by
    intro g h
    apply Subtype.ext
    exact map_mul (k328dom7_matHom φ) _ _

private theorem k328dom7_matHom_injective {K E : Type} [Field K] [Field E] {φ : K →+* E}
    (hφ : Function.Injective φ) : Function.Injective (k328dom7_matHom φ) := by
  intro A B h
  apply Matrix.ext
  intro i j
  have h2 := congrFun (congrFun h (k328dom7_e7 i)) (k328dom7_e7 j)
  have h3 : φ (A i j) = φ (B i j) := by
    simpa [k328dom7_matHom, RingHom.mapMatrix_apply, Matrix.reindex_apply] using h2
  exact hφ h3

private theorem k328dom7_slHom_injective {K E : Type} [Field K] [Field E] {φ : K →+* E}
    (hφ : Function.Injective φ) : Function.Injective (k328dom7_slHom φ) := by
  intro g h hgh
  apply Subtype.ext
  apply Units.ext
  apply k328dom7_matHom_injective hφ
  exact congrArg (fun x : Matrix.SpecialLinearGroup (Fin 7) E =>
    (x : Matrix (Fin 7) (Fin 7) E)) hgh

private theorem k328dom7_ker_le_center (K : Type) [Field K] :
    (QuotientGroup.mk' ((StatedScalars k328dom7_ι K).subgroupOf (k328dom7_H K))).ker ≤
      Subgroup.center (k328dom7_H K) := by
  intro x hx
  rw [QuotientGroup.ker_mk'] at hx
  rw [Subgroup.mem_center_iff]
  intro y
  apply Subtype.ext
  have hxZ : (x.1 : GL k328dom7_ι K) ∈ Subgroup.center (GL k328dom7_ι K) := by
    rw [← CFSG.Open.StatedAPI.statedScalars_eq_center]
    exact hx
  exact Subgroup.mem_center_iff.mp hxZ y.1

private theorem k328dom7_eigenspace_reindex_le_four {K E : Type} [Field K] [Field E]
    (φ : K →+* E) (h2E : (2 : E) ≠ 0)
    {g : GL k328dom7_ι K} (hg : g ∈ k328dom7_H K)
    {ω : E} (hω : ω ^ 2 + ω + 1 = 0) (hω1 : ω ≠ 1) :
    Module.finrank E (Module.End.eigenspace
        (Matrix.toLin' (Matrix.reindex k328dom7_e7 k328dom7_e7
          (φ.mapMatrix (g : Matrix k328dom7_ι k328dom7_ι K)))) ω) ≤ 4 := by
  rw [k328dom7_eigenspace_reindex_finrank]
  have hμ2 : ω ^ 2 ≠ 1 := k328domo_omega_sq_ne_one hω hω1
  have hpres : ∀ u v : k328dom7_ι → E,
      QuadraticMap.polar (CFSG.LieType.Universal.Spin.quadOdd 3 E)
          ((Matrix.GeneralLinearGroup.map φ g) *ᵥ u)
          ((Matrix.GeneralLinearGroup.map φ g) *ᵥ v) =
        QuadraticMap.polar (CFSG.LieType.Universal.Spin.quadOdd 3 E) u v :=
    k328dom7_isometry_baseChange φ g (fun v => by
      have h := CFSG.GroupTheory.WeirSylow.apply_mulVec_of_mem_isometryCore
        (CFSG.GroupTheory.WeirSylow.statedOmega_le_isometryCore
          (CFSG.Open.StatedQuadOdd 3 K) hg) v
      rw [CFSG.LieType.Universal.Spin.coe_quadOdd] at ⊢
      exact h)
  have hle := k328dom7_eigenspace_finrank_le h2E (Matrix.GeneralLinearGroup.map φ g) hpres hμ2
  exact le_trans hle (by norm_num)

private theorem k328dom7_H_contra {K : Type} [Field K] [Finite K] {p f : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) (hp3 : p ≠ 3) (hcard : Nat.card K = p ^ f)
    {Zb Xb : Subgroup (CFSG.Open.StatedProj (k328dom7_H K))}
    (hZb : Pos (CFSG.Open.StatedProj (k328dom7_H K)) Zb Xb) (_hXbne : Xb ≠ ⊤)
    (hEig : ∀ (E : Type) [Field E] [Finite E], ringChar E ≠ 2 → ∀ (n : ℕ)
      (Y : Subgroup (Matrix.SpecialLinearGroup (Fin n) E)), ⁅Y, Y⁆ = Y →
      ∀ z ∈ Y, (∀ y ∈ Y, Commute z y) → orderOf z = 3 → ∀ μ : E, μ ≠ 1 →
        Module.End.eigenspace (Matrix.toLin' (z : Matrix (Fin n) (Fin n) E)) μ ≠ ⊥ →
        Module.finrank E
            (Module.End.eigenspace (Matrix.toLin' (z : Matrix (Fin n) (Fin n) E)) μ) ≤ 4 →
        ∀ (W : Type) [Group W] (φ : ↥Y →* W), Function.Surjective φ →
          φ.ker ≤ Subgroup.center ↥Y → ¬ (LieModel W .PSL 3 2 2 ∨ LieModel W .PSU 3 2 3)) :
    False := by
  classical
  let H := k328dom7_H K
  let π : H →* CFSG.Open.StatedProj H :=
    QuotientGroup.mk' ((CFSG.Open.StatedScalars k328dom7_ι K).subgroupOf H)
  let L : Subgroup (CFSG.Open.StatedProj H) := Xb
  let M : Subgroup H := ⁅L.comap π, L.comap π⁆
  have hπsurj : Function.Surjective π := QuotientGroup.mk'_surjective _
  have hcen : π.ker ≤ Subgroup.center H := k328dom7_ker_le_center K
  have hperfL : Group.IsPerfect ↥L := Group.isPerfect_def.mpr hZb.2.2.2.2.1.1
  have hLperf : ⁅L, L⁆ = L := Subgroup.isPerfect_iff.mp hperfL
  have hMperf : Group.IsPerfect ↥M :=
    CFSG.GroupTheory.PerfectCover.isPerfect_commutator_comap π hπsurj hcen hLperf
  have hmapM : M.map π = L :=
    CFSG.GroupTheory.PerfectCover.map_commutator_comap π hπsurj hLperf
  let φX : ↥M →* ↥L :=
    { toFun := fun m => ⟨π m.1, by rw [← hmapM]; exact Subgroup.mem_map_of_mem π m.2⟩
      map_one' := by apply Subtype.ext; exact map_one π
      map_mul' := by intro a b; apply Subtype.ext; exact map_mul π a.1 b.1 }
  have hφXsurj : Function.Surjective φX := by
    intro l
    obtain ⟨m, hmM, hm⟩ := Subgroup.mem_map.mp (by rw [hmapM]; exact l.2)
    exact ⟨⟨m, hmM⟩, Subtype.ext hm⟩
  have hφXker : φX.ker ≤ Subgroup.center ↥M := by
    intro k hk
    rw [Subgroup.mem_center_iff]
    intro m
    apply Subtype.ext
    have hkπ : π k.1 = 1 := congrArg Subtype.val (MonoidHom.mem_ker.mp hk)
    have hkZ : k.1 ∈ Subgroup.center H := hcen (MonoidHom.mem_ker.mpr hkπ)
    exact Subgroup.mem_center_iff.mp hkZ m.1
  obtain ⟨z, hzcent, hzord⟩ :=
    k328domo_center_order_three φX hφXsurj hφXker hMperf hZb.2.2.2.2.2.1
  let W : Type := ↥L ⧸ Subgroup.center ↥L
  let φW : ↥M →* W := (QuotientGroup.mk' (Subgroup.center ↥L)).comp φX
  have hφWsurj : Function.Surjective φW :=
    (QuotientGroup.mk'_surjective (Subgroup.center ↥L)).comp hφXsurj
  have hφWker : φW.ker ≤ Subgroup.center ↥M := by
    intro k hk
    have hk' : φX k ∈ Subgroup.center ↥L :=
      (QuotientGroup.eq_one_iff (N := Subgroup.center ↥L) (φX k)).mp (MonoidHom.mem_ker.mp hk)
    exact k328domo_comap_center_le_center φX hφXker hMperf hk'
  have hWlie : LieModel W .PSL 3 2 2 ∨ LieModel W .PSU 3 2 3 := hZb.2.2.2.2.2.2
  obtain ⟨E, hEfield, hEfin, ι, ω, hιinj, hEchar, hω1, hωsum⟩ :=
    k328domo_exists_omega K hp2 hp3 hcard
  let : Field E := hEfield
  let : Finite E := hEfin
  have hE2 : (2 : E) ≠ 0 := Ring.two_ne_zero hEchar
  let gH : H := z.1
  let Y : Subgroup (Matrix.SpecialLinearGroup (Fin 7) E) := M.map (k328dom7_slHom ι)
  let zY : Matrix.SpecialLinearGroup (Fin 7) E := k328dom7_slHom ι gH
  have hYperf : ⁅Y, Y⁆ = Y := by
    show ⁅M.map (k328dom7_slHom ι), M.map (k328dom7_slHom ι)⁆ = M.map (k328dom7_slHom ι)
    rw [← Subgroup.map_commutator M M (k328dom7_slHom ι), Subgroup.isPerfect_iff.mp hMperf]
  have hzYmem : zY ∈ Y := Subgroup.mem_map_of_mem _ z.2
  have hzYcent : ∀ y ∈ Y, Commute zY y := by
    intro y hy
    obtain ⟨m, hmM, rfl⟩ := Subgroup.mem_map.mp hy
    rw [commute_iff_eq, ← map_mul, ← map_mul]
    congr 1
    exact congrArg Subtype.val (Subgroup.mem_center_iff.mp hzcent ⟨m, hmM⟩).symm
  have hzYord : orderOf zY = 3 := by
    change orderOf (k328dom7_slHom ι gH) = 3
    rw [orderOf_injective (k328dom7_slHom ι)
      (k328dom7_slHom_injective hιinj) gH, Subgroup.orderOf_coe z, hzord]
  have hY3 : zY ^ 3 = 1 := by rw [← hzYord]; exact pow_orderOf_eq_one zY
  have hY3m : (zY : Matrix (Fin 7) (Fin 7) E) ^ 3 = 1 := congrArg Subtype.val hY3
  have hf3 : (Matrix.toLin' (zY : Matrix (Fin 7) (Fin 7) E)) ^ 3 = 1 := by
    rw [← Matrix.toLin'_pow, hY3m, Matrix.toLin'_one]; rfl
  have hne : Matrix.toLin' (zY : Matrix (Fin 7) (Fin 7) E) ≠ 1 := by
    intro h
    have h' : Matrix.toLin' (zY : Matrix (Fin 7) (Fin 7) E) =
        Matrix.toLin' (1 : Matrix (Fin 7) (Fin 7) E) := by
      rw [Matrix.toLin'_one, h]; rfl
    have hM : (zY : Matrix (Fin 7) (Fin 7) E) = 1 :=
      (LinearEquiv.injective (Matrix.toLin' : Matrix (Fin 7) (Fin 7) E ≃ₗ[E]
        ((Fin 7 → E) →ₗ[E] (Fin 7 → E)))) h'
    have hz1 : zY = 1 := Subtype.eq hM
    rw [hz1, orderOf_one] at hzYord
    omega
  have heig_ex : Module.End.eigenspace (Matrix.toLin' (zY : Matrix (Fin 7) (Fin 7) E)) ω ≠ ⊥ ∨
      Module.End.eigenspace (Matrix.toLin' (zY : Matrix (Fin 7) (Fin 7) E)) (ω ^ 2) ≠ ⊥ :=
    k328domo_eigenspace_or hf3 hne hωsum hω1
  have hVdim : ∀ μ : E, μ ^ 2 + μ + 1 = 0 → μ ≠ 1 →
      Module.finrank E (Module.End.eigenspace
        (Matrix.toLin' (zY : Matrix (Fin 7) (Fin 7) E)) μ) ≤ 4 := by
    intro μ hμ hμ1
    have h := k328dom7_eigenspace_reindex_le_four ι hE2
      (g := (gH : GL k328dom7_ι K)) gH.2 hμ hμ1
    change Module.finrank E (Module.End.eigenspace
      (Matrix.toLin' (Matrix.reindex k328dom7_e7 k328dom7_e7
        (ι.mapMatrix ((gH : GL k328dom7_ι K) : Matrix k328dom7_ι k328dom7_ι K)))) μ) ≤ 4
    exact h
  have hω2poly : (ω ^ 2) ^ 2 + ω ^ 2 + 1 = 0 := by
    have h3 : ω ^ 3 = 1 := by linear_combination (ω - 1) * hωsum
    linear_combination ω * h3 + hωsum
  have hω2ne : ω ^ 2 ≠ 1 := k328domo_omega_sq_ne_one hωsum hω1
  let eMY := Subgroup.equivMapOfInjective M (k328dom7_slHom ι) (k328dom7_slHom_injective hιinj)
  let φWY : ↥Y →* W := φW.comp (eMY.symm : ↥Y →* ↥M)
  have hφWYsurj : Function.Surjective φWY := by
    intro w
    obtain ⟨m, hm⟩ := hφWsurj w
    exact ⟨eMY m, by show φW (eMY.symm (eMY m)) = w; rw [MulEquiv.symm_apply_apply]; exact hm⟩
  have hφWYker : φWY.ker ≤ Subgroup.center ↥Y := by
    have hker : φWY.ker = (φW.ker).map eMY := by
      ext y
      rw [MonoidHom.mem_ker, Subgroup.mem_map]
      constructor
      · intro hy
        obtain ⟨m, rfl⟩ := eMY.surjective y
        exact ⟨m, by simpa [φWY] using hy, rfl⟩
      · rintro ⟨m, hm, rfl⟩
        simpa [φWY] using hm
    rw [hker]
    calc (φW.ker).map eMY ≤ (Subgroup.center ↥M).map eMY := Subgroup.map_mono hφWker
      _ = Subgroup.center ↥Y := Subgroup.map_center_eq eMY
  cases heig_ex with
  | inl hωne =>
    exact hEig E hEchar 7 Y hYperf zY hzYmem hzYcent hzYord ω hω1 hωne (hVdim ω hωsum hω1)
      W φWY hφWYsurj hφWYker hWlie
  | inr hV2ne =>
    exact hEig E hEchar 7 Y hYperf zY hzYmem hzYcent hzYord (ω ^ 2) hω2ne hV2ne
      (hVdim (ω ^ 2) hω2poly hω2ne) W φWY hφWYsurj hφWYker hWlie

private theorem k328dom7_core
    (hEig : ∀ (E : Type) [Field E] [Finite E], ringChar E ≠ 2 → ∀ (n : ℕ)
      (Y : Subgroup (Matrix.SpecialLinearGroup (Fin n) E)), ⁅Y, Y⁆ = Y →
      ∀ z ∈ Y, (∀ y ∈ Y, Commute z y) → orderOf z = 3 → ∀ μ : E, μ ≠ 1 →
        Module.End.eigenspace (Matrix.toLin' (z : Matrix (Fin n) (Fin n) E)) μ ≠ ⊥ →
        Module.finrank E
            (Module.End.eigenspace (Matrix.toLin' (z : Matrix (Fin n) (Fin n) E)) μ) ≤ 4 →
        ∀ (W : Type) [Group W] (φ : ↥Y →* W), Function.Surjective φ →
          φ.ker ≤ Subgroup.center ↥Y → ¬ (LieModel W .PSL 3 2 2 ∨ LieModel W .PSU 3 2 3)) :
    ∀ (S : Type) [Group S] [Finite S], IsSimpleGroup S → ∀ p f : ℕ, p ≠ 3 →
      LieModel S .POmegaOdd 3 p f → ¬ K328DetPosIn S := by
  intro S _ _ hS p f hp3 hmodel hpos
  have hclass : CFSG.Open.StatedClassicalModel S .POmegaOdd 3 p f :=
    CFSG.Blueprint.LieModel.statedClassicalModel hmodel (by decide)
  unfold CFSG.Open.StatedClassicalModel at hclass
  obtain ⟨hadm, K, hKfield, hKfin, hKcard, ⟨e⟩⟩ := hclass
  let : Field K := hKfield
  let : Finite K := hKfin
  have : Fact p.Prime := ⟨hadm.1⟩
  have hp2 : p ≠ 2 := hadm.2.2.2
  obtain ⟨Z, X, hZ, hXne⟩ := hpos
  have hXbne : X.map e.toMonoidHom ≠ ⊤ := by
    intro h
    have h' : X.map e.toMonoidHom = (⊤ : Subgroup S).map e.toMonoidHom := by
      rw [Subgroup.map_top_of_surjective _ e.surjective]; exact h
    exact hXne (Subgroup.map_injective e.injective h')
  exact k328dom7_H_contra hp2 hp3 hKcard (pos_map e hZ) hXbne hEig

theorem k328det_famPOmegaOdd :
    ∀ (S : Type) [Group S] [Finite S], IsSimpleGroup S → ∀ p f : ℕ, p ≠ 3 →
      LieModel S .POmegaOdd 3 p f → ¬ K328DetPosIn S :=
  k328dom7_core k328det_oddEigenblock

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.K328

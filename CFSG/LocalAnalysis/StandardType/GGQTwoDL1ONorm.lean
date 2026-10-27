module

public import CFSG.LocalAnalysis.StandardType.GGOrthFrameCore
public import CFSG.LocalAnalysis.StandardType.GGQTwoDL1OBlock
public import CFSG.RankThree.OrthogonalInvolutions.Dickson

public section

namespace CFSG.StandardType.QTwo

open Module Multiplicative QuadraticMap
open CFSG.RankThree.Classical2 (orthDerived)
open CFSG.ClassicalInvolution.PhanDn CFSG.ClassicalInvolution.Models.OrthogonalPairs
open CFSG.ClassicalGroups.Unitary CFSG.LieType.Universal.Unitary CFSG.LieType.Steinberg
open CFSG.LieType.BorelTits CFSG.ClassicalInvolution.Phan
open CFSG.ClassicalInvolution.Balance.StrongBalance.Unitary
open CFSG.RankThree.OrthogonalInvolutions (omegaGroup mem_omegaGroup commSpace mem_commSpace
  sub_mem_commSpace finrank_commSpace_reflection)

structure QTwoDL1ONormChart {p : ℕ} {G : Type} [Group G] {Bs L : Subgroup G}
    (Φ : OrthTorus.OrthFrameCore p Bs L) [Algebra Φ.F (GaloisField 2 2)] where
  E : QuadExt Φ.F (GaloisField 2 2) (unitaryInvolution (GaloisField 2 2) 2 1)
  χ : Φ.V ≃ₗ[Φ.F] (Fin Φ.r → GaloisField 2 2)
  ζ : normOne (unitaryInvolution (GaloisField 2 2) 2 1)
  ζ_ne_one : ζ ≠ 1
  ζ_pow : ζ ^ p = 1
  isometry : ∀ v, Qn E Φ.r (χ v) = Φ.Q v
  torus : ∀ (g : Fin Φ.r → Multiplicative (ZMod p)) (v : Φ.V),
    χ (Φ.Δ.τ g v) = diagHom Φ.F (unitaryInvolution (GaloisField 2 2) 2 1) Φ.r
      (fun i => ζ ^ (toAdd (g i)).val) (χ v)

variable {p : ℕ} {G : Type} [Group G] {Bs L : Subgroup G}

private theorem p9uONrm_trans_conj_mul {K : Type*} [Field K] {V W : Type*}
    [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W] (e : V ≃ₗ[K] W)
    (f g : W ≃ₗ[K] W) :
    e.trans ((f * g).trans e.symm) =
      (e.trans (f.trans e.symm)) * (e.trans (g.trans e.symm)) := by
  ext x
  simp only [LinearEquiv.trans_apply, LinearEquiv.mul_apply, LinearEquiv.apply_symm_apply]

private def p9uONrm_conjHom {K : Type*} [Field K] {V W : Type*} [AddCommGroup V]
    [Module K V] [AddCommGroup W] [Module K W] (e : V ≃ₗ[K] W) :
    (W ≃ₗ[K] W) →* (V ≃ₗ[K] V) where
  toFun g := e.trans (g.trans e.symm)
  map_one' := by
    ext x
    simp only [LinearEquiv.trans_apply, LinearEquiv.coe_one, id, LinearEquiv.symm_apply_apply]
  map_mul' f g := p9uONrm_trans_conj_mul e f g

private theorem p9uONrm_commSpace_conj {K : Type*} [Field K] {V W : Type*}
    [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W] (e : V ≃ₗ[K] W)
    (g : W ≃ₗ[K] W) :
    commSpace (e.trans (g.trans e.symm)) = (commSpace g).map (e.symm : W →ₗ[K] V) := by
  ext x
  rw [mem_commSpace, Submodule.mem_map]
  constructor
  · rintro ⟨v, rfl⟩
    refine ⟨g (e v) - e v, sub_mem_commSpace g _, ?_⟩
    simp only [map_sub, LinearEquiv.trans_apply, LinearEquiv.coe_coe,
      LinearEquiv.apply_symm_apply, LinearEquiv.symm_apply_apply]
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨w, rfl⟩ := mem_commSpace.mp hy
    refine ⟨e.symm w, ?_⟩
    simp only [map_sub, LinearEquiv.trans_apply, LinearEquiv.coe_coe,
      LinearEquiv.symm_apply_apply, LinearEquiv.apply_symm_apply]

private theorem p9uONrm_commSpace_conj_symm {K : Type*} [Field K] {V W : Type*}
    [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W] (e : V ≃ₗ[K] W)
    (g : W ≃ₗ[K] W) :
    commSpace g = (commSpace (e.trans (g.trans e.symm))).map (e : V →ₗ[K] W) := by
  ext x
  rw [mem_commSpace, Submodule.mem_map]
  constructor
  · rintro ⟨w, rfl⟩
    refine ⟨(e.trans (g.trans e.symm)) (e.symm w) - e.symm w, sub_mem_commSpace _ _, ?_⟩
    simp only [map_sub, LinearEquiv.trans_apply, LinearEquiv.coe_coe,
      LinearEquiv.apply_symm_apply, LinearEquiv.symm_apply_apply]
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨v, rfl⟩ := mem_commSpace.mp hy
    refine ⟨e v, ?_⟩
    rw [LinearEquiv.coe_coe]
    rw [map_sub, LinearEquiv.trans_apply, LinearEquiv.trans_apply,
      LinearEquiv.apply_symm_apply]

private theorem p9uONrm_polar_comp {K : Type*} [Field K] {V W : Type*}
    [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W] (Q : QuadraticForm K W)
    (e : V ≃ₗ[K] W) (x y : V) :
    polarBilin (Q.comp (e : V →ₗ[K] W)) x y = polarBilin Q (e x) (e y) := by
  rw [QuadraticMap.polarBilin_comp]
  rfl

theorem qtwoDL1_oChart_nondeg (Φ : OrthTorus.OrthFrameCore p Bs L)
    [Algebra Φ.F (GaloisField 2 2)] (C : QTwoDL1ONormChart Φ) :
    (polarBilin Φ.Q).Nondegenerate := by
  have hQ : Φ.Q = (Qn C.E Φ.r).comp (C.χ : Φ.V →ₗ[Φ.F] (Fin Φ.r → GaloisField 2 2)) := by
    ext v
    exact (C.isometry v).symm
  have hQn := Qn_polarBilin_nondegenerate C.E Φ.r
  have hpolar : ∀ x y, polarBilin Φ.Q x y = polarBilin (Qn C.E Φ.r) (C.χ x) (C.χ y) := by
    intro x y
    rw [hQ]
    exact p9uONrm_polar_comp (Qn C.E Φ.r) C.χ x y
  refine ⟨?_, ?_⟩
  · intro x hx
    apply C.χ.injective
    rw [map_zero]
    apply hQn.1
    intro y
    obtain ⟨z, rfl⟩ := C.χ.surjective y
    rw [← hpolar x z]
    exact hx z
  · intro y hy
    apply C.χ.injective
    rw [map_zero]
    apply hQn.2
    intro x
    obtain ⟨z, rfl⟩ := C.χ.surjective x
    rw [← hpolar z y]
    exact hy z

theorem qtwoDL1_oChart_finrank (Φ : OrthTorus.OrthFrameCore p Bs L)
    [Algebra Φ.F (GaloisField 2 2)] (C : QTwoDL1ONormChart Φ) :
    finrank Φ.F Φ.V = 2 * Φ.r := by
  rw [C.χ.finrank_eq, Module.finrank_pi_fintype]
  simp [C.E.finrank_eq, Nat.mul_comm]

theorem qtwoDL1_oChart_witness (Φ : OrthTorus.OrthFrameCore p Bs L)
    [Algebra Φ.F (GaloisField 2 2)] (C : QTwoDL1ONormChart Φ) :
    ∃ s ∈ TauCeti.QuadraticMap.orthogonalGroup Φ.Q,
      s ∉ omegaGroup Φ.Q (qtwoDL1_oChart_nondeg Φ C) := by
  have hr : 0 < Φ.r := by have := Φ.hr; omega
  let i₀ : Fin Φ.r := ⟨0, hr⟩
  let s : Φ.V ≃ₗ[Φ.F] Φ.V := C.χ.trans ((tauAt C.E i₀).trans C.χ.symm)
  have hsO : s ∈ TauCeti.QuadraticMap.orthogonalGroup Φ.Q := by
    refine TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mpr fun v => ?_
    simp only [s, LinearEquiv.trans_apply]
    rw [← C.isometry (C.χ.symm (tauAt C.E i₀ (C.χ v))), ← C.isometry v,
      LinearEquiv.apply_symm_apply]
    exact TauCeti.QuadraticMap.map_app_of_mem_orthogonalGroup
      (tauAt_mem_orthogonalGroup C.E i₀) (C.χ v)
  refine ⟨s, hsO, ?_⟩
  intro hsΩ
  rw [mem_omegaGroup] at hsΩ
  have hfin : finrank Φ.F (commSpace s) = 1 := by
    have hconj : commSpace s = (commSpace (tauAt C.E i₀)).map
        (C.χ.symm : (Fin Φ.r → GaloisField 2 2) →ₗ[Φ.F] Φ.V) := by
      rw [show s = C.χ.trans ((tauAt C.E i₀).trans C.χ.symm) from rfl]
      exact p9uONrm_commSpace_conj C.χ (tauAt C.E i₀)
    rw [hconj, LinearEquiv.finrank_map_eq]
    haveI : Invertible (Qn C.E Φ.r (Pi.single i₀ 1)) :=
      invertibleOfNonzero (by rw [Qn_single_one C.E i₀]; exact one_ne_zero)
    have hrefl : tauAt C.E i₀ =
        TauCeti.QuadraticMap.reflection (Qn C.E Φ.r) (Pi.single i₀ 1) := by
      rw [tauAt_eq_reflect C.E i₀, CFSG.ClassicalGroups.Orthogonal.reflect_eq_reflection]
    rw [hrefl]
    exact finrank_commSpace_reflection (Qn_polarBilin_nondegenerate C.E Φ.r) (Pi.single i₀ 1)
  rw [hfin] at hsΩ
  exact Nat.not_even_one hsΩ.2

theorem qtwoDL1_oChart_block (Φ : OrthTorus.OrthFrameCore p Bs L) [Fact p.Prime]
    (hF : Nat.card Φ.F = 2) [Algebra Φ.F (GaloisField 2 2)] (C : QTwoDL1ONormChart Φ)
    {i j k : Fin Φ.r} (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) {g : Φ.V ≃ₗ[Φ.F] Φ.V}
    (hgO : g ∈ TauCeti.QuadraticMap.orthogonalGroup Φ.Q)
    (hgc : ∀ f : Fin Φ.r → Multiplicative (ZMod p), f i = f j → f j = f k →
      g * Φ.Δ.τ f = Φ.Δ.τ f * g)
    (h2 : ∃ m : ℕ, g ^ (2 ^ m) = 1) :
    (∃ s ∈ coordBlockSU (GaloisField 2 2) 2 1 ({i, j, k} : Finset (Fin Φ.r)),
      ∀ v, C.χ (g v) = suEndN (F := Φ.F) (unitaryInvolution (GaloisField 2 2) 2 1) Φ.r s
        (C.χ v)) ∧
    g ∈ omegaGroup Φ.Q (qtwoDL1_oChart_nondeg Φ C) := by
  have hp3 : p = 3 := by
    have h : p ∣ 3 := by simpa [hF] using Φ.hpq
    exact (Nat.prime_dvd_prime_iff_eq (Fact.out : p.Prime) Nat.prime_three).mp h
  subst p
  let σ := unitaryInvolution (GaloisField 2 2) 2 1
  let g' : (Fin Φ.r → GaloisField 2 2) ≃ₗ[Φ.F] (Fin Φ.r → GaloisField 2 2) :=
    C.χ.symm.trans (g.trans C.χ)
  have hgO' : g' ∈ TauCeti.QuadraticMap.orthogonalGroup (Qn C.E Φ.r) := by
    refine TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mpr fun x => ?_
    simp only [g', LinearEquiv.trans_apply]
    rw [C.isometry (g (C.χ.symm x)),
      TauCeti.QuadraticMap.map_app_of_mem_orthogonalGroup hgO (C.χ.symm x),
      ← C.isometry (C.χ.symm x), LinearEquiv.apply_symm_apply]
  have hdiag : ∀ f : Fin Φ.r → ZMod 3,
      diagHom Φ.F σ Φ.r (fun l => C.ζ ^ (f l).val) =
        C.χ.symm.trans ((Φ.Δ.τ (fun l => Multiplicative.ofAdd (f l))).trans C.χ) := by
    intro f
    apply LinearEquiv.ext
    intro v
    rw [LinearEquiv.trans_apply, LinearEquiv.trans_apply]
    have ht := C.torus (fun l => Multiplicative.ofAdd (f l)) (C.χ.symm v)
    rw [LinearEquiv.apply_symm_apply] at ht
    exact ht.symm
  have hgc' : ∀ f : Fin Φ.r → ZMod 3, f i = f j → f j = f k →
      g' * diagHom Φ.F σ Φ.r (fun l => C.ζ ^ (f l).val) =
        diagHom Φ.F σ Φ.r (fun l => C.ζ ^ (f l).val) * g' := by
    intro f hfi hfj
    have hcomm := hgc (fun l => Multiplicative.ofAdd (f l)) hfi hfj
    have hconj := congrArg (p9uONrm_conjHom C.χ.symm) hcomm
    rw [map_mul, map_mul] at hconj
    have hg : (p9uONrm_conjHom C.χ.symm) g = g' := rfl
    have hτ : (p9uONrm_conjHom C.χ.symm) (Φ.Δ.τ (fun l => Multiplicative.ofAdd (f l))) =
        diagHom Φ.F σ Φ.r (fun l => C.ζ ^ (f l).val) := (hdiag f).symm
    rw [hg, hτ] at hconj
    exact hconj
  have h2' : ∃ m : ℕ, g' ^ (2 ^ m) = 1 := by
    obtain ⟨m, hm⟩ := h2
    refine ⟨m, ?_⟩
    rw [show g' = C.χ.symm.trans (g.trans C.χ) from rfl]
    exact (map_pow (p9uONrm_conjHom C.χ.symm) g (2 ^ m)).symm.trans (by rw [hm, map_one])
  obtain ⟨s, hs, hs_eq⟩ := qtwoDL1_orthBlock (F := Φ.F) (K := GaloisField 2 2)
    (by rw [GaloisField.card (p := 2) (n := 2) (by norm_num)]; norm_num) C.E hij hjk hik
    C.ζ_ne_one C.ζ_pow hgO' hgc' h2'
  refine ⟨⟨s, hs, ?_⟩, ?_⟩
  · intro v
    rw [hs_eq]
    simp only [g', LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply]
  · rw [mem_omegaGroup]
    refine ⟨hgO, ?_⟩
    haveI : FiniteDimensional Φ.F (GaloisField 2 2) :=
      FiniteDimensional.of_finrank_pos (by rw [C.E.finrank_eq]; norm_num)
    have hKlin : ∀ (a : GaloisField 2 2) (x : Fin Φ.r → GaloisField 2 2),
        g' (a • x) = a • g' x := by
      intro a x
      rw [← hs_eq, suEndN_apply, suEndN_apply, CFSG.ClassicalGroups.Unitary.smul_def,
        CFSG.ClassicalGroups.Unitary.smul_def, Matrix.mulVec_smul]
    have hg'Ω := qtwoDL1_mem_omegaGroup_of_isKLinear C.E hgO' hKlin
    rw [mem_omegaGroup] at hg'Ω
    have hconj : commSpace g = (commSpace g').map
        (C.χ.symm : (Fin Φ.r → GaloisField 2 2) →ₗ[Φ.F] Φ.V) := by
      rw [show g' = C.χ.symm.trans (g.trans C.χ) from rfl]
      exact p9uONrm_commSpace_conj_symm C.χ.symm g
    rw [hconj, LinearEquiv.finrank_map_eq]
    exact hg'Ω.2

end CFSG.StandardType.QTwo

end

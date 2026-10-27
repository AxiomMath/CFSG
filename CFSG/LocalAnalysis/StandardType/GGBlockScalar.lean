module

public import CFSG.LocalAnalysis.StandardType.GGTPNThmRACore
public import CFSG.LocalAnalysis.StandardType.GGTPNThmRAC1
public import CFSG.LocalAnalysis.StandardType.GGTPNThmRADescent
public import CFSG.RankThree.PartOne.KC.PrimaryDecomposition
public import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.LinearBlocks
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHigherLinearAction

public section

namespace CFSG.StandardType

open Polynomial Matrix CFSG.Assembly CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.RankThree.PartOne.KCPrimary CFSG.RankThree.CALinearPrimary
open CFSG.HardMathSupport.Solomon.Coordinator CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple

open scoped Classical in
private noncomputable def bsc_mu {K : Type*} [Field K] (ε : K) (h : K[X]) : K[X] :=
  if h = X - 1 then C ε else X

private noncomputable def bsc_tauPoly {K : Type*} [Field K] (ε : K)
    {V : Type*} [AddCommGroup V] [Module K V] (x : Module.End K V) (h : K[X]) : K[X] :=
  1 + (bsc_mu ε h - 1) * primaryIdempotent x h

private noncomputable def bsc_tau {K : Type*} [Field K] (ε : K)
    {V : Type*} [AddCommGroup V] [Module K V] (x : Module.End K V) (h : K[X]) :
    Module.End K V :=
  aeval x (bsc_tauPoly ε x h)

private theorem bsc_tau_eq {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]
    (ε : K) (x : Module.End K V) (h : K[X]) :
    bsc_tau ε x h = 1 + (aeval x (bsc_mu ε h) - 1) * primaryProjection x h := by
  simp only [bsc_tau, bsc_tauPoly, primaryProjection, map_one, map_add, map_mul, map_sub]

private theorem bsc_tau_commute {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]
    (ε : K) (x : Module.End K V) (h h' : K[X]) :
    Commute (bsc_tau ε x h) (bsc_tau ε x h') := by
  show bsc_tau ε x h * bsc_tau ε x h' = bsc_tau ε x h' * bsc_tau ε x h
  simp only [bsc_tau, ← map_mul]
  rw [mul_comm (bsc_tauPoly ε x h') (bsc_tauPoly ε x h)]

private theorem bsc_aeval_mem_primaryComponent {K : Type*} [Field K] {V : Type*}
    [AddCommGroup V] [Module K V] (x : Module.End K V) (f : K[X]) {h : K[X]} {v : V}
    (hv : v ∈ primaryComponent x h) :
    aeval x f v ∈ primaryComponent x h :=
  apply_mem_primaryComponent (commute_aeval (Commute.refl x) f).symm hv

private theorem bsc_tau_apply_of_mem {K : Type*} [Field K] {V : Type*} [AddCommGroup V]
    [Module K V] [FiniteDimensional K V] {x : Module.End K V} (hsq : Squarefree (minpoly K x))
    (ε : K) {h : K[X]} (hh : h ∈ primaryFactors x) {v : V}
    (hv : v ∈ primaryComponent x h) :
    bsc_tau ε x h v = aeval x (bsc_mu ε h) v := by
  rw [bsc_tau_eq]
  have hproj : primaryProjection x h v = v := primaryProjection_of_mem hsq hh hv
  simp only [LinearMap.add_apply, Module.End.mul_apply, hproj, LinearMap.sub_apply,
    Module.End.one_apply]
  abel

private theorem bsc_tau_apply_of_mem_ne {K : Type*} [Field K] {V : Type*} [AddCommGroup V]
    [Module K V] [FiniteDimensional K V] {x : Module.End K V} (hsq : Squarefree (minpoly K x))
    (ε : K) {h b : K[X]} (hh : h ∈ primaryFactors x) (hb : b ∈ primaryFactors x)
    (hbh : b ≠ h) {v : V} (hv : v ∈ primaryComponent x b) :
    bsc_tau ε x h v = v := by
  rw [bsc_tau_eq]
  have hproj : primaryProjection x h v = 0 :=
    primaryProjection_of_mem_ne hsq hh hb hbh hv
  simp only [LinearMap.add_apply, Module.End.mul_apply, hproj, LinearMap.sub_apply,
    Module.End.one_apply]
  simp

private theorem bsc_tau_pow_apply_of_mem {K : Type*} [Field K] {V : Type*} [AddCommGroup V]
    [Module K V] [FiniteDimensional K V] {x : Module.End K V} (hsq : Squarefree (minpoly K x))
    (ε : K) {h : K[X]} (hh : h ∈ primaryFactors x) (v : V)
    (hv : v ∈ primaryComponent x h) (n : ℕ) :
    ((bsc_tau ε x h) ^ n) v = aeval x (bsc_mu ε h ^ n) v := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', Module.End.mul_apply, ih]
    rw [bsc_tau_apply_of_mem hsq ε hh
      (bsc_aeval_mem_primaryComponent x (bsc_mu ε h ^ n) hv)]
    rw [← Module.End.mul_apply, ← map_mul, ← pow_succ']

private theorem bsc_tau_pow_apply_of_mem_ne {K : Type*} [Field K] {V : Type*}
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] {x : Module.End K V}
    (hsq : Squarefree (minpoly K x)) (ε : K) {h b : K[X]} (hh : h ∈ primaryFactors x)
    (hb : b ∈ primaryFactors x) (hbh : b ≠ h) {v : V} (hv : v ∈ primaryComponent x b) (n : ℕ) :
    ((bsc_tau ε x h) ^ n) v = v := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', Module.End.mul_apply, ih]
    exact bsc_tau_apply_of_mem_ne hsq ε hh hb hbh hv

private theorem bsc_tau_pow_mem_component {K : Type*} [Field K] {V : Type*} [AddCommGroup V]
    [Module K V] (ε : K) (x : Module.End K V) {f h : K[X]} (n : ℕ) {v : V}
    (hv : v ∈ primaryComponent x h) :
    ((bsc_tau ε x f) ^ n) v ∈ primaryComponent x h := by
  induction n with
  | zero => simpa using hv
  | succ n ih =>
    rw [pow_succ', Module.End.mul_apply]
    exact bsc_aeval_mem_primaryComponent x (bsc_tauPoly ε x f) ih

private theorem bsc_tau_pow_p_eq_one {K : Type*} [Field K] {V : Type*} [AddCommGroup V]
    [Module K V] [FiniteDimensional K V] {x : Module.End K V} (hsq : Squarefree (minpoly K x))
    (ε : K) {p : ℕ} {h : K[X]} (hh : h ∈ primaryFactors x)
    (hmu : h ∣ bsc_mu ε h ^ p - 1) :
    (bsc_tau ε x h) ^ p = 1 := by
  refine ext_primaryComponent hsq (fun b hb v hv => ?_)
  change ((bsc_tau ε x h) ^ p) v = v
  by_cases hbh : b = h
  · subst hbh
    rw [bsc_tau_pow_apply_of_mem hsq ε hh v hv p]
    obtain ⟨q, hq⟩ := hmu
    have h1 : bsc_mu ε b ^ p = 1 + b * q := by rw [← hq]; ring
    rw [h1, map_add, map_mul]
    simp only [map_one, LinearMap.add_apply, Module.End.one_apply, Module.End.mul_apply]
    rw [mem_primaryComponent.mp (bsc_aeval_mem_primaryComponent x q hv)]
    simp
  · exact bsc_tau_pow_apply_of_mem_ne hsq ε hh hb hbh hv p

private noncomputable def bsc_tauUnit {K : Type*} [Field K] {V : Type*} [AddCommGroup V]
    [Module K V] [FiniteDimensional K V] {p : ℕ} (hp : p.Prime) (ε : K)
    {x : Module.End K V} (hsq : Squarefree (minpoly K x)) {h : K[X]}
    (hh : h ∈ primaryFactors x) (hmu : h ∣ bsc_mu ε h ^ p - 1) :
    (Module.End K V)ˣ :=
  ⟨bsc_tau ε x h, (bsc_tau ε x h) ^ (p - 1), by
      show (bsc_tau ε x h) ^ 1 * (bsc_tau ε x h) ^ (p - 1) = 1
      rw [← pow_add, show 1 + (p - 1) = p by
          rw [Nat.add_comm]; exact Nat.succ_pred_eq_of_pos hp.pos,
        bsc_tau_pow_p_eq_one hsq ε hh hmu], by
      show (bsc_tau ε x h) ^ (p - 1) * (bsc_tau ε x h) ^ 1 = 1
      rw [← pow_add, show (p - 1) + 1 = p by exact Nat.succ_pred_eq_of_pos hp.pos,
        bsc_tau_pow_p_eq_one hsq ε hh hmu]⟩

@[simp] private theorem bsc_coe_tauUnit {K : Type*} [Field K] {V : Type*} [AddCommGroup V]
    [Module K V] [FiniteDimensional K V] {p : ℕ} (hp : p.Prime) (ε : K)
    {x : Module.End K V} (hsq : Squarefree (minpoly K x)) {h : K[X]}
    (hh : h ∈ primaryFactors x) (hmu : h ∣ bsc_mu ε h ^ p - 1) :
    ((bsc_tauUnit hp ε hsq hh hmu : (Module.End K V)ˣ) : Module.End K V) =
      bsc_tau ε x h := rfl

private theorem bsc_tauUnit_commute {K : Type*} [Field K] {V : Type*} [AddCommGroup V]
    [Module K V] [FiniteDimensional K V] {p : ℕ} (hp : p.Prime) (ε : K)
    {x : Module.End K V} (hsq : Squarefree (minpoly K x)) {h h' : K[X]}
    (hh : h ∈ primaryFactors x) (hh' : h' ∈ primaryFactors x)
    (hmu : h ∣ bsc_mu ε h ^ p - 1) (hmu' : h' ∣ bsc_mu ε h' ^ p - 1) :
    Commute (bsc_tauUnit hp ε hsq hh hmu) (bsc_tauUnit hp ε hsq hh' hmu') := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mul]
  exact (bsc_tau_commute ε x h h').eq

private theorem bsc_eps_pow_eq_one {K : Type*} [Field K] {p : ℕ} {ε : K}
    (hdvd : X - C ε ∣ (X ^ p - 1 : K[X])) : ε ^ p = 1 := by
  have hroot : (X ^ p - 1 : K[X]).IsRoot ε := (dvd_iff_isRoot).mp hdvd
  have h := hroot.eq_zero
  simp only [eval_sub, eval_pow, eval_X, eval_one] at h
  exact sub_eq_zero.mp h

private theorem bsc_good_dvd {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] {p : ℕ} {x : Module.End K V} {ε : K}
    (hxp : x ^ p = 1) (hgood : (X - C ε) ∈ primaryFactors x) :
    X - C ε ∣ (X ^ p - 1 : K[X]) := by
  refine dvd_trans (mem_primaryFactors.mp hgood).2.2 ?_
  exact minpoly.dvd K x (by simp [hxp])

private theorem bsc_mu_pow_sub_one_dvd {K : Type*} [Field K] {V : Type*} [AddCommGroup V]
    [Module K V] [FiniteDimensional K V] {p : ℕ} {x : Module.End K V} {ε : K}
    (hxp : x ^ p = 1) (hgood : (X - C ε) ∈ primaryFactors x)
    {h : K[X]} (hh : h ∈ primaryFactors x) (hne : h ≠ X - C ε) :
    h ∣ bsc_mu ε h ^ p - 1 := by
  have heps : ε ^ p = 1 := bsc_eps_pow_eq_one (bsc_good_dvd hxp hgood)
  by_cases h1 : h = X - 1
  · subst h1
    rw [bsc_mu, if_pos rfl]
    have hzero : (C ε : K[X]) ^ p - 1 = 0 := by
      rw [← C_pow, heps, C_1, sub_self]
    rw [hzero]
    exact dvd_zero _
  · rw [bsc_mu, if_neg h1]
    exact dvd_trans (mem_primaryFactors.mp hh).2.2
      (minpoly.dvd K x (by simp [hxp]))

private theorem bsc_mu_sub_one_not_dvd {K : Type*} [Field K] {V : Type*} [AddCommGroup V]
    [Module K V] [FiniteDimensional K V] {x : Module.End K V} {ε : K} {h : K[X]}
    (hh : h ∈ primaryFactors x) (hne : h ≠ X - C ε) :
    ¬ h ∣ bsc_mu ε h - 1 := by
  intro hdvd
  by_cases h1 : h = X - 1
  · subst h1
    rw [bsc_mu, if_pos rfl] at hdvd
    have hroot : (C ε - 1 : K[X]).IsRoot 1 := (dvd_iff_isRoot).mp hdvd
    have h := hroot.eq_zero
    simp only [eval_sub, eval_C, eval_one] at h
    have heps1 : ε = 1 := sub_eq_zero.mp h
    exact hne (by rw [heps1, C_1])
  · rw [bsc_mu, if_neg h1] at hdvd
    have hassoc : Associated h (X - 1) :=
      (irreducible_of_mem_primaryFactors hh).associated_of_dvd (irreducible_X_sub_C 1) hdvd
    exact h1 (eq_of_monic_of_associated (monic_of_mem_primaryFactors hh) (monic_X_sub_C 1) hassoc)

private theorem bsc_mk_pow_eq_one {K : Type*} [Field K] {h : K[X]} (f : K[X]) {n : ℕ}
    (hdiv : h ∣ f ^ n - 1) :
    (AdjoinRoot.mk h f) ^ n = 1 := by
  rw [← map_pow, ← map_one (AdjoinRoot.mk h), ← sub_eq_zero, ← map_sub]
  exact AdjoinRoot.mk_eq_zero.mpr hdiv

private theorem bsc_mk_eq_of_aeval_eq {K : Type*} [Field K] {V : Type*} [AddCommGroup V]
    [Module K V] [FiniteDimensional K V] {x : Module.End K V} {h : K[X]}
    (hh : h ∈ primaryFactors x) {f g : K[X]} {v : V}
    (hv : v ∈ primaryComponent x h) (hv0 : v ≠ 0)
    (hact : aeval x f v = aeval x g v) :
    AdjoinRoot.mk h f = AdjoinRoot.mk h g := by
  haveI : Fact (Irreducible h) := ⟨irreducible_of_mem_primaryFactors hh⟩
  have hscalar : (AdjoinRoot.mk h f) • (⟨v, hv⟩ : primaryComponent x h) =
      (AdjoinRoot.mk h g) • (⟨v, hv⟩ : primaryComponent x h) := by
    apply Subtype.ext
    rw [coe_mk_smul_primaryComponent, coe_mk_smul_primaryComponent]
    exact hact
  have h0 : (AdjoinRoot.mk h f - AdjoinRoot.mk h g) •
      (⟨v, hv⟩ : primaryComponent x h) = 0 := by
    rw [sub_smul, hscalar, sub_self]
  have hc0 : AdjoinRoot.mk h f - AdjoinRoot.mk h g = 0 := by
    by_contra hc
    have hsingle : (⟨v, hv⟩ : primaryComponent x h) = 0 := by
      have h1 : (⟨v, hv⟩ : primaryComponent x h) =
          (AdjoinRoot.mk h f - AdjoinRoot.mk h g)⁻¹ •
            ((AdjoinRoot.mk h f - AdjoinRoot.mk h g) • ⟨v, hv⟩) := by
        rw [← mul_smul, inv_mul_cancel₀ hc, one_smul]
      rw [h1, h0, smul_zero]
    exact hv0 (Subtype.ext_iff.mp hsingle)
  exact sub_eq_zero.mp hc0

private theorem bsc_modEq_of_apply {K : Type*} [Field K] {V : Type*} [AddCommGroup V]
    [Module K V] [FiniteDimensional K V] {p : ℕ} (hp : p.Prime) {x : Module.End K V}
    (hsq : Squarefree (minpoly K x)) {ε : K} {h : K[X]} (hh : h ∈ primaryFactors x)
    (hne : h ≠ X - C ε) (hmu_p : h ∣ bsc_mu ε h ^ p - 1) {m n : ℕ} {v : V}
    (hv : v ∈ primaryComponent x h) (hv0 : v ≠ 0)
    (heq : ((bsc_tau ε x h) ^ m) v = ((bsc_tau ε x h) ^ n) v) :
    m % p = n % p := by
  haveI : Fact (Irreducible h) := ⟨irreducible_of_mem_primaryFactors hh⟩
  have hact : aeval x (bsc_mu ε h ^ m) v = aeval x (bsc_mu ε h ^ n) v := by
    rw [← bsc_tau_pow_apply_of_mem hsq ε hh v hv m,
      ← bsc_tau_pow_apply_of_mem hsq ε hh v hv n]
    exact heq
  have hc : AdjoinRoot.mk h (bsc_mu ε h ^ m) = AdjoinRoot.mk h (bsc_mu ε h ^ n) :=
    bsc_mk_eq_of_aeval_eq hh hv hv0 hact
  have hcm : (AdjoinRoot.mk h (bsc_mu ε h)) ^ m = (AdjoinRoot.mk h (bsc_mu ε h)) ^ n := by
    simpa only [← map_pow] using hc
  have hnot : ¬ h ∣ bsc_mu ε h - 1 := bsc_mu_sub_one_not_dvd hh hne
  have hne1 : AdjoinRoot.mk h (bsc_mu ε h) ≠ 1 := by
    intro h1
    apply hnot
    have : AdjoinRoot.mk h (bsc_mu ε h - 1) = 0 := by
      rw [map_sub, h1, map_one, sub_self]
    exact AdjoinRoot.mk_eq_zero.mp this
  have hc0 : AdjoinRoot.mk h (bsc_mu ε h) ≠ 0 := by
    intro hz
    have hp' := bsc_mk_pow_eq_one (bsc_mu ε h) hmu_p
    rw [hz, zero_pow hp.pos.ne'] at hp'
    exact one_ne_zero hp'.symm
  let cu : (AdjoinRoot h)ˣ := Units.mk0 (AdjoinRoot.mk h (bsc_mu ε h)) hc0
  have hcu : cu ^ m = cu ^ n := by
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val, Units.val_mk0]
    exact hcm
  have hcu_p : cu ^ p = 1 := by
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, Units.val_mk0, Units.val_one]
    exact bsc_mk_pow_eq_one _ hmu_p
  have hcu_ne1 : cu ≠ 1 := by
    intro h1
    apply hne1
    have := congrArg (fun u : (AdjoinRoot h)ˣ => (u : AdjoinRoot h)) h1
    rwa [Units.val_mk0, Units.val_one] at this
  have hord : orderOf cu = p := by
    rcases hp.eq_one_or_self_of_dvd _ (orderOf_dvd_of_pow_eq_one hcu_p) with h1 | hp'
    · exact absurd (orderOf_eq_one_iff.mp h1) hcu_ne1
    · exact hp'
  have hmod := pow_eq_pow_iff_modEq.mp hcu
  rwa [hord] at hmod

private theorem bsc_indep_modEq {K : Type*} [Field K] {V : Type*} [AddCommGroup V]
    [Module K V] [FiniteDimensional K V] {p : ℕ} (hp : p.Prime) {x : Module.End K V}
    (hsq : Squarefree (minpoly K x)) {ε : K} {h0 h1 h2 : K[X]}
    (hh0 : h0 ∈ primaryFactors x) (hh1 : h1 ∈ primaryFactors x) (hh2 : h2 ∈ primaryFactors x)
    (hne0 : h0 ≠ X - C ε) (hne1 : h1 ≠ X - C ε) (hne2 : h2 ≠ X - C ε)
    (h01 : h0 ≠ h1) (h02 : h0 ≠ h2) (h12 : h1 ≠ h2)
    (hmu0 : h0 ∣ bsc_mu ε h0 ^ p - 1) (hmu1 : h1 ∣ bsc_mu ε h1 ^ p - 1)
    (hmu2 : h2 ∣ bsc_mu ε h2 ^ p - 1)
    {e0 e1 e2 f0 f1 f2 : ℕ}
    (he : (bsc_tau ε x h0) ^ e0 * (bsc_tau ε x h1) ^ e1 * (bsc_tau ε x h2) ^ e2 =
      (bsc_tau ε x h0) ^ f0 * (bsc_tau ε x h1) ^ f1 * (bsc_tau ε x h2) ^ f2) :
    e0 % p = f0 % p ∧ e1 % p = f1 % p ∧ e2 % p = f2 % p := by
  have hm0 : e0 % p = f0 % p := by
    obtain ⟨v, hv, hv0⟩ :=
      Submodule.exists_mem_ne_zero_of_ne_bot (primaryComponent_ne_bot hsq hh0)
    have h1v : ((bsc_tau ε x h1) ^ e1) v = v :=
      bsc_tau_pow_apply_of_mem_ne hsq ε hh1 hh0 h01 hv e1
    have h2v : ((bsc_tau ε x h2) ^ e2) v = v :=
      bsc_tau_pow_apply_of_mem_ne hsq ε hh2 hh0 h02 hv e2
    have h1v' : ((bsc_tau ε x h1) ^ f1) v = v :=
      bsc_tau_pow_apply_of_mem_ne hsq ε hh1 hh0 h01 hv f1
    have h2v' : ((bsc_tau ε x h2) ^ f2) v = v :=
      bsc_tau_pow_apply_of_mem_ne hsq ε hh2 hh0 h02 hv f2
    have hv_eq := congrArg (fun T : Module.End K V => T v) he
    simp only [Module.End.mul_apply, h1v, h2v, h1v', h2v'] at hv_eq
    exact bsc_modEq_of_apply hp hsq hh0 hne0 hmu0 hv hv0 hv_eq
  have hm1 : e1 % p = f1 % p := by
    obtain ⟨v, hv, hv0⟩ :=
      Submodule.exists_mem_ne_zero_of_ne_bot (primaryComponent_ne_bot hsq hh1)
    have h2e : ((bsc_tau ε x h2) ^ e2) v = v :=
      bsc_tau_pow_apply_of_mem_ne hsq ε hh2 hh1 h12 hv e2
    have h2f : ((bsc_tau ε x h2) ^ f2) v = v :=
      bsc_tau_pow_apply_of_mem_ne hsq ε hh2 hh1 h12 hv f2
    have h0e : ((bsc_tau ε x h0) ^ e0) (((bsc_tau ε x h1) ^ e1) v) =
        ((bsc_tau ε x h1) ^ e1) v :=
      bsc_tau_pow_apply_of_mem_ne hsq ε hh0 hh1 h01.symm
        (bsc_tau_pow_mem_component ε x e1 hv) e0
    have h0f : ((bsc_tau ε x h0) ^ f0) (((bsc_tau ε x h1) ^ f1) v) =
        ((bsc_tau ε x h1) ^ f1) v :=
      bsc_tau_pow_apply_of_mem_ne hsq ε hh0 hh1 h01.symm
        (bsc_tau_pow_mem_component ε x f1 hv) f0
    have hlhs : (((bsc_tau ε x h0) ^ e0 * (bsc_tau ε x h1) ^ e1) *
        (bsc_tau ε x h2) ^ e2) v = ((bsc_tau ε x h1) ^ e1) v := by
      rw [Module.End.mul_apply, Module.End.mul_apply, h2e]
      exact h0e
    have hrhs : (((bsc_tau ε x h0) ^ f0 * (bsc_tau ε x h1) ^ f1) *
        (bsc_tau ε x h2) ^ f2) v = ((bsc_tau ε x h1) ^ f1) v := by
      rw [Module.End.mul_apply, Module.End.mul_apply, h2f]
      exact h0f
    have hv_eq : ((bsc_tau ε x h1) ^ e1) v = ((bsc_tau ε x h1) ^ f1) v := by
      rw [← hlhs, ← hrhs]
      exact congrArg (fun T : Module.End K V => T v) he
    exact bsc_modEq_of_apply hp hsq hh1 hne1 hmu1 hv hv0 hv_eq
  have hm2 : e2 % p = f2 % p := by
    obtain ⟨v, hv, hv0⟩ :=
      Submodule.exists_mem_ne_zero_of_ne_bot (primaryComponent_ne_bot hsq hh2)
    have h1e : ((bsc_tau ε x h1) ^ e1) (((bsc_tau ε x h2) ^ e2) v) =
        ((bsc_tau ε x h2) ^ e2) v :=
      bsc_tau_pow_apply_of_mem_ne hsq ε hh1 hh2 h12.symm
        (bsc_tau_pow_mem_component ε x e2 hv) e1
    have h1f : ((bsc_tau ε x h1) ^ f1) (((bsc_tau ε x h2) ^ f2) v) =
        ((bsc_tau ε x h2) ^ f2) v :=
      bsc_tau_pow_apply_of_mem_ne hsq ε hh1 hh2 h12.symm
        (bsc_tau_pow_mem_component ε x f2 hv) f1
    have h0e : ((bsc_tau ε x h0) ^ e0)
        (((bsc_tau ε x h1) ^ e1) (((bsc_tau ε x h2) ^ e2) v)) =
        ((bsc_tau ε x h1) ^ e1) (((bsc_tau ε x h2) ^ e2) v) :=
      bsc_tau_pow_apply_of_mem_ne hsq ε hh0 hh2 h02.symm
        (bsc_tau_pow_mem_component ε x e1 (bsc_tau_pow_mem_component ε x e2 hv)) e0
    have h0f : ((bsc_tau ε x h0) ^ f0)
        (((bsc_tau ε x h1) ^ f1) (((bsc_tau ε x h2) ^ f2) v)) =
        ((bsc_tau ε x h1) ^ f1) (((bsc_tau ε x h2) ^ f2) v) :=
      bsc_tau_pow_apply_of_mem_ne hsq ε hh0 hh2 h02.symm
        (bsc_tau_pow_mem_component ε x f1 (bsc_tau_pow_mem_component ε x f2 hv)) f0
    have hlhs : (((bsc_tau ε x h0) ^ e0 * (bsc_tau ε x h1) ^ e1) *
        (bsc_tau ε x h2) ^ e2) v = ((bsc_tau ε x h2) ^ e2) v := by
      rw [Module.End.mul_apply, Module.End.mul_apply, h0e, h1e]
    have hrhs : (((bsc_tau ε x h0) ^ f0 * (bsc_tau ε x h1) ^ f1) *
        (bsc_tau ε x h2) ^ f2) v = ((bsc_tau ε x h2) ^ f2) v := by
      rw [Module.End.mul_apply, Module.End.mul_apply, h0f, h1f]
    have hv_eq : ((bsc_tau ε x h2) ^ e2) v = ((bsc_tau ε x h2) ^ f2) v := by
      rw [← hlhs, ← hrhs]
      exact congrArg (fun T : Module.End K V => T v) he
    exact bsc_modEq_of_apply hp hsq hh2 hne2 hmu2 hv hv0 hv_eq
  exact ⟨hm0, hm1, hm2⟩

private theorem bsc_p_ne_zero {K : Type*} [Field K] {N p : ℕ} (hp : p.Prime)
    (g : GL (Fin N) K) (hg : g ^ p = 1)
    (hcard : 4 ≤ (primaryFactors (glA g : Module.End K (Fin N → K))).card) :
    (p : K) ≠ 0 := by
  intro hpk
  haveI : CharP K p := (CharP.charP_iff_prime_eq_zero hp).mpr hpk
  haveI : Fact p.Prime := ⟨hp⟩
  set x : Module.End K (Fin N → K) := (glA g : Module.End K (Fin N → K)) with hx
  have hxp : x ^ p = 1 := by
    rw [hx]
    change (((Matrix.GeneralLinearGroup.toLin g : (Module.End K (Fin N → K))ˣ) :
      Module.End K (Fin N → K))) ^ p = 1
    rw [← Units.val_pow_eq_pow_val, ← map_pow, hg, map_one, Units.val_one]
  have hchar : (X - C 1 : K[X]) ^ p = X ^ p - 1 := by
    haveI : CharP (K[X]) p := Polynomial.charP
    rw [sub_pow_char]
    simp
  have hmin : minpoly K x ∣ (X - 1) ^ p := by
    have h1 : aeval x ((X ^ p - 1 : K[X])) = 0 := by
      rw [map_sub, map_pow, aeval_X, map_one, hxp, sub_self]
    have h2 : minpoly K x ∣ X ^ p - 1 := minpoly.dvd K x h1
    rwa [← hchar] at h2
  have hsub : ∀ h ∈ primaryFactors x, h = X - 1 := by
    intro h hh
    have hdvd : h ∣ (X - 1) ^ p := dvd_trans (mem_primaryFactors.mp hh).2.2 hmin
    have hdvd1 : h ∣ X - 1 :=
      (irreducible_of_mem_primaryFactors hh).prime.dvd_of_dvd_pow hdvd
    exact eq_of_monic_of_associated (monic_of_mem_primaryFactors hh) (monic_X_sub_C 1)
      ((irreducible_of_mem_primaryFactors hh).associated_of_dvd (irreducible_X_sub_C 1) hdvd1)
  have hle : (primaryFactors x).card ≤ 1 := by
    have hsub' : (primaryFactors x) ⊆ ({X - 1} : Finset K[X]) := by
      intro h hh
      simpa using hsub h hh
    calc (primaryFactors x).card ≤ ({X - 1} : Finset K[X]).card := Finset.card_le_card hsub'
      _ = 1 := Finset.card_singleton _
  have hcardx : 4 ≤ (primaryFactors x).card := by rw [hx]; exact hcard
  omega

theorem ggBlockScalarCore_holds :
    ∀ (p N : ℕ), p.Prime → p ≠ 2 → ∀ (K : Type) [Field K] [Finite K] (g : GL (Fin N) K) (ε : K),
      g ^ p = 1 →
      (Polynomial.X - Polynomial.C ε) ∈ primaryFactors (glA g : Module.End K (Fin N → K)) →
      (∀ h ∈ primaryFactors (glA g : Module.End K (Fin N → K)), h ≠ (Polynomial.X - Polynomial.C ε) →
        primaryMultiplicity (glA g : Module.End K (Fin N → K)) h = 1) →
      4 ≤ (primaryFactors (glA g : Module.End K (Fin N → K))).card →
      ∃ U : Subgroup (SpecialLinearGroup (Fin N) K),
        p ^ 2 ≤ Nat.card U ∧
        (∀ τ ∈ U, τ ^ p = 1) ∧
        (∀ τ ∈ U, ∀ B : GL (Fin N) K, B * g * B⁻¹ = g →
          CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation N K B τ = τ) ∧
        (∀ τ ∈ U, ∀ v : Fin N → K,
          v ∈ primaryComponent (glA g : Module.End K (Fin N → K))
              (Polynomial.X - Polynomial.C ε) →
            (glA (τ : GL (Fin N) K) : Module.End K (Fin N → K)) v = v) := by
  intro p N hp hp2 K _instK _finK g ε hg hgood hmult hcard
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  have hpk : (p : K) ≠ 0 := bsc_p_ne_zero hp g hg hcard
  let x : Module.End K (Fin N → K) := (glA g : Module.End K (Fin N → K))
  have hgoodx : (X - C ε) ∈ primaryFactors x := hgood
  have hcardx : 4 ≤ (primaryFactors x).card := hcard
  have hxp : x ^ p = 1 := by
    change (((Matrix.GeneralLinearGroup.toLin g : (Module.End K (Fin N → K))ˣ) :
      Module.End K (Fin N → K))) ^ p = 1
    rw [← Units.val_pow_eq_pow_val, ← map_pow, hg, map_one, Units.val_one]
  have hsq : Squarefree (minpoly K x) := by
    refine squarefree_minpoly_of_aeval_eq_zero (p := (X ^ p - 1 : K[X])) ?_ ?_
    · exact (Polynomial.separable_X_pow_sub_C (1 : K) hpk one_ne_zero).squarefree
    · rw [map_sub, map_pow, aeval_X, map_one, hxp, sub_self]
  have hs_card : 3 ≤ ((primaryFactors x).erase (X - C ε)).card := by
    rw [Finset.card_erase_of_mem hgoodx]
    omega
  obtain ⟨t, ht_sub, ht_card⟩ := Finset.exists_subset_card_eq hs_card
  obtain ⟨h0, h1, h2, h01, h02, h12, ht_eq⟩ := Finset.card_eq_three.mp ht_card
  have h0t : h0 ∈ t := by rw [ht_eq]; simp
  have h1t : h1 ∈ t := by rw [ht_eq]; simp
  have h2t : h2 ∈ t := by rw [ht_eq]; simp
  have h0s : h0 ∈ (primaryFactors x).erase (X - C ε) := ht_sub h0t
  have h1s : h1 ∈ (primaryFactors x).erase (X - C ε) := ht_sub h1t
  have h2s : h2 ∈ (primaryFactors x).erase (X - C ε) := ht_sub h2t
  have h0pf : h0 ∈ primaryFactors x := Finset.mem_of_mem_erase h0s
  have h1pf : h1 ∈ primaryFactors x := Finset.mem_of_mem_erase h1s
  have h2pf : h2 ∈ primaryFactors x := Finset.mem_of_mem_erase h2s
  have h0ne : h0 ≠ X - C ε := Finset.ne_of_mem_erase h0s
  have h1ne : h1 ≠ X - C ε := Finset.ne_of_mem_erase h1s
  have h2ne : h2 ≠ X - C ε := Finset.ne_of_mem_erase h2s
  have hμ0 : h0 ∣ bsc_mu ε h0 ^ p - 1 := bsc_mu_pow_sub_one_dvd hxp hgoodx h0pf h0ne
  have hμ1 : h1 ∣ bsc_mu ε h1 ^ p - 1 := bsc_mu_pow_sub_one_dvd hxp hgoodx h1pf h1ne
  have hμ2 : h2 ∣ bsc_mu ε h2 ^ p - 1 := bsc_mu_pow_sub_one_dvd hxp hgoodx h2pf h2ne
  let τ0 : (Module.End K (Fin N → K))ˣ := bsc_tauUnit hp ε hsq h0pf hμ0
  let τ1 : (Module.End K (Fin N → K))ˣ := bsc_tauUnit hp ε hsq h1pf hμ1
  let τ2 : (Module.End K (Fin N → K))ˣ := bsc_tauUnit hp ε hsq h2pf hμ2
  have hτ0p : (bsc_tau ε x h0) ^ p = 1 := bsc_tau_pow_p_eq_one hsq ε h0pf hμ0
  have hτ1p : (bsc_tau ε x h1) ^ p = 1 := bsc_tau_pow_p_eq_one hsq ε h1pf hμ1
  have hτ2p : (bsc_tau ε x h2) ^ p = 1 := bsc_tau_pow_p_eq_one hsq ε h2pf hμ2
  have hτ0up : τ0 ^ p = 1 := by
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, Units.val_one, show
      ((τ0 : (Module.End K (Fin N → K))ˣ) : Module.End K (Fin N → K)) =
        bsc_tau ε x h0 from rfl, hτ0p]
  have hτ1up : τ1 ^ p = 1 := by
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, Units.val_one, show
      ((τ1 : (Module.End K (Fin N → K))ˣ) : Module.End K (Fin N → K)) =
        bsc_tau ε x h1 from rfl, hτ1p]
  have hτ2up : τ2 ^ p = 1 := by
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, Units.val_one, show
      ((τ2 : (Module.End K (Fin N → K))ˣ) : Module.End K (Fin N → K)) =
        bsc_tau ε x h2 from rfl, hτ2p]
  let G : Subgroup (Module.End K (Fin N → K))ˣ :=
    Subgroup.closure ({τ0, τ1, τ2} : Set (Module.End K (Fin N → K))ˣ)
  have hτ01 : Commute τ0 τ1 := bsc_tauUnit_commute hp ε hsq h0pf h1pf hμ0 hμ1
  have hτ02 : Commute τ0 τ2 := bsc_tauUnit_commute hp ε hsq h0pf h2pf hμ0 hμ2
  have hτ12 : Commute τ1 τ2 := bsc_tauUnit_commute hp ε hsq h1pf h2pf hμ1 hμ2
  have hcommS : ({τ0, τ1, τ2} : Set (Module.End K (Fin N → K))ˣ).Pairwise Commute := by
    intro a ha b hb _
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha hb
    rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl
    · exact Commute.refl _
    · exact hτ01
    · exact hτ02
    · exact hτ01.symm
    · exact Commute.refl _
    · exact hτ12
    · exact hτ02.symm
    · exact hτ12.symm
    · exact Commute.refl _
  letI : CommGroup G := Subgroup.closureCommGroupOfComm hcommS
  have hτ0G : τ0 ∈ G := Subgroup.mem_closure_of_mem (by simp)
  have hτ1G : τ1 ∈ G := Subgroup.mem_closure_of_mem (by simp)
  have hτ2G : τ2 ∈ G := Subgroup.mem_closure_of_mem (by simp)
  have hexp : ∀ y : G, (y : (Module.End K (Fin N → K))ˣ) ^ p = 1 := by
    intro y
    have hy : (⟨(y : (Module.End K (Fin N → K))ˣ), y.2⟩ : G) ^ p = 1 := by
      refine Subgroup.closure_induction (p := fun z _ => (⟨z, by assumption⟩ : G) ^ p = 1)
        ?_ ?_ ?_ ?_ y.2
      · intro z hz
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
        rcases hz with rfl | rfl | rfl
        · apply Subtype.ext
          simpa using hτ0up
        · apply Subtype.ext
          simpa using hτ1up
        · apply Subtype.ext
          simpa using hτ2up
      · apply Subtype.ext
        simp
      · intro u v huG hvG hu hv
        have huv : (⟨u * v, G.mul_mem huG hvG⟩ : G) = (⟨u, huG⟩ : G) * ⟨v, hvG⟩ :=
          Subtype.ext rfl
        rw [huv, mul_pow, hu, hv, mul_one]
      · intro u huG hu
        have huv : (⟨u⁻¹, G.inv_mem huG⟩ : G) = (⟨u, huG⟩ : G)⁻¹ := Subtype.ext rfl
        rw [huv, inv_pow, hu, inv_one]
    simpa using congrArg (fun u : G => (u : (Module.End K (Fin N → K))ˣ)) hy
  let ψ : (Fin 3 → Fin p) → G := fun a =>
    ⟨τ0 ^ (a 0).val * τ1 ^ (a 1).val * τ2 ^ (a 2).val,
      G.mul_mem (G.mul_mem (G.pow_mem hτ0G _) (G.pow_mem hτ1G _)) (G.pow_mem hτ2G _)⟩
  have hψinj : Function.Injective ψ := by
    intro a b hab
    have he : (bsc_tau ε x h0) ^ (a 0).val * (bsc_tau ε x h1) ^ (a 1).val *
          (bsc_tau ε x h2) ^ (a 2).val =
        (bsc_tau ε x h0) ^ (b 0).val * (bsc_tau ε x h1) ^ (b 1).val *
          (bsc_tau ε x h2) ^ (b 2).val := by
      have h := congrArg (fun u : G => ((u : (Module.End K (Fin N → K))ˣ) :
        Module.End K (Fin N → K))) hab
      simpa only [ψ, τ0, τ1, τ2, Units.val_mul, Units.val_pow_eq_pow_val,
        bsc_coe_tauUnit] using h
    have hmod := bsc_indep_modEq hp hsq h0pf h1pf h2pf h0ne h1ne h2ne h01 h02 h12
      hμ0 hμ1 hμ2 he
    funext i
    fin_cases i
    · apply Fin.ext
      have := hmod.1
      rwa [Nat.mod_eq_of_lt (a 0).isLt, Nat.mod_eq_of_lt (b 0).isLt] at this
    · apply Fin.ext
      have := hmod.2.1
      rwa [Nat.mod_eq_of_lt (a 1).isLt, Nat.mod_eq_of_lt (b 1).isLt] at this
    · apply Fin.ext
      have := hmod.2.2
      rwa [Nat.mod_eq_of_lt (a 2).isLt, Nat.mod_eq_of_lt (b 2).isLt] at this
  have hcardG : p ^ 3 ≤ Nat.card G := by
    have h := Nat.card_le_card_of_injective ψ hψinj
    rwa [show Nat.card (Fin 3 → Fin p) = p ^ 3 from by
      simp [Nat.card_eq_fintype_card, Fintype.card_fun]] at h
  let detHom : (Module.End K (Fin N → K))ˣ →* Kˣ :=
    Units.map (LinearMap.det : Module.End K (Fin N → K) →* K)
  let f : G →* Kˣ := detHom.comp G.subtype
  haveI : NeZero p := ⟨hp.ne_zero⟩
  have hfr : f.range ≤ rootsOfUnity p K := by
    rintro u ⟨y, rfl⟩
    rw [mem_rootsOfUnity]
    show detHom (y : (Module.End K (Fin N → K))ˣ) ^ p = 1
    rw [← map_pow, show (y : (Module.End K (Fin N → K))ˣ) ^ p = 1 from hexp y, map_one]
  have hfcard : Nat.card f.range ≤ p := by
    have hinj : Function.Injective
        (fun z : f.range => (⟨z.1, hfr z.2⟩ : rootsOfUnity p K)) :=
      fun a b h => Subtype.ext (congrArg (fun w : rootsOfUnity p K => (w : Kˣ)) h)
    calc Nat.card f.range ≤ Nat.card (rootsOfUnity p K) := Nat.card_le_card_of_injective _ hinj
      _ ≤ p := card_rootsOfUnity K p
  have hker : p ^ 2 ≤ Nat.card f.ker := by
    have h1 : p ^ 3 ≤ Nat.card f.ker * Nat.card f.range := by
      rw [Subgroup.card_ker_mul_card_range]
      exact hcardG
    have h2 : p ^ 3 ≤ Nat.card f.ker * p :=
      le_trans h1 (Nat.mul_le_mul_left _ hfcard)
    have hp3 : p ^ 3 = p ^ 2 * p := by ring
    rw [hp3] at h2
    exact Nat.le_of_mul_le_mul_right h2 hp.pos
  let Kdet : Subgroup (Module.End K (Fin N → K))ˣ := detHom.ker
  let U' : Subgroup (Module.End K (Fin N → K))ˣ := G ⊓ Kdet
  have hmap_ker : f.ker.map G.subtype = U' := by
    ext y
    constructor
    · intro hy
      rw [Subgroup.mem_map] at hy
      obtain ⟨z, hz, rfl⟩ := hy
      exact ⟨z.2, hz⟩
    · intro hy
      rw [Subgroup.mem_map]
      exact ⟨⟨y, hy.1⟩, hy.2, rfl⟩
  have hcardU' : Nat.card U' = Nat.card f.ker := by
    rw [← hmap_ker]
    exact (Nat.card_congr (Subgroup.equivMapOfInjective f.ker G.subtype
      (fun a b h => Subtype.ext h)).toEquiv).symm
  have hKdet_le_range : Kdet ≤ (slGL N K).range := by
    intro y hy
    have h1 : (detHom y : K) = 1 := congrArg (fun u : Kˣ => (u : K)) (MonoidHom.mem_ker.mp hy)
    exact mem_range_slGL (by simpa [detHom] using h1)
  have hU'le : U' ≤ (slGL N K).range := le_trans inf_le_right hKdet_le_range
  let U : Subgroup (SpecialLinearGroup (Fin N) K) := U'.comap (slGL N K)
  have hmap_sl : U.map (slGL N K) = U' := by
    change (U'.comap (slGL N K)).map (slGL N K) = U'
    rw [Subgroup.map_comap_eq]
    exact inf_eq_right.mpr hU'le
  have hcardU : Nat.card U = Nat.card f.ker := by
    have h1 : Nat.card U = Nat.card (U.map (slGL N K)) :=
      Nat.card_congr (Subgroup.equivMapOfInjective U (slGL N K) (slGL_injective)).toEquiv
    rw [h1, hmap_sl, hcardU']
  have hU : p ^ 2 ≤ Nat.card U := by rw [hcardU]; exact hker
  refine ⟨U, hU, ?_, ?_, ?_⟩
  · intro τ hτ
    have hmem : slGL N K τ ∈ G := (Subgroup.mem_comap.mp hτ).1
    have hpow : (slGL N K τ) ^ p = 1 := hexp ⟨slGL N K τ, hmem⟩
    apply slGL_injective
    rw [map_pow, hpow, map_one]
  · intro τ hτ B hB
    have hmem : slGL N K τ ∈ G := (Subgroup.mem_comap.mp hτ).1
    have hBu : glA B * glA g * (glA B)⁻¹ = glA g := by
      rw [← map_mul, ← map_inv, ← map_mul, hB]
    have hu_comm : Commute (glA B) (glA g) := by
      show glA B * glA g = glA g * glA B
      have h1 : (glA B * glA g * (glA B)⁻¹) * glA B = glA g * glA B := by rw [hBu]
      rwa [mul_assoc, inv_mul_cancel, mul_one] at h1
    have hBx : Commute (((glA B : (Module.End K (Fin N → K))ˣ) :
        Module.End K (Fin N → K))) x := by
      have h := congrArg (fun w : (Module.End K (Fin N → K))ˣ =>
        (w : Module.End K (Fin N → K))) hu_comm.eq
      rw [Units.val_mul, Units.val_mul] at h
      exact h
    have hcent : ∀ y ∈ G, Commute (glA B) y := by
      intro y hy
      refine Subgroup.closure_induction (p := fun z _ => Commute (glA B) z) ?_ ?_ ?_ ?_ hy
      · intro z hz
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
        rcases hz with rfl | rfl | rfl
        · apply Units.ext
          rw [Units.val_mul, Units.val_mul, show ((τ0 : (Module.End K (Fin N → K))ˣ) :
              Module.End K (Fin N → K)) = bsc_tau ε x h0 from rfl]
          exact (commute_aeval hBx (bsc_tauPoly ε x h0)).eq
        · apply Units.ext
          rw [Units.val_mul, Units.val_mul, show ((τ1 : (Module.End K (Fin N → K))ˣ) :
              Module.End K (Fin N → K)) = bsc_tau ε x h1 from rfl]
          exact (commute_aeval hBx (bsc_tauPoly ε x h1)).eq
        · apply Units.ext
          rw [Units.val_mul, Units.val_mul, show ((τ2 : (Module.End K (Fin N → K))ˣ) :
              Module.End K (Fin N → K)) = bsc_tau ε x h2 from rfl]
          exact (commute_aeval hBx (bsc_tauPoly ε x h2)).eq
      · exact Commute.one_right _
      · intro u v _ _ hu hv
        exact hu.mul_right hv
      · intro u _ hu
        exact hu.inv_right
    have hsl : slGL N K (CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation N
      K B τ) =
        glA B * slGL N K τ * (glA B)⁻¹ := by
      change Matrix.GeneralLinearGroup.toLin (Matrix.SpecialLinearGroup.toGL
          (CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation N K B τ)) =
        Matrix.GeneralLinearGroup.toLin B *
          Matrix.GeneralLinearGroup.toLin (Matrix.SpecialLinearGroup.toGL τ) *
          (Matrix.GeneralLinearGroup.toLin B)⁻¹
      rw [CFSG.ComponentClassification.CatalogueBHigherLinearAction.toGL_slConjugation,
        map_mul, map_mul, map_inv]
    apply slGL_injective
    rw [hsl, (hcent (slGL N K τ) hmem).eq]
    group
  · intro τ hτ v hv
    have hmem : slGL N K τ ∈ G := (Subgroup.mem_comap.mp hτ).1
    have hfix : ∀ y ∈ G, (y : Module.End K (Fin N → K)) v = v := by
      intro y hy
      refine Subgroup.closure_induction (p := fun z _ =>
        (((z : (Module.End K (Fin N → K))ˣ) : Module.End K (Fin N → K)) v = v))
        ?_ ?_ ?_ ?_ hy
      · intro z hz
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
        rcases hz with rfl | rfl | rfl
        · change (bsc_tau ε x h0) v = v
          exact bsc_tau_apply_of_mem_ne hsq ε h0pf hgoodx h0ne.symm hv
        · change (bsc_tau ε x h1) v = v
          exact bsc_tau_apply_of_mem_ne hsq ε h1pf hgoodx h1ne.symm hv
        · change (bsc_tau ε x h2) v = v
          exact bsc_tau_apply_of_mem_ne hsq ε h2pf hgoodx h2ne.symm hv
      · simp
      · intro u w _ _ hu hw
        change (((u * w : (Module.End K (Fin N → K))ˣ) : Module.End K (Fin N → K))) v = v
        rw [Units.val_mul, Module.End.mul_apply, hw, hu]
      · intro u _ hu
        change (((u⁻¹ : (Module.End K (Fin N → K))ˣ) : Module.End K (Fin N → K))) v = v
        have h1 : ((u⁻¹ : (Module.End K (Fin N → K))ˣ) : Module.End K (Fin N → K)) v =
            ((u⁻¹ : (Module.End K (Fin N → K))ˣ) : Module.End K (Fin N → K))
              (((u : (Module.End K (Fin N → K))ˣ) : Module.End K (Fin N → K)) v) := by rw [hu]
        rw [h1]
        change (((u⁻¹ * u : (Module.End K (Fin N → K))ˣ) : Module.End K (Fin N → K))) v = v
        rw [inv_mul_cancel]
        simp
    exact hfix (slGL N K τ) hmem

end CFSG.StandardType

end
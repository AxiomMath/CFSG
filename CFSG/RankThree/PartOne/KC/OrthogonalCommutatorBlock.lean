module

public import CFSG.RankThree.PartOne.KC.OrthogonalCommutatorFix
public import CFSG.RankThree.PartOne.KC.OrthogonalCommutatorTorsion
public import CFSG.RankThree.PartOne.KC.OrthogonalSupportedScalarConj

public section

namespace CFSG.RankThree.PartOne.KCOrthComm

open Polynomial Module CFSG.RankThree.PartOne.KCPrimary CFSG.RankThree.PartOne.KCOrthogonal

variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V] {xe : V ≃ₗ[K] V}

@[expose] def BlockScalar (xe : V ≃ₗ[K] V) (M : V ≃ₗ[K] V) (h : K[X]) : Prop :=
  ∃ f : K[X], ∀ v ∈ primaryComponent xe.toLinearMap h, M v = aeval xe.toLinearMap f v

theorem aeval_mem_primaryComponent (f : K[X]) {h : K[X]} {v : V}
    (hv : v ∈ primaryComponent xe.toLinearMap h) :
    aeval xe.toLinearMap f v ∈ primaryComponent xe.toLinearMap h :=
  apply_mem_primaryComponent (commute_aeval (Commute.refl xe.toLinearMap) f).symm hv

theorem BlockScalar.apply_mem {M : V ≃ₗ[K] V} {h : K[X]} (hM : BlockScalar xe M h) {v : V}
    (hv : v ∈ primaryComponent xe.toLinearMap h) : M v ∈ primaryComponent xe.toLinearMap h := by
  obtain ⟨f, hf⟩ := hM
  rw [hf v hv]
  exact aeval_mem_primaryComponent f hv

theorem pow_apply_of_blockScalar {M : V ≃ₗ[K] V} {h : K[X]} {f : K[X]}
    (hf : ∀ v ∈ primaryComponent xe.toLinearMap h, M v = aeval xe.toLinearMap f v) (n : ℕ)
    {v : V} (hv : v ∈ primaryComponent xe.toLinearMap h) :
    (M ^ n) v = aeval xe.toLinearMap (f ^ n) v := by
  induction n generalizing v with
  | zero => simp
  | succ n ih =>
    rw [pow_succ M n, LinearEquiv.mul_apply, hf v hv, ih (aeval_mem_primaryComponent f hv),
      pow_succ f n, map_mul, Module.End.mul_apply]

theorem mul_comm_apply_of_blockScalar {M M' : V ≃ₗ[K] V} {h : K[X]} (hM : BlockScalar xe M h)
    (hM' : BlockScalar xe M' h) {v : V} (hv : v ∈ primaryComponent xe.toLinearMap h) :
    M (M' v) = M' (M v) := by
  obtain ⟨f, hf⟩ := hM
  obtain ⟨f', hf'⟩ := hM'
  rw [hf' v hv, hf _ (aeval_mem_primaryComponent f' hv), hf v hv,
    hf' _ (aeval_mem_primaryComponent f hv)]
  rw [← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul, mul_comm]

theorem mul_comm_of_blockScalar [FiniteDimensional K V]
    (hsq : Squarefree (minpoly K xe.toLinearMap)) {M M' : V ≃ₗ[K] V}
    (hM : ∀ h ∈ primaryFactors xe.toLinearMap, BlockScalar xe M h)
    (hM' : ∀ h ∈ primaryFactors xe.toLinearMap, BlockScalar xe M' h) : M * M' = M' * M := by
  have hlin : (M * M').toLinearMap = (M' * M).toLinearMap := by
    refine ext_primaryComponent hsq fun h hh v hv => ?_
    exact mul_comm_apply_of_blockScalar (hM h hh) (hM' h hh) hv
  exact LinearEquiv.toLinearMap_injective hlin

theorem dvd_of_aeval_eq_zero [FiniteDimensional K V]
    (hsq : Squarefree (minpoly K xe.toLinearMap)) {h : K[X]}
    (hh : h ∈ primaryFactors xe.toLinearMap) {g : K[X]}
    (hg : ∀ v ∈ primaryComponent xe.toLinearMap h, aeval xe.toLinearMap g v = 0) : h ∣ g := by
  by_contra hnd
  have hirr := irreducible_of_mem_primaryFactors hh
  have hcop : IsCoprime h g := (hirr.coprime_iff_not_dvd).mpr hnd
  obtain ⟨a, b, hab⟩ := hcop
  obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot (primaryComponent_ne_bot hsq hh)
  apply hv0
  have h1 : aeval xe.toLinearMap (a * h + b * g) v = v := by
    rw [hab, map_one]
    rfl
  rw [map_add, LinearMap.add_apply, map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply,
    mem_primaryComponent.mp hv, hg v hv, map_zero, map_zero, add_zero] at h1
  exact h1.symm

theorem map_symm_eq_self {σ : K ≃+* K} {h : K[X]} (hσ : h.map (σ : K →+* K) = h) :
    h.map (σ.symm : K →+* K) = h := by
  have h1 := congrArg (Polynomial.map (σ.symm : K →+* K)) hσ
  rw [Polynomial.map_map] at h1
  have h2 : (σ.symm : K →+* K).comp (σ : K →+* K) = RingHom.id K :=
    RingHom.ext fun c => σ.symm_apply_apply c
  rw [h2, Polynomial.map_id] at h1
  exact h1.symm

theorem semilinConj_apply_eq_of_blockScalar [FiniteDimensional K V]
    (hsq : Squarefree (minpoly K xe.toLinearMap)) {σ : K ≃+* K} {F : V ≃+ V}
    (hF : ∀ (c : K) (v : V), F (c • v) = σ c • F v) (hFx : ∀ v, F (xe v) = xe (F v)) {N : ℕ}
    (hN : Odd N) (hσN : σ ^ N = 1) {h : K[X]} (hh : h ∈ primaryFactors xe.toLinearMap)
    (hσh : h.map (σ : K →+* K) = h) {M : V ≃ₗ[K] V} (hM : BlockScalar xe M h) {s : ℕ}
    (hMs : M ^ 2 ^ s = 1) {v : V} (hv : v ∈ primaryComponent xe.toLinearMap h) :
    semilinConj F σ hF M v = M v := by
  have hFx' : ∀ v, F.symm (xe v) = xe (F.symm v) := fun v => by
    apply F.injective
    rw [AddEquiv.apply_symm_apply, hFx, AddEquiv.apply_symm_apply]
  have hF' : ∀ (c : K) (v : V), F.symm (c • v) = σ.symm c • F.symm v := semilin_symm_smul F σ hF
  have : Fact (Irreducible h) := ⟨irreducible_of_mem_primaryFactors hh⟩
  obtain ⟨f, hf⟩ := hM
  have hvF : F.symm v ∈ primaryComponent xe.toLinearMap h := by
    have := F_mem_primaryComponent σ.symm F.symm hF' hFx' hv
    rwa [map_symm_eq_self hσh] at this
  have hpow : AdjoinRoot.mk h f ^ 2 ^ s = 1 := by
    have hdvd : h ∣ f ^ 2 ^ s - 1 := by
      refine dvd_of_aeval_eq_zero hsq hh fun w hw => ?_
      have h1 := pow_apply_of_blockScalar hf (2 ^ s) hw
      rw [hMs] at h1
      rw [map_sub, LinearMap.sub_apply, ← h1, map_one]
      change (1 : V ≃ₗ[K] V) w - w = 0
      simp
    rw [← map_pow, ← map_one (AdjoinRoot.mk h)]
    exact AdjoinRoot.mk_eq_mk.mpr (by simpa using hdvd)
  have hmk := mk_map_eq_of_pow_two_pow_eq_one hN hσN hσh hpow
  have hdvd2 : h ∣ f.map (σ : K →+* K) - f := AdjoinRoot.mk_eq_mk.mp hmk
  have hvan : aeval xe.toLinearMap (f.map (σ : K →+* K)) v = aeval xe.toLinearMap f v := by
    obtain ⟨q, hq⟩ := hdvd2
    have : aeval xe.toLinearMap (f.map (σ : K →+* K) - f) v = 0 := by
      rw [hq, map_mul, Module.End.mul_apply]
      exact mem_primaryComponent.mp (aeval_mem_primaryComponent q hv)
    rw [map_sub, LinearMap.sub_apply, sub_eq_zero] at this
    exact this
  change F (M (F.symm v)) = M v
  rw [hf _ hvF, F_aeval σ F hF hFx, AddEquiv.apply_symm_apply, hvan, hf v hv]

theorem semilinConj_eq_of_blockScalar [FiniteDimensional K V]
    (hsq : Squarefree (minpoly K xe.toLinearMap)) {σ : K ≃+* K} {F : V ≃+ V}
    (hF : ∀ (c : K) (v : V), F (c • v) = σ c • F v) (hFx : ∀ v, F (xe v) = xe (F v)) {N : ℕ}
    (hN : Odd N) (hσN : σ ^ N = 1)
    (hfix : ∀ h ∈ primaryFactors xe.toLinearMap, h.map (σ : K →+* K) = h) {M : V ≃ₗ[K] V}
    (hM : ∀ h ∈ primaryFactors xe.toLinearMap, BlockScalar xe M h) {s : ℕ} (hMs : M ^ 2 ^ s = 1) :
    semilinConj F σ hF M = M := by
  refine LinearEquiv.toLinearMap_injective (ext_primaryComponent hsq fun h hh v hv => ?_)
  exact semilinConj_apply_eq_of_blockScalar hsq hF hFx hN hσN hh (hfix h hh) (hM h hh) hMs hv

end CFSG.RankThree.PartOne.KCOrthComm

module

public import Mathlib.GroupTheory.IsPerfect
public import Mathlib.RepresentationTheory.Irreducible

import Mathlib.Algebra.Polynomial.SpecificDegree

public section

open Polynomial

namespace CFSG.RankThree.PartTwo.J2Residue

variable {K : Type*} [Field K] {Γ : Type*} [Group Γ] {V : Type*} [AddCommGroup V] [Module K V]

theorem det_eq_one_of_isPerfect {K V Λ : Type*} [Field K] [AddCommGroup V] [Module K V]
    [Group Λ] (hΛ : Group.IsPerfect Λ) (ρ : Representation K Λ V) (g : Λ) :
    LinearMap.det (ρ g) = 1 := by
  let φ : Λ →* Kˣ :=
    (Units.map (LinearMap.det : (V →ₗ[K] V) →* K)).comp ρ.asGroupHom
  have hker : commutator Λ ≤ φ.ker := Abelianization.commutator_subset_ker φ
  rw [hΛ.commutator_eq_top] at hker
  have hmem : g ∈ φ.ker := hker (Subgroup.mem_top g)
  rw [MonoidHom.mem_ker] at hmem
  have h' := congrArg Units.val hmem
  simpa [φ, Representation.asGroupHom_apply] using h'

theorem isCompl_ker_sub_one_ker_add_one {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (h2 : (2 : K) ≠ 0) (T : Module.End K V) (hT : T * T = 1) :
    IsCompl (LinearMap.ker (T - 1)) (LinearMap.ker (T + 1)) := by
  have hTT : ∀ v, T (T v) = v := fun v => by
    have := congrArg (fun f : Module.End K V => f v) hT
    simpa using this
  constructor
  · rw [Submodule.disjoint_def]
    intro v h1 h2'
    rw [LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero] at h1
    rw [LinearMap.mem_ker, LinearMap.add_apply, Module.End.one_apply] at h2'
    rw [h1] at h2'
    have h3 : (2 : K) • v = 0 := by rw [two_smul]; exact h2'
    exact (smul_eq_zero.mp h3).resolve_left h2
  · rw [codisjoint_iff, eq_top_iff]
    intro v _
    have hsum : (2 : K)⁻¹ • (v + T v) + (2 : K)⁻¹ • (v - T v) = v := by
      rw [← smul_add, show v + T v + (v - T v) = (2 : K) • v by rw [two_smul]; abel,
        smul_smul, inv_mul_cancel₀ h2, one_smul]
    rw [← hsum]
    apply Submodule.add_mem_sup
    · rw [LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply, map_smul, map_add, hTT]
      rw [add_comm (T v) v, sub_self]
    · rw [LinearMap.mem_ker, LinearMap.add_apply, Module.End.one_apply, map_smul, map_sub, hTT]
      rw [← smul_add]
      simp

theorem det_eq_neg_one_pow_finrank_ker_add_one {K V : Type*} [Field K] [AddCommGroup V]
    [Module K V] [FiniteDimensional K V] (h2 : (2 : K) ≠ 0) {T : Module.End K V}
    (hT : T * T = 1) :
    LinearMap.det T = (-1 : K) ^ Module.finrank K (LinearMap.ker (T + 1)) := by
  have hc := isCompl_ker_sub_one_ker_add_one h2 T hT
  let e : (LinearMap.ker (T - 1) × LinearMap.ker (T + 1)) ≃ₗ[K] V :=
    Submodule.prodEquivOfIsCompl _ _ hc
  let f : Module.End K (LinearMap.ker (T - 1) × LinearMap.ker (T + 1)) :=
    LinearMap.prodMap LinearMap.id (-LinearMap.id)
  have hTe : ∀ z : LinearMap.ker (T - 1) × LinearMap.ker (T + 1), T (e z) = e (f z) := by
    rintro ⟨p, q⟩
    have hp : T (p : V) = p := by
      have := p.2
      rw [LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero] at this
      exact this
    have hq : T (q : V) = -q := by
      have := q.2
      rw [LinearMap.mem_ker, LinearMap.add_apply, Module.End.one_apply,
        add_eq_zero_iff_eq_neg] at this
      exact this
    simp [e, f, Submodule.coe_prodEquivOfIsCompl', hp, hq]
  have hTf : T = (e : _ →ₗ[K] V) ∘ₗ f ∘ₗ (e.symm : V →ₗ[K] _) := by
    refine LinearMap.ext fun x => ?_
    have := hTe (e.symm x)
    simpa using this
  have hdet : LinearMap.det T = LinearMap.det f := by
    conv_lhs => rw [hTf]
    rw [LinearMap.det_conj]
  rw [hdet, LinearMap.det_prodMap]
  have h1 : LinearMap.det (LinearMap.id : Module.End K (LinearMap.ker (T - 1))) = 1 :=
    LinearMap.det_id
  have h2' : LinearMap.det (-LinearMap.id : Module.End K (LinearMap.ker (T + 1))) =
      (-1 : K) ^ Module.finrank K (LinearMap.ker (T + 1)) := by
    rw [show (-LinearMap.id : Module.End K (LinearMap.ker (T + 1))) = (-1 : K) • LinearMap.id from
      (neg_one_smul K _).symm, LinearMap.det_smul, LinearMap.det_id, mul_one]
  rw [h1, h2', one_mul]

theorem rho_eq_neg_one_of_commute {ρ : Representation K Γ V} (hρ : ρ.IsIrreducible) {z : Γ}
    (hz : ∀ g : Γ, ρ z * ρ g = ρ g * ρ z) (hz2 : z * z = 1) (hz1 : ρ z ≠ 1) : ρ z = -1 := by
  let U : Subrepresentation ρ :=
    Subrepresentation.mk (LinearMap.ker (ρ z - 1)) (by
      intro g v hv
      rw [LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero] at hv ⊢
      calc ρ z (ρ g v) = (ρ z * ρ g) v := by rw [Module.End.mul_apply]
        _ = (ρ g * ρ z) v := by rw [hz g]
        _ = ρ g (ρ z v) := by rw [Module.End.mul_apply]
        _ = ρ g v := by rw [hv])
  have hUne : U ≠ ⊤ := by
    intro htop
    apply hz1
    ext v
    have hv : v ∈ U := by rw [htop]; exact Submodule.mem_top
    have hv' : v ∈ LinearMap.ker (ρ z - 1) := hv
    rw [LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero] at hv'
    simpa [Module.End.one_apply] using hv'
  have hUbot : U = ⊥ := (hρ.eq_bot_or_eq_top U).resolve_right hUne
  have hker : LinearMap.ker (ρ z - 1) = ⊥ := by
    have := congrArg Subrepresentation.toSubmodule hUbot
    rw [show (⊥ : Subrepresentation ρ).toSubmodule = (⊥ : Submodule K V) from rfl] at this
    simpa [U] using this
  have hzz : ρ z * ρ z = 1 := by
    rw [← map_mul, hz2, map_one]
  have hzero : (ρ z - 1) * (ρ z + 1) = 0 := by
    rw [sub_mul, one_mul, mul_add, mul_one, hzz]
    abel
  ext v
  have hmem : (ρ z + 1) v ∈ LinearMap.ker (ρ z - 1) := by
    show (ρ z - 1) ((ρ z + 1) v) = 0
    have := congrArg (fun f : Module.End K V => f v) hzero
    simpa [Module.End.mul_apply] using this
  rw [hker] at hmem
  have hv : ρ z v + v = 0 := by
    simpa [LinearMap.add_apply, Module.End.one_apply] using hmem
  rw [LinearMap.neg_apply, Module.End.one_apply]
  exact eq_neg_of_add_eq_zero_left hv

theorem rho_mul_rho_add_rho_add_one_eq_zero {ρ : Representation K Γ V} (hρ : ρ.IsIrreducible)
    {σ : Γ} (hσ : ∀ g : Γ, ρ σ * ρ g = ρ g * ρ σ) (hσ3 : σ ^ 3 = 1) (hσ1 : ρ σ ≠ 1) :
    ρ σ * ρ σ + ρ σ + 1 = 0 := by
  let U : Subrepresentation ρ :=
    Subrepresentation.mk (LinearMap.ker (ρ σ - 1)) (by
      intro g v hv
      rw [LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero] at hv ⊢
      calc ρ σ (ρ g v) = (ρ σ * ρ g) v := by rw [Module.End.mul_apply]
        _ = (ρ g * ρ σ) v := by rw [hσ g]
        _ = ρ g (ρ σ v) := by rw [Module.End.mul_apply]
        _ = ρ g v := by rw [hv])
  have hUne : U ≠ ⊤ := by
    intro htop
    apply hσ1
    ext v
    have hv : v ∈ U := by rw [htop]; exact Submodule.mem_top
    have hv' : v ∈ LinearMap.ker (ρ σ - 1) := hv
    rw [LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero] at hv'
    simpa [Module.End.one_apply] using hv'
  have hUbot : U = ⊥ := (hρ.eq_bot_or_eq_top U).resolve_right hUne
  have hker : LinearMap.ker (ρ σ - 1) = ⊥ := by
    have := congrArg Subrepresentation.toSubmodule hUbot
    rw [show (⊥ : Subrepresentation ρ).toSubmodule = (⊥ : Submodule K V) from rfl] at this
    simpa [U] using this
  have hthree : ρ σ * ρ σ * ρ σ = 1 := by
    rw [← map_mul, ← map_mul, show (σ * σ) * σ = σ ^ 3 by rw [pow_succ, pow_two], hσ3,
      map_one]
  have hzero : (ρ σ - 1) * (ρ σ * ρ σ + ρ σ + 1) = 0 := by
    rw [sub_mul, one_mul, mul_add, mul_add, mul_one, ← mul_assoc, hthree]
    abel
  ext v
  have hmem : (ρ σ * ρ σ + ρ σ + 1) v ∈ LinearMap.ker (ρ σ - 1) := by
    show (ρ σ - 1) ((ρ σ * ρ σ + ρ σ + 1) v) = 0
    have := congrArg (fun f : Module.End K V => f v) hzero
    simpa [Module.End.mul_apply] using this
  rw [hker] at hmem
  simpa using hmem

theorem even_finrank_ker_add_one_of_isPerfect (h2 : (2 : K) ≠ 0) [FiniteDimensional K V]
    (ρ : Representation K Γ V) {Λ : Subgroup Γ} (hΛ : Group.IsPerfect Λ) {z : Γ} (hzΛ : z ∈ Λ)
    (hz2 : z * z = 1) : Even (Module.finrank K (LinearMap.ker (ρ z + 1))) := by
  let T : Module.End K V := ρ z
  have hT : T * T = 1 := by
    change ρ z * ρ z = 1
    rw [← map_mul, hz2, map_one]
  have hdet : LinearMap.det T = (-1 : K) ^ Module.finrank K (LinearMap.ker (T + 1)) :=
    det_eq_neg_one_pow_finrank_ker_add_one h2 hT
  have hdet1 : LinearMap.det T = 1 := by
    have := det_eq_one_of_isPerfect hΛ (ρ.comp Λ.subtype) ⟨z, hzΛ⟩
    simpa [T] using this
  have hpow : (-1 : K) ^ Module.finrank K (LinearMap.ker (T + 1)) = 1 := by
    rw [← hdet, hdet1]
  have hne : (-1 : K) ≠ 1 := by
    intro h
    apply h2
    linear_combination -h
  exact (neg_one_pow_eq_one_iff_even hne).mp hpow

theorem even_finrank_of_isPerfect (h2 : (2 : K) ≠ 0) [FiniteDimensional K V]
    (ρ : Representation K Γ V) {Λ : Subgroup Γ} (hΛ : Group.IsPerfect Λ) (W : Submodule K V)
    (hW : ∀ g ∈ Λ, ∀ w ∈ W, ρ g w ∈ W) {z : Γ} (hzΛ : z ∈ Λ) (hz : ∀ w ∈ W, ρ z w = -w) :
    Even (Module.finrank K W) := by
  let ρΛ : Representation K Λ V := ρ.comp Λ.subtype
  let S : Subrepresentation ρΛ :=
    Subrepresentation.mk W (fun g w hw => hW (g : Γ) g.2 w hw)
  have hdet : LinearMap.det (S.toRepresentation ⟨z, hzΛ⟩) = 1 :=
    det_eq_one_of_isPerfect hΛ S.toRepresentation ⟨z, hzΛ⟩
  have hneg : S.toRepresentation ⟨z, hzΛ⟩ = -1 := by
    ext w
    have hw : ((S.toRepresentation ⟨z, hzΛ⟩) w : V) = ρ z (w : V) := by
      have hwW : S.toRepresentation ⟨z, hzΛ⟩ w =
          ⟨ρ z (w : V), hW z hzΛ (w : V) w.2⟩ := by
        rw [Subrepresentation.toRepresentation_apply_coe]
        rfl
      rw [hwW]
    rw [hw]
    have h := hz (w : V) w.2
    simpa [LinearMap.neg_apply, Module.End.one_apply] using h
  have hpow : (-1 : K) ^ Module.finrank K W = 1 := by
    have hdetneg : LinearMap.det (S.toRepresentation ⟨z, hzΛ⟩) = (-1 : K) ^ Module.finrank K W := by
      rw [hneg]
      rw [show (-1 : Module.End K W) = (-1 : K) • LinearMap.id from (neg_one_smul K _).symm]
      rw [LinearMap.det_smul, LinearMap.det_id, mul_one]
    rw [← hdetneg, hdet]
  have hne : (-1 : K) ≠ 1 := by
    intro h
    apply h2
    linear_combination -h
  exact (neg_one_pow_eq_one_iff_even hne).mp hpow

private theorem mul_sub_scalar_mul_sub_scalar_eq_zero {K W : Type*} [Field K]
    [AddCommGroup W] [Module K W] {τ : Module.End K W} {a b : K}
    (hτ : τ ^ 2 + τ + 1 = 0) (hsum : a + b = -1) (hprod : a * b = 1) :
    (τ - a • (1 : Module.End K W)) * (τ - b • (1 : Module.End K W)) = 0 := by
  have h : (τ - a • (1 : Module.End K W)) * (τ - b • (1 : Module.End K W)) =
      τ * τ - (a + b) • τ + (a * b) • (1 : Module.End K W) := by
    rw [sub_mul, mul_sub, mul_sub]
    simp only [smul_mul_assoc, mul_smul_comm, one_mul, mul_one, smul_smul]
    module
  rw [h, hsum, hprod]
  simp only [neg_smul, one_smul]
  have hτ' : τ * τ + τ + 1 = 0 := by simpa [pow_two] using hτ
  rw [sub_neg_eq_add]
  exact hτ'

private theorem isCompl_ker_sub_scalar_ker_sub_scalar {K W : Type*} [Field K]
    [AddCommGroup W] [Module K W] {τ : Module.End K W} {ω : K}
    (hτ : τ ^ 2 + τ + 1 = 0) (hω : ω ^ 2 + ω + 1 = 0)
    (hωne : ω ^ 2 ≠ ω) :
    IsCompl (LinearMap.ker (τ - ω • (1 : Module.End K W)))
      (LinearMap.ker (τ - ω ^ 2 • (1 : Module.End K W))) := by
  have hω3 : ω ^ 3 = 1 := by
    have h : (ω - 1) * (ω ^ 2 + ω + 1) = 0 := by rw [hω, mul_zero]
    have h' : (ω - 1) * (ω ^ 2 + ω + 1) = ω ^ 3 - 1 := by ring
    rw [h'] at h
    exact sub_eq_zero.mp h
  have hωsum : ω + ω ^ 2 = -1 := by linear_combination hω
  have hωprod : ω * ω ^ 2 = 1 := by rw [← hω3]; ring
  have hωsum' : ω ^ 2 + ω = -1 := by rw [add_comm]; exact hωsum
  have hωprod' : ω ^ 2 * ω = 1 := by rw [mul_comm]; exact hωprod
  have hfac : (τ - ω • (1 : Module.End K W)) * (τ - ω ^ 2 • (1 : Module.End K W)) = 0 :=
    mul_sub_scalar_mul_sub_scalar_eq_zero hτ hωsum hωprod
  have hfac' : (τ - ω ^ 2 • (1 : Module.End K W)) * (τ - ω • (1 : Module.End K W)) = 0 :=
    mul_sub_scalar_mul_sub_scalar_eq_zero hτ hωsum' hωprod'
  have hc : ω - ω ^ 2 ≠ 0 := sub_ne_zero.mpr (Ne.symm hωne)
  constructor
  · rw [Submodule.disjoint_def]
    intro v hv1 hv2
    rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply,
      sub_eq_zero] at hv1
    rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply,
      sub_eq_zero] at hv2
    have h : (ω - ω ^ 2) • v = 0 := by
      rw [sub_smul, ← hv1, ← hv2, sub_self]
    exact (smul_eq_zero.mp h).resolve_left hc
  · rw [codisjoint_iff, eq_top_iff]
    intro v _
    rw [Submodule.mem_sup]
    refine ⟨(ω - ω ^ 2)⁻¹ • ((τ - ω ^ 2 • (1 : Module.End K W)) v), ?_,
      (ω ^ 2 - ω)⁻¹ • ((τ - ω • (1 : Module.End K W)) v), ?_, ?_⟩
    · rw [LinearMap.mem_ker]
      have h : (τ - ω • (1 : Module.End K W))
          ((ω - ω ^ 2)⁻¹ • ((τ - ω ^ 2 • (1 : Module.End K W)) v)) =
          (ω - ω ^ 2)⁻¹ •
            (((τ - ω • (1 : Module.End K W)) * (τ - ω ^ 2 • (1 : Module.End K W))) v) := by
        rw [map_smul, Module.End.mul_apply]
      rw [h, hfac]
      simp
    · rw [LinearMap.mem_ker]
      have h : (τ - ω ^ 2 • (1 : Module.End K W))
          ((ω ^ 2 - ω)⁻¹ • ((τ - ω • (1 : Module.End K W)) v)) =
          (ω ^ 2 - ω)⁻¹ •
            (((τ - ω ^ 2 • (1 : Module.End K W)) * (τ - ω • (1 : Module.End K W))) v) := by
        rw [map_smul, Module.End.mul_apply]
      rw [h, hfac']
      simp
    · have hneg : ω ^ 2 - ω = -(ω - ω ^ 2) := by ring
      calc
        (ω - ω ^ 2)⁻¹ • ((τ - ω ^ 2 • (1 : Module.End K W)) v) +
            (ω ^ 2 - ω)⁻¹ • ((τ - ω • (1 : Module.End K W)) v)
            = (ω - ω ^ 2)⁻¹ • ((τ - ω ^ 2 • (1 : Module.End K W)) v) -
                (ω - ω ^ 2)⁻¹ • ((τ - ω • (1 : Module.End K W)) v) := by
                rw [hneg, inv_neg, neg_smul]
                abel
        _ = (ω - ω ^ 2)⁻¹ •
              (((τ - ω ^ 2 • (1 : Module.End K W)) v) -
                ((τ - ω • (1 : Module.End K W)) v)) := by
                rw [← smul_sub]
        _ = (ω - ω ^ 2)⁻¹ • ((ω - ω ^ 2) • v) := by
                congr 1
                rw [LinearMap.sub_apply, LinearMap.sub_apply, LinearMap.smul_apply,
                  LinearMap.smul_apply, Module.End.one_apply]
                module
        _ = v := by
                rw [smul_smul, inv_mul_cancel₀ hc, one_smul]

private theorem three_dvd_finrank_eigenspace {K W Λ : Type*} [Field K] [AddCommGroup W]
    [Module K W] [FiniteDimensional K W] [Group Λ] (hΛ : Group.IsPerfect Λ)
    (ρ : Representation K Λ W) (σ : Λ) (τ : Module.End K W) (hσ : ρ σ = τ)
    (U : Submodule K W) (hU : ∀ g : Λ, ∀ u ∈ U, ρ g u ∈ U) {ω : K}
    (hUτ : ∀ u ∈ U, τ u = ω • u) (hω3 : ω ^ 3 = 1) (hω1 : ω ≠ 1) :
    3 ∣ Module.finrank K U := by
  let S : Subrepresentation ρ := Subrepresentation.mk U (fun g u hu => hU g u hu)
  have hdet : LinearMap.det (S.toRepresentation σ) = 1 :=
    det_eq_one_of_isPerfect hΛ S.toRepresentation σ
  have hscalar : S.toRepresentation σ = ω • (1 : Module.End K U) := by
    ext u
    have hcoe : ((S.toRepresentation σ) u : W) = ρ σ (u : W) := by
      exact (Subrepresentation.toRepresentation_apply_coe (ρ' := S) (g := σ) (v := u)
        (w := ⟨ρ σ (u : W), hU σ (u : W) u.2⟩)).mp rfl
    rw [hcoe, hσ, LinearMap.smul_apply, Module.End.one_apply]
    simpa using hUτ (u : W) u.2
  have hpow : ω ^ Module.finrank K U = 1 := by
    have h := congrArg LinearMap.det hscalar
    rw [hdet] at h
    simpa using h.symm
  haveI : Fact (Nat.Prime 3) := ⟨by decide⟩
  have hord : orderOf ω = 3 := orderOf_eq_prime hω3 hω1
  have hdvd : orderOf (ω : K) ∣ Module.finrank K U := (orderOf_dvd_iff_pow_eq_one).mpr hpow
  simpa [hord] using hdvd

private theorem three_dvd_of_root {K W Λ : Type*} [Field K] [AddCommGroup W]
    [Module K W] [FiniteDimensional K W] [Group Λ] (hΛ : Group.IsPerfect Λ)
    (ρ : Representation K Λ W) (σ : Λ) (τ : Module.End K W) (hσ : ρ σ = τ)
    (hτ : τ ^ 2 + τ + 1 = 0) (hcomm : ∀ g : Λ, Commute (ρ g) τ)
    (h3 : (3 : K) ≠ 0) {ω : K} (hω : ω ^ 2 + ω + 1 = 0) :
    3 ∣ Module.finrank K W := by
  have hω3 : ω ^ 3 = 1 := by
    have h : (ω - 1) * (ω ^ 2 + ω + 1) = 0 := by rw [hω, mul_zero]
    have h' : (ω - 1) * (ω ^ 2 + ω + 1) = ω ^ 3 - 1 := by ring
    rw [h'] at h
    exact sub_eq_zero.mp h
  have hω1 : ω ≠ 1 := by
    intro h
    subst h
    apply h3
    linear_combination hω
  have hω0 : ω ≠ 0 := by
    intro h
    subst h
    have h10 : (1 : K) = 0 := by simpa using hω
    exact one_ne_zero h10
  have hω2ne1 : ω ^ 2 ≠ 1 := by
    intro h
    apply hω1
    calc ω = ω * ω ^ 2 := by rw [h, mul_one]
      _ = ω ^ 3 := by ring
      _ = 1 := hω3
  have hωne : ω ^ 2 ≠ ω := by
    intro h
    have hprod : ω * (1 - ω) = 0 := by
      have h' : ω - ω ^ 2 = 0 := sub_eq_zero.mpr h.symm
      linear_combination h'
    rcases mul_eq_zero.mp hprod with h0 | h1
    · exact hω0 h0
    · exact hω1 (sub_eq_zero.mp h1).symm
  let U : Submodule K W := LinearMap.ker (τ - ω • (1 : Module.End K W))
  let V : Submodule K W := LinearMap.ker (τ - ω ^ 2 • (1 : Module.End K W))
  have hc : IsCompl U V := isCompl_ker_sub_scalar_ker_sub_scalar hτ hω hωne
  have hUinv : ∀ g : Λ, ∀ u ∈ U, ρ g u ∈ U := by
    intro g u hu
    rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply,
      sub_eq_zero] at hu ⊢
    calc τ (ρ g u) = (τ * ρ g) u := by rw [Module.End.mul_apply]
      _ = (ρ g * τ) u := by rw [← (hcomm g).eq]
      _ = ρ g (τ u) := by rw [Module.End.mul_apply]
      _ = ρ g (ω • u) := by rw [hu]
      _ = ω • ρ g u := by rw [map_smul]
  have hVinv : ∀ g : Λ, ∀ v ∈ V, ρ g v ∈ V := by
    intro g v hv
    rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply,
      sub_eq_zero] at hv ⊢
    calc τ (ρ g v) = (τ * ρ g) v := by rw [Module.End.mul_apply]
      _ = (ρ g * τ) v := by rw [← (hcomm g).eq]
      _ = ρ g (τ v) := by rw [Module.End.mul_apply]
      _ = ρ g (ω ^ 2 • v) := by rw [hv]
      _ = ω ^ 2 • ρ g v := by rw [map_smul]
  have hUτ : ∀ u ∈ U, τ u = ω • u := by
    intro u hu
    simpa [U, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply,
      Module.End.one_apply, sub_eq_zero] using hu
  have hVτ : ∀ v ∈ V, τ v = ω ^ 2 • v := by
    intro v hv
    simpa [V, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply,
      Module.End.one_apply, sub_eq_zero] using hv
  have hdU : 3 ∣ Module.finrank K U :=
    three_dvd_finrank_eigenspace hΛ ρ σ τ hσ U hUinv hUτ hω3 hω1
  have hdV : 3 ∣ Module.finrank K V :=
    three_dvd_finrank_eigenspace hΛ ρ σ τ hσ V hVinv hVτ
      (by calc (ω ^ 2) ^ 3 = (ω ^ 3) ^ 2 := by ring
        _ = 1 := by rw [hω3, one_pow]) hω2ne1
  have hdim : Module.finrank K U + Module.finrank K V = Module.finrank K W :=
    Submodule.finrank_add_eq_of_isCompl hc
  rw [← hdim]
  exact Nat.dvd_add hdU hdV

private theorem three_dvd_of_nonsplit {K W Λ : Type*} [Field K] [AddCommGroup W]
    [Module K W] [FiniteDimensional K W] [Group Λ] (hΛ : Group.IsPerfect Λ)
    (ρ : Representation K Λ W) (σ : Λ) (τ : Module.End K W) (hσ : ρ σ = τ)
    (hτ : τ ^ 2 + τ + 1 = 0) (hcomm : ∀ g : Λ, Commute (ρ g) τ)
    (h3 : (3 : K) ≠ 0) (hno : ∀ ω : K, ω ^ 2 + ω + 1 ≠ 0) :
    3 ∣ Module.finrank K W := by
  let p : K[X] := X ^ 2 + X + 1
  have hp_deg : p.natDegree = 2 := by
    dsimp only [p]
    compute_degree!
  have hp_ne : p ≠ 0 := by
    intro h
    rw [h] at hp_deg
    simp at hp_deg
  have hp_irr : Irreducible p := by
    apply Polynomial.irreducible_of_degree_le_three_of_not_isRoot
    · rw [hp_deg]; decide
    · intro r hr
      apply hno r
      simpa [p, IsRoot] using hr
  haveI : Fact (Irreducible p) := ⟨hp_irr⟩
  let E := K[X] ⧸ Ideal.span {p}
  haveI : (Ideal.span {p}).IsMaximal := AdjoinRoot.span_maximal_of_irreducible
  letI : Field E := Ideal.Quotient.field _
  have hpτ : aeval τ p = 0 := by
    simpa [p] using hτ
  let ψ : K[X] →+* Module.End K W := (aeval τ).toRingHom
  have hψ : ∀ q ∈ Ideal.span {p}, ψ q = 0 := by
    intro q hq
    obtain ⟨r, rfl⟩ := Ideal.mem_span_singleton'.1 hq
    rw [map_mul]
    have hpψ : ψ p = 0 := by simpa [ψ] using hpτ
    rw [hpψ, mul_zero]
  let φring : E →+* Module.End K W := Ideal.Quotient.lift (Ideal.span {p}) ψ hψ
  have hφring_mk : ∀ q : K[X],
      φring (Ideal.Quotient.mk (Ideal.span {p}) q) = aeval τ q := by
    intro q
    exact Ideal.Quotient.lift_mk (Ideal.span {p}) (a := q) ψ hψ
  letI : Module E W := Module.compHom W φring
  have hφring_C : ∀ r : K, φring (algebraMap K E r) =
      algebraMap K (Module.End K W) r := by
    intro r
    change φring (Ideal.Quotient.mk (Ideal.span {p}) (Polynomial.C r)) =
      algebraMap K (Module.End K W) r
    rw [hφring_mk]
    simp [ψ]
  haveI : IsScalarTower K E W := ⟨fun r x m => by
    change φring (r • x) m = r • φring x m
    have hsm : r • x = algebraMap K E r * x := Algebra.smul_def r x
    rw [hsm, map_mul, hφring_C]
    rfl⟩
  haveI : FiniteDimensional E W := Module.Finite.of_restrictScalars_finite K E W
  haveI : FiniteDimensional K E := (AdjoinRoot.powerBasis hp_ne).finite
  have hE2 : Module.finrank K E = 2 := by
    rw [show Module.finrank K E = Module.finrank K (AdjoinRoot p) from rfl]
    rw [(AdjoinRoot.powerBasis hp_ne).finrank, AdjoinRoot.powerBasis_dim, hp_deg]
  have hdim : Module.finrank K E * Module.finrank E W = Module.finrank K W :=
    Module.finrank_mul_finrank K E W
  rw [hE2] at hdim
  have hElin : ∀ g : Λ, ∀ c : E, ∀ w : W, ρ g (c • w) = c • ρ g w := by
    intro g c w
    induction c using AdjoinRoot.induction_on with
    | ih q =>
      change ρ g ((Ideal.Quotient.mk (Ideal.span {p}) q) • w) =
        (Ideal.Quotient.mk (Ideal.span {p}) q) • ρ g w
      have hsmul : ∀ x : W,
          (Ideal.Quotient.mk (Ideal.span {p}) q : E) • x = (aeval τ q) x := by
        intro x
        change φring (Ideal.Quotient.mk (Ideal.span {p}) q) x = (aeval τ q) x
        rw [hφring_mk]
      have hcommq : Commute (ρ g) (aeval τ q) := by
        have hmem : aeval τ q ∈ Algebra.adjoin K ({τ} : Set (Module.End K W)) :=
          Polynomial.aeval_mem_adjoin_singleton K τ
        exact Algebra.commute_of_mem_adjoin_singleton_of_commute hmem (hcomm g)
      calc ρ g ((Ideal.Quotient.mk (Ideal.span {p}) q : E) • w)
          = ρ g ((aeval τ q) w) := by rw [hsmul]
        _ = (ρ g * aeval τ q) w := by rw [Module.End.mul_apply]
        _ = (aeval τ q * ρ g) w := by rw [hcommq.eq]
        _ = (aeval τ q) (ρ g w) := by rw [Module.End.mul_apply]
        _ = (Ideal.Quotient.mk (Ideal.span {p}) q : E) • ρ g w := by rw [hsmul]
  let ρE : Representation E Λ W :=
    { toFun := fun g =>
        { toFun := fun w => ρ g w
          map_add' := fun x y => (ρ g).map_add x y
          map_smul' := hElin g }
      map_one' := by
        ext w
        simpa using congrArg (fun f : Module.End K W => f w) (map_one ρ)
      map_mul' := by
        intro g h
        ext w
        simpa [Module.End.mul_apply] using
          congrArg (fun f : Module.End K W => f w) (map_mul ρ g h) }
  have hτE : (ρE σ) ^ 2 + ρE σ + 1 = 0 := by
    ext w
    have h := congrArg (fun f : Module.End K W => f w) hτ
    simpa [Module.End.mul_apply, pow_two, ρE, hσ] using h
  have hcommE : ∀ g : Λ, Commute (ρE g) (ρE σ) := by
    intro g
    ext w
    have h := congrArg (fun f : Module.End K W => f w) (hcomm g).eq
    simpa [Module.End.mul_apply, ρE, hσ] using h
  have h3E : (3 : E) ≠ 0 := by
    intro h
    apply h3
    have h' : algebraMap K E (3 : K) = 0 := by
      rw [map_ofNat]
      exact h
    exact (FaithfulSMul.algebraMap_eq_zero_iff K E).mp h'
  have hα : (AdjoinRoot.root p) ^ 2 + AdjoinRoot.root p + 1 = 0 := by
    have := AdjoinRoot.eval₂_root p
    simpa [p] using this
  have hdivE : 3 ∣ Module.finrank E W :=
    three_dvd_of_root hΛ ρE σ (ρE σ) rfl hτE hcommE h3E (ω := AdjoinRoot.root p) hα
  have : 3 ∣ 2 * Module.finrank E W := dvd_mul_of_dvd_right hdivE 2
  rwa [hdim] at this

theorem three_dvd_finrank_of_isPerfect (h3 : (3 : K) ≠ 0) [FiniteDimensional K V]
    (ρ : Representation K Γ V) {Λ : Subgroup Γ} (hΛ : Group.IsPerfect Λ) (W : Submodule K V)
    (hW : ∀ g ∈ Λ, ∀ w ∈ W, ρ g w ∈ W) {σ : Γ} (hσΛ : σ ∈ Λ)
    (hσ : ∀ g ∈ Λ, ρ σ * ρ g = ρ g * ρ σ) (hσ3 : ∀ w ∈ W, ρ σ (ρ σ w) + ρ σ w + w = 0) :
    3 ∣ Module.finrank K W := by
  let ρΛ : Representation K Λ V := ρ.comp Λ.subtype
  let S : Subrepresentation ρΛ :=
    Subrepresentation.mk W (fun g w hw => hW (g : Γ) g.2 w hw)
  let τ : Module.End K W := S.toRepresentation ⟨σ, hσΛ⟩
  have hcoe : ∀ (g : Λ) (u : W), ((S.toRepresentation g) u : V) = ρ (g : Γ) (u : V) := by
    intro g u
    have hwW : S.toRepresentation g u =
        ⟨ρ (g : Γ) (u : V), hW (g : Γ) g.2 (u : V) u.2⟩ := by
      rw [Subrepresentation.toRepresentation_apply_coe]
      rfl
    rw [hwW]
  have hτ : τ ^ 2 + τ + 1 = 0 := by
    ext w
    have h1 := hcoe ⟨σ, hσΛ⟩ w
    have h2 := hcoe ⟨σ, hσΛ⟩ ((S.toRepresentation ⟨σ, hσΛ⟩) w)
    simpa [τ, Module.End.mul_apply, pow_two, h1, h2] using hσ3 (w : V) w.2
  have hcomm : ∀ g : Λ, Commute (S.toRepresentation g) τ := by
    intro g
    ext w
    have h1 := hcoe g w
    have h2 := hcoe ⟨σ, hσΛ⟩ w
    have h3' := hcoe g ((S.toRepresentation ⟨σ, hσΛ⟩) w)
    have h4 := hcoe ⟨σ, hσΛ⟩ ((S.toRepresentation g) w)
    have h := congrArg (fun f : Module.End K V => f (w : V)) (hσ (g : Γ) g.2)
    simpa [τ, Module.End.mul_apply, h1, h2, h3', h4] using h.symm
  by_cases hsplit : ∃ ω : K, ω ^ 2 + ω + 1 = 0
  · obtain ⟨ω, hω⟩ := hsplit
    exact three_dvd_of_root hΛ S.toRepresentation ⟨σ, hσΛ⟩ τ rfl hτ hcomm h3 hω
  · exact three_dvd_of_nonsplit hΛ S.toRepresentation ⟨σ, hσΛ⟩ τ rfl hτ hcomm h3
      (fun ω hω => hsplit ⟨ω, hω⟩)

theorem finrank_eq_add_of_eq_neg_one (h2 : (2 : K) ≠ 0) [FiniteDimensional K V]
    {x z : V →ₗ[K] V} (hx : x * x = 1) (hz : z = -1) :
    Module.finrank K V =
      Module.finrank K (LinearMap.ker (x - 1)) + Module.finrank K (LinearMap.ker (x * z - 1)) := by
  have hc := isCompl_ker_sub_one_ker_add_one h2 x hx
  have hker : LinearMap.ker (x * z - 1) = LinearMap.ker (x + 1) := by
    rw [hz]
    have h : x * (-1 : V →ₗ[K] V) - 1 = -(x + 1) := by
      ext v
      simp
      abel
    rw [h, LinearMap.ker_neg]
  rw [hker]
  exact (Submodule.finrank_add_eq_of_isCompl hc).symm

end CFSG.RankThree.PartTwo.J2Residue

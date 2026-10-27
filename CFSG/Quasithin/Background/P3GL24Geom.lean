module

public import CFSG.Quasithin.Background.P3GL24A5
public import Mathlib.Algebra.Module.StablyFree.Basic
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card
public import Mathlib.LinearAlgebra.Projectivization.Action
public import Mathlib.LinearAlgebra.Projectivization.Cardinality
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat

public section

namespace CFSG.Quasithin

namespace G11

namespace G118

open scoped LinearAlgebra.Projectivization
open Equiv

section

variable {F : Type} [Field F] {U : Type} [AddCommGroup U] [Module F U]

@[expose] noncomputable def gl24Rho : (U ≃ₗ[F] U) →* Perm (ℙ F U) :=
  MulAction.toPermHom (U ≃ₗ[F] U) (ℙ F U)

theorem gl24Rho_mk (g : U ≃ₗ[F] U) (u : U) (hu : u ≠ 0) :
    gl24Rho g (Projectivization.mk F u hu) =
      Projectivization.mk F (g u) (by simpa using hu) := rfl

theorem gl24Rho_eq_one_iff (g : U ≃ₗ[F] U) :
    gl24Rho g = 1 ↔ ∃ a : F, ∀ u, g u = a • u := by
  constructor
  · intro h
    obtain ⟨a, ha⟩ := (g : U →ₗ[F] U).exists_eq_smul_id_of_forall_notLinearIndependent
      fun v => by
        by_cases hv : v = 0
        · simp [hv, linearIndependent_fin2]
        · have := congrArg (fun p => p (Projectivization.mk F v hv)) h
          simp only [gl24Rho_mk, Perm.one_apply] at this
          rw [Projectivization.mk_eq_mk_iff'] at this
          obtain ⟨b, hb⟩ := this
          rw [LinearIndependent.pair_iff' hv]
          push Not
          exact ⟨b, by simpa using hb⟩
    exact ⟨a, fun u => by simpa using congrArg (fun f : U →ₗ[F] U => f u) ha⟩
  · rintro ⟨a, ha⟩
    ext p
    induction p using Projectivization.ind with | _ v hv =>
    simp only [gl24Rho_mk, Perm.one_apply]
    rw [Projectivization.mk_eq_mk_iff']
    exact ⟨a, by simpa using (ha v).symm⟩

theorem gl24_pow_apply_of_forall (g : U ≃ₗ[F] U) (a : F) (ha : ∀ u, g u = a • u) (n : ℕ)
    (u : U) : (g ^ n) u = a ^ n • u := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, LinearEquiv.mul_apply, ha, map_smul, ih, smul_smul, pow_succ, mul_comm]

theorem gl24_pow_three [Finite F] (hF : Nat.card F = 4) (a : F) (ha : a ≠ 0) : a ^ 3 = 1 := by
  have := Fintype.ofFinite F
  have h := FiniteField.pow_card_sub_one_eq_one a ha
  rwa [← Nat.card_eq_fintype_card, hF] at h

theorem gl24_scalar_ne_zero [Nontrivial U] (g : U ≃ₗ[F] U) (a : F) (ha : ∀ u, g u = a • u) :
    a ≠ 0 := by
  rintro rfl
  obtain ⟨u, hu⟩ := exists_ne (0 : U)
  apply hu
  exact g.injective (by simp [ha])

theorem gl24_ker_pow_three [Nontrivial U] [Finite F] (hF : Nat.card F = 4) (z : U ≃ₗ[F] U)
    (hz : gl24Rho z = 1) : z ^ 3 = 1 := by
  obtain ⟨a, ha⟩ := (gl24Rho_eq_one_iff z).1 hz
  have ha0 : a ≠ 0 := gl24_scalar_ne_zero z a ha
  ext u
  rw [gl24_pow_apply_of_forall z a ha, gl24_pow_three hF a ha0]
  simp

theorem gl24_ker_central (z : U ≃ₗ[F] U) (a : F) (ha : ∀ u, z u = a • u) (g : U ≃ₗ[F] U) :
    g * z = z * g := by
  ext u
  simp [ha]

theorem gl24_cube [Nontrivial U] [Finite F] [Module.Finite F U] (hF : Nat.card F = 4)
    (hU : Module.finrank F U = 2) (g : U ≃ₗ[F] U) (hg : gl24Rho (g ^ 3) = 1) : g ^ 3 = 1 := by
  obtain ⟨a, ha⟩ := (gl24Rho_eq_one_iff (g ^ 3)).1 hg
  have ha0 : a ≠ 0 := gl24_scalar_ne_zero _ a ha
  have ha3 := gl24_pow_three hF a ha0
  have h1 : ((LinearEquiv.det (g ^ 3) : Fˣ) : F) = a ^ 2 := by
    rw [LinearEquiv.coe_det]
    have : ((g ^ 3 : U ≃ₗ[F] U) : U →ₗ[F] U) = a • LinearMap.id := by
      ext u
      simp [ha]
    rw [this, LinearMap.det_smul, LinearMap.det_id, hU, mul_one]
  have hd3 : (LinearEquiv.det g) ^ 3 = 1 := by
    have : Nat.card Fˣ = 3 := by rw [Nat.card_units, hF]
    rw [← this]
    exact pow_card_eq_one'
  have h2 : a ^ 2 = 1 := by
    rw [← h1, map_pow, hd3]
    simp
  have ha1 : a = 1 := by
    calc a = a ^ 3 * (a ^ 2)⁻¹ := by field_simp
      _ = 1 := by rw [ha3, h2]; simp
  ext u
  rw [ha]
  simp [ha1]

theorem gl24_card_gl [Finite F] [Module.Finite F U] (hF : Nat.card F = 4)
    (hU : Module.finrank F U = 2) : Nat.card (U ≃ₗ[F] U) = 180 := by
  have b := Module.finBasisOfFinrankEq F U hU
  let e : (U ≃ₗ[F] U) ≃* GL (Fin 2) F :=
    (LinearMap.GeneralLinearGroup.generalLinearEquiv F U).symm.trans
      (Units.mapEquiv (LinearMap.toMatrixAlgEquiv b).toMulEquiv)
  rw [Nat.card_congr e.toEquiv]
  have := Fintype.ofFinite F
  rw [Matrix.card_GL_field, ← Nat.card_eq_fintype_card, hF]
  decide

theorem gl24_card_ker [Nontrivial U] [Finite F] (hF : Nat.card F = 4) :
    Nat.card (gl24Rho : (U ≃ₗ[F] U) →* Perm (ℙ F U)).ker = 3 := by
  have hsm : ∀ (a : Fˣ) (u : U), (LinearEquiv.smulOfUnit a : U ≃ₗ[F] U) u = (a : F) • u :=
    fun a u => rfl
  let Φ : Fˣ → (gl24Rho : (U ≃ₗ[F] U) →* Perm (ℙ F U)).ker := fun a =>
    ⟨LinearEquiv.smulOfUnit a, (gl24Rho_eq_one_iff _).2 ⟨a, hsm a⟩⟩
  have hbij : Function.Bijective Φ := by
    constructor
    · intro a b hab
      obtain ⟨u, hu⟩ := exists_ne (0 : U)
      have h := congrArg (fun g : (gl24Rho : (U ≃ₗ[F] U) →* Perm (ℙ F U)).ker =>
        (g : U ≃ₗ[F] U) u) hab
      simp only [Φ, hsm] at h
      exact Units.ext (smul_left_injective F hu h)
    · rintro ⟨g, hg⟩
      obtain ⟨a, ha⟩ := (gl24Rho_eq_one_iff g).1 hg
      have ha0 : a ≠ 0 := gl24_scalar_ne_zero g a ha
      refine ⟨Units.mk0 a ha0, Subtype.ext ?_⟩
      ext u
      simp only [Φ, hsm, Units.val_mk0]
      exact (ha u).symm
  rw [← Nat.card_eq_of_bijective Φ hbij, Nat.card_units, hF]

theorem gl24_tau_eq_refl [Module.Finite F U] (hU : Module.finrank F U = 2) (τ : F ≃+* F)
    (σ : U →ₛₗ[(τ : F →+* F)] U) (hσ : Function.Injective σ) (g : U ≃ₗ[F] U)
    (h : ∀ u : U, ∃ b : F, σ u = b • g u) : τ = RingEquiv.refl F := by
  have hψ : ∀ w : U, ∃ b : F, g.symm (σ w) = b • w := by
    intro w
    obtain ⟨b, hb⟩ := h w
    exact ⟨b, by rw [hb, map_smul, g.symm_apply_apply]⟩
  have : Nontrivial U := Module.nontrivial_of_finrank_pos (R := F) (by omega)
  obtain ⟨u, hu⟩ := exists_ne (0 : U)
  obtain ⟨v, hv⟩ :=
    exists_linearIndependent_pair_of_one_lt_finrank (R := F) (M := U) (by omega) hu
  have hpair := LinearIndependent.pair_iff.1 hv
  obtain ⟨l1, h1⟩ := hψ u
  obtain ⟨l2, h2⟩ := hψ v
  obtain ⟨l3, h3⟩ := hψ (u + v)
  have h3' : l1 • u + l2 • v = l3 • u + l3 • v := by
    rw [map_add, map_add, h1, h2, smul_add] at h3
    exact h3
  have e13 : l1 = l3 ∧ l2 = l3 := by
    have := hpair (l1 - l3) (l2 - l3) (by
      calc (l1 - l3) • u + (l2 - l3) • v = (l1 • u + l2 • v) - (l3 • u + l3 • v) := by
            rw [sub_smul, sub_smul]; abel
        _ = 0 := by rw [h3']; exact sub_self _)
    exact ⟨sub_eq_zero.1 this.1, sub_eq_zero.1 this.2⟩
  have hl1 : l1 ≠ 0 := by
    rintro rfl
    apply hu
    rw [zero_smul] at h1
    have h0 : σ u = 0 := g.symm.injective (h1.trans (map_zero g.symm).symm)
    exact hσ (h0.trans (map_zero σ).symm)
  ext c
  obtain ⟨m, hm⟩ := hψ (c • u + v)
  have hm' : (τ c • l1) • u + l2 • v = (m * c) • u + m • v := by
    rw [map_add, map_add, map_smulₛₗ, map_smulₛₗ, h1, h2, smul_smul, smul_add, smul_smul] at hm
    exact hm
  have e := hpair (τ c * l1 - m * c) (l2 - m) (by
    calc (τ c * l1 - m * c) • u + (l2 - m) • v
        = ((τ c • l1) • u + l2 • v) - ((m * c) • u + m • v) := by
          rw [sub_smul, sub_smul, smul_eq_mul]; abel
      _ = 0 := by rw [hm']; exact sub_self _)
  have hmv : m = l1 := by
    have h2m : l2 = m := sub_eq_zero.1 e.2
    rw [← h2m, e13.2, ← e13.1]
  have hc : τ c * l1 = c * l1 := by
    have := sub_eq_zero.1 e.1
    rw [hmv] at this
    rw [this, mul_comm]
  exact mul_right_cancel₀ hl1 hc

theorem gl24_card_proj [Finite F] [Module.Finite F U] (hF : Nat.card F = 4)
    (hU : Module.finrank F U = 2) : Nat.card (ℙ F U) = 5 := by
  rw [Projectivization.card_of_finrank_two F U hU, hF]

@[expose] noncomputable def gl24Rho5 (e : ℙ F U ≃ Fin 5) : (U ≃ₗ[F] U) →* Perm (Fin 5) :=
  e.permCongrHom.toMonoidHom.comp gl24Rho

theorem gl24Rho5_eq_one_iff (e : ℙ F U ≃ Fin 5) (g : U ≃ₗ[F] U) :
    gl24Rho5 e g = 1 ↔ gl24Rho g = 1 := by
  simp only [gl24Rho5, MonoidHom.comp_apply, MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_ofClass]
  exact map_eq_one_iff _ e.permCongrHom.injective

theorem gl24_card_range5 [Nontrivial U] [Finite F] [Module.Finite F U] (hF : Nat.card F = 4)
    (hU : Module.finrank F U = 2) (e : ℙ F U ≃ Fin 5) : Nat.card (gl24Rho5 e).range = 60 := by
  have hker : (gl24Rho5 e).ker = (gl24Rho : (U ≃ₗ[F] U) →* Perm (ℙ F U)).ker := by
    ext g
    simp only [MonoidHom.mem_ker, gl24Rho5_eq_one_iff]
  have h1 := Subgroup.index_ker (gl24Rho5 e)
  have h2 := (gl24Rho5 e).ker.card_mul_index
  rw [hker] at h1 h2
  rw [gl24_card_ker hF, gl24_card_gl hF hU, h1] at h2
  omega

theorem gl24_range5_eq_alt [Nontrivial U] [Finite F] [Module.Finite F U] (hF : Nat.card F = 4)
    (hU : Module.finrank F U = 2) (e : ℙ F U ≃ Fin 5) :
    (gl24Rho5 e).range = alternatingGroup (Fin 5) :=
  gl24_eq_alt_of_card_sixty _ (gl24_card_range5 hF hU e)

theorem gl24Rho5_sign [Nontrivial U] [Finite F] [Module.Finite F U] (hF : Nat.card F = 4)
    (hU : Module.finrank F U = 2) (e : ℙ F U ≃ Fin 5) (g : U ≃ₗ[F] U) :
    Perm.sign (gl24Rho5 e g) = 1 := by
  have : gl24Rho5 e g ∈ (gl24Rho5 e).range := MonoidHom.mem_range.2 ⟨g, rfl⟩
  rw [gl24_range5_eq_alt hF hU e] at this
  exact Perm.mem_alternatingGroup.1 this

@[expose] noncomputable def gl24Sigma {τ : F ≃+* F} (σ : U →ₛₗ[(τ : F →+* F)] U)
    (hσ : Function.Injective σ)
    (hinv : ∀ p : ℙ F U, Projectivization.map σ hσ (Projectivization.map σ hσ p) = p) :
    Perm (ℙ F U) where
  toFun := Projectivization.map σ hσ
  invFun := Projectivization.map σ hσ
  left_inv := hinv
  right_inv := hinv

theorem gl24Sigma_mul_self {τ : F ≃+* F} (σ : U →ₛₗ[(τ : F →+* F)] U)
    (hσ : Function.Injective σ)
    (hinv : ∀ p : ℙ F U, Projectivization.map σ hσ (Projectivization.map σ hσ p) = p) :
    gl24Sigma σ hσ hinv * gl24Sigma σ hσ hinv = 1 := by
  ext p
  exact hinv p

theorem gl24Sigma_conj {τ : F ≃+* F} (σ : U →ₛₗ[(τ : F →+* F)] U)
    (hσ : Function.Injective σ)
    (hinv : ∀ p : ℙ F U, Projectivization.map σ hσ (Projectivization.map σ hσ p) = p)
    (c c' : U ≃ₗ[F] U) (h : ∀ u, c' (σ u) = σ (c u)) :
    gl24Rho c' * gl24Sigma σ hσ hinv = gl24Sigma σ hσ hinv * gl24Rho c := by
  ext p
  induction p using Projectivization.ind with | _ u hu =>
  simp only [Perm.mul_apply, gl24Rho_mk]
  change gl24Rho c' (Projectivization.map σ hσ (Projectivization.mk F u hu)) =
    Projectivization.map σ hσ (gl24Rho c (Projectivization.mk F u hu))
  rw [Projectivization.map_mk, gl24Rho_mk, gl24Rho_mk, Projectivization.map_mk]
  congr 1
  exact h u

theorem gl24_sigma_not_mem_range [Module.Finite F U] (hU : Module.finrank F U = 2)
    {τ : F ≃+* F} (σ : U →ₛₗ[(τ : F →+* F)] U) (hσ : Function.Injective σ)
    (hinv : ∀ p : ℙ F U, Projectivization.map σ hσ (Projectivization.map σ hσ p) = p)
    (hτ : τ ≠ RingEquiv.refl F) :
    gl24Sigma σ hσ hinv ∉ (gl24Rho : (U ≃ₗ[F] U) →* Perm (ℙ F U)).range := by
  rintro ⟨g, hg⟩
  apply hτ
  refine gl24_tau_eq_refl hU τ σ hσ g (fun u => ?_)
  by_cases hu : u = 0
  · exact ⟨0, by simp [hu]⟩
  · have h := congrArg (fun f : Perm (ℙ F U) => f (Projectivization.mk F u hu)) hg
    simp only [gl24Rho_mk] at h
    change Projectivization.mk F (g u) _ =
      Projectivization.map σ hσ (Projectivization.mk F u hu) at h
    rw [Projectivization.map_mk, Projectivization.mk_eq_mk_iff'] at h
    obtain ⟨a, ha⟩ := h
    have ha0 : a ≠ 0 := by
      rintro rfl
      rw [zero_smul] at ha
      exact hu (g.injective (ha.symm.trans (map_zero g).symm))
    exact ⟨a⁻¹, by rw [← ha, smul_smul, inv_mul_cancel₀ ha0, one_smul]⟩

theorem gl24_sigma_sign [Nontrivial U] [Finite F] [Module.Finite F U] (hF : Nat.card F = 4)
    (hU : Module.finrank F U = 2) (e : ℙ F U ≃ Fin 5) {τ : F ≃+* F}
    (σ : U →ₛₗ[(τ : F →+* F)] U) (hσ : Function.Injective σ)
    (hinv : ∀ p : ℙ F U, Projectivization.map σ hσ (Projectivization.map σ hσ p) = p)
    (hτ : τ ≠ RingEquiv.refl F) :
    Perm.sign (e.permCongr (gl24Sigma σ hσ hinv)) = -1 := by
  rcases Int.units_eq_one_or (Perm.sign (e.permCongr (gl24Sigma σ hσ hinv))) with h | h
  · exfalso
    have hmem : e.permCongr (gl24Sigma σ hσ hinv) ∈ alternatingGroup (Fin 5) :=
      Perm.mem_alternatingGroup.2 h
    rw [← gl24_range5_eq_alt hF hU e] at hmem
    obtain ⟨g, hg⟩ := MonoidHom.mem_range.1 hmem
    apply gl24_sigma_not_mem_range hU σ hσ hinv hτ
    exact ⟨g, e.permCongrHom.injective hg⟩
  · exact h

end

end G118

end G11

end CFSG.Quasithin

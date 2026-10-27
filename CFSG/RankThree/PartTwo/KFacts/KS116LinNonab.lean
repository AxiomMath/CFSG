module

public import Mathlib.LinearAlgebra.Center
public import CFSG.RankThree.PartTwo.KFacts.KS116LinRep

public section

namespace CFSG.RankThree.PartTwo.KFacts.NDC

section ScalarCommutator

open Representation
open scoped commutatorElement

section Rep

variable {F : Type*} [Field F] {G : Type*} [Group G] {V : Type*} [AddCommGroup V] [Module F V]

private theorem ndcF_eq_zero_of_smul_eq_zero_isUnit [Nontrivial V] {w : V →ₗ[F] V}
    (hw : IsUnit w) {c : F} (h : c • w = 0) : c = 0 := by
  have h1 : (c • (1 : V →ₗ[F] V)) * w = 0 * w := by
    rw [smul_mul_assoc, one_mul, zero_mul, h]
  have h2 : c • (1 : V →ₗ[F] V) = 0 := hw.mul_right_cancel h1
  obtain ⟨x, hx⟩ := exists_ne (0 : V)
  have h3 := congrArg (fun f : V →ₗ[F] V => f x) h2
  simp only [LinearMap.smul_apply, Module.End.one_apply, LinearMap.zero_apply] at h3
  exact (smul_eq_zero.mp h3).resolve_right hx

theorem commutant_anticomm_scalar [Module.Finite F V] (h2 : (2 : F) ≠ 0)
    (hd : Module.finrank F V = 2) (u v : V →ₗ[F] V) (hu : IsUnit u) (hv : IsUnit v)
    (huv : u * v = -(v * u)) (φ : V →ₗ[F] V) (hφu : φ * u = u * φ) (hφv : φ * v = v * φ) :
    ∃ c : F, φ = c • (1 : V →ₗ[F] V) := by
  haveI : Nontrivial V := Module.nontrivial_of_finrank_pos (R := F) (by rw [hd]; norm_num)
  have hnotscalar : ∀ a : F, u ≠ a • (1 : V →ₗ[F] V) := by
    intro a ha
    rw [ha] at huv hu
    simp only [smul_mul_assoc, one_mul, mul_smul_comm, mul_one] at huv
    have key : (2 * a) • v = 0 := by
      rw [two_mul, add_smul]
      calc a • v + a • v = a • v + -(a • v) := by rw [← huv]
        _ = 0 := add_neg_cancel _
    have ha0 : a = 0 := by
      rcases mul_eq_zero.mp (ndcF_eq_zero_of_smul_eq_zero_isUnit hv key) with h | h
      · exact absurd h h2
      · exact h
    rw [ha0, zero_smul] at hu
    exact hu.ne_zero rfl
  obtain ⟨m, hm⟩ : ∃ m : V, LinearIndependent F ![m, u m] := by
    by_contra hcon
    simp only [not_exists] at hcon
    obtain ⟨a, ha⟩ := LinearMap.exists_eq_smul_id_of_forall_notLinearIndependent (f := u) hcon
    exact hnotscalar a ha
  have hcard : Fintype.card (Fin 2) = Module.finrank F V := by
    rw [Fintype.card_fin, hd]
  obtain ⟨B, hB⟩ : ∃ B : Module.Basis (Fin 2) F V, ⇑B = ![m, u m] :=
    ⟨basisOfLinearIndependentOfCardEqFinrank hm hcard,
      coe_basisOfLinearIndependentOfCardEqFinrank hm hcard⟩
  have hB0 : B 0 = m := by simp [hB]
  have hB1 : B 1 = u m := by simp [hB]
  obtain ⟨a, b, hφm⟩ : ∃ a b : F, φ m = a • m + b • u m := by
    have hsum := B.sum_repr (φ m)
    rw [Fin.sum_univ_two, hB0, hB1] at hsum
    exact ⟨B.repr (φ m) 0, B.repr (φ m) 1, hsum.symm⟩
  have hφum : φ (u m) = a • u m + b • u (u m) := by
    have h1 : φ (u m) = u (φ m) := by
      have h := congrArg (fun f : V →ₗ[F] V => f m) hφu
      simpa only [Module.End.mul_apply] using h
    rw [h1, hφm, map_add, map_smul, map_smul]
  have hφeq : φ = a • (1 : V →ₗ[F] V) + b • u := by
    apply B.ext
    intro i
    fin_cases i
    · simp [hB0, hφm]
    · simp [hB1, hφum]
  rw [hφeq] at hφv
  simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm, one_mul, mul_one] at hφv
  have hbuv : b • (u * v) = b • (v * u) := add_left_cancel hφv
  have hvu : v * u = -(u * v) := by rw [huv, neg_neg]
  rw [hvu, smul_neg] at hbuv
  have key : (2 * b) • (u * v) = 0 := by
    rw [two_mul, add_smul]
    calc b • (u * v) + b • (u * v) = b • (u * v) + -(b • (u * v)) := by rw [← hbuv]
      _ = 0 := add_neg_cancel _
  have hb0 : b = 0 := by
    rcases mul_eq_zero.mp (ndcF_eq_zero_of_smul_eq_zero_isUnit (hu.mul hv) key) with h | h
    · exact absurd h h2
    · exact h
  exact ⟨a, by rw [hφeq, hb0, zero_smul, add_zero]⟩

theorem commutator_scalar_pow_finrank [Module.Finite F V] (ρ : Representation F G V) (x y : G)
    (c : F) (hc : ρ ⁅x, y⁆ = c • (1 : V →ₗ[F] V)) : c ^ Module.finrank F V = 1 := by
  have hinv : ∀ z : G, LinearMap.det (ρ z) * LinearMap.det (ρ z⁻¹) = 1 := by
    intro z
    rw [← map_mul LinearMap.det, ← map_mul ρ, mul_inv_cancel, map_one, map_one]
  have hdet : LinearMap.det (ρ ⁅x, y⁆) = 1 := by
    have e : LinearMap.det (ρ ⁅x, y⁆) = (LinearMap.det (ρ x) * LinearMap.det (ρ x⁻¹)) *
        (LinearMap.det (ρ y) * LinearMap.det (ρ y⁻¹)) := by
      simp only [commutatorElement_def, map_mul]
      ring
    rw [e, hinv x, hinv y, one_mul]
  have h1 : LinearMap.det (c • (1 : V →ₗ[F] V)) = c ^ Module.finrank F V := by
    rw [LinearMap.det_smul, map_one, mul_one]
  rw [← h1, ← hc]
  exact hdet

theorem three_dvd_orderOf_commutator [Module.Finite F V] (hd : Module.finrank F V = 3)
    (ρ : Representation F G V) (x y : G) (c : F) (hc : ρ ⁅x, y⁆ = c • (1 : V →ₗ[F] V))
    (hne : ρ x * ρ y ≠ ρ y * ρ x) : 3 ∣ orderOf ⁅x, y⁆ := by
  haveI : Nontrivial V := Module.nontrivial_of_finrank_pos (R := F) (by rw [hd]; norm_num)
  have hpow : c ^ 3 = 1 := by
    have h := commutator_scalar_pow_finrank ρ x y c hc
    rwa [hd] at h
  have hc1 : c ≠ 1 := by
    intro h1
    apply hne
    rw [h1, one_smul] at hc
    simp only [commutatorElement_def, map_mul] at hc
    have hCA : ρ x⁻¹ * ρ x = 1 := by rw [← map_mul ρ, inv_mul_cancel, map_one]
    have hDB : ρ y⁻¹ * ρ y = 1 := by rw [← map_mul ρ, inv_mul_cancel, map_one]
    have hABC : ρ x * ρ y * ρ x⁻¹ = ρ y := by
      calc ρ x * ρ y * ρ x⁻¹ = ρ x * ρ y * ρ x⁻¹ * (ρ y⁻¹ * ρ y) := by rw [hDB, mul_one]
        _ = (ρ x * ρ y * ρ x⁻¹ * ρ y⁻¹) * ρ y := by simp only [mul_assoc]
        _ = ρ y := by rw [hc, one_mul]
    calc ρ x * ρ y = ρ x * ρ y * (ρ x⁻¹ * ρ x) := by rw [hCA, mul_one]
      _ = (ρ x * ρ y * ρ x⁻¹) * ρ x := by simp only [mul_assoc]
      _ = ρ y * ρ x := by rw [hABC]
  have hord : orderOf c = 3 := orderOf_eq_prime hpow hc1
  have hgpow : ρ (⁅x, y⁆ ^ orderOf ⁅x, y⁆) = 1 := by
    rw [pow_orderOf_eq_one, map_one]
  rw [map_pow, hc, smul_pow, one_pow] at hgpow
  have hcn : c ^ orderOf ⁅x, y⁆ = 1 := by
    have h2 : (c ^ orderOf ⁅x, y⁆ - 1) • (1 : V →ₗ[F] V) = 0 := by
      rw [sub_smul, hgpow, one_smul, sub_self]
    have h3 := ndcF_eq_zero_of_smul_eq_zero_isUnit isUnit_one h2
    exact sub_eq_zero.mp h3
  have hdvd := orderOf_dvd_of_pow_eq_one hcn
  rw [hord] at hdvd
  exact hdvd

end Rep

end ScalarCommutator

section NonabelianPlane

open Representation
open scoped commutatorElement

section Rep

variable {F : Type*} [Field F] {G : Type*} [Group G] {V : Type*} [AddCommGroup V] [Module F V]

private theorem nab2_rel (ρ : Representation F G V) (a b : G) (c : F)
    (h : ρ ⁅a, b⁆ = c • (1 : V →ₗ[F] V)) : ρ a * ρ b = c • (ρ b * ρ a) := by
  have h' : ρ a * ρ b * ρ a⁻¹ * ρ b⁻¹ = c • (1 : V →ₗ[F] V) := by
    rw [← h, commutatorElement_def, map_mul, map_mul, map_mul]
  have haa : ρ a⁻¹ * ρ a = 1 := by rw [← map_mul, inv_mul_cancel, map_one]
  have hbb : ρ b⁻¹ * ρ b = 1 := by rw [← map_mul, inv_mul_cancel, map_one]
  calc ρ a * ρ b = ρ a * ρ b * ρ a⁻¹ * ρ b⁻¹ * (ρ b * ρ a) := by
        rw [mul_assoc (ρ a * ρ b * ρ a⁻¹) (ρ b⁻¹) (ρ b * ρ a),
          ← mul_assoc (ρ b⁻¹) (ρ b) (ρ a), hbb, one_mul,
          mul_assoc (ρ a * ρ b) (ρ a⁻¹) (ρ a), haa, mul_one]
    _ = c • (ρ b * ρ a) := by rw [h', smul_mul_assoc, one_mul]

private theorem nab2_sq (hd : Module.finrank F V = 2) [Module.Finite F V]
    (ρ : Representation F G V) (a b : G) (c : F) (h : ρ ⁅a, b⁆ = c • (1 : V →ₗ[F] V)) :
    c * c = 1 := by
  have h2 := commutator_scalar_pow_finrank ρ a b c h
  rw [hd, pow_two] at h2
  exact h2

private theorem nab2_anti_inv {a b ai : V →ₗ[F] V} (ha : a * ai = 1) (hai : ai * a = 1)
    (hab : a * b = -(b * a)) : ai * b = -(b * ai) := by
  have hba : b * a = -(a * b) := by rw [hab, neg_neg]
  calc ai * b = ai * (b * (a * ai)) := by rw [ha, mul_one]
    _ = ai * ((b * a) * ai) := by rw [mul_assoc b a ai]
    _ = ai * (-(a * b) * ai) := by rw [hba]
    _ = -(ai * ((a * b) * ai)) := by rw [neg_mul, mul_neg]
    _ = -((ai * a) * (b * ai)) := by simp only [mul_assoc]
    _ = -(b * ai) := by rw [hai, one_mul]

private theorem nab2_twist {w u v mi : V →ₗ[F] V} {c₁ c₂ ε₁ ε₂ : F}
    (hwu : w * u = c₁ • (u * w)) (hwv : w * v = c₂ • (v * w))
    (hmu : mi * u = ε₁ • (u * mi)) (hmv : mi * v = ε₂ • (v * mi))
    (h₁ : ε₁ * c₁ = 1) (h₂ : ε₂ * c₂ = 1) :
    w * mi * u = u * (w * mi) ∧ w * mi * v = v * (w * mi) := by
  constructor
  · calc w * mi * u = w * (mi * u) := mul_assoc _ _ _
      _ = ε₁ • (w * (u * mi)) := by rw [hmu, mul_smul_comm]
      _ = ε₁ • ((w * u) * mi) := by rw [mul_assoc]
      _ = ε₁ • ((c₁ • (u * w)) * mi) := by rw [hwu]
      _ = (ε₁ * c₁) • (u * (w * mi)) := by rw [smul_mul_assoc, smul_smul, mul_assoc]
      _ = u * (w * mi) := by rw [h₁, one_smul]
  · calc w * mi * v = w * (mi * v) := mul_assoc _ _ _
      _ = ε₂ • (w * (v * mi)) := by rw [hmv, mul_smul_comm]
      _ = ε₂ • ((w * v) * mi) := by rw [mul_assoc]
      _ = ε₂ • ((c₂ • (v * w)) * mi) := by rw [hwv]
      _ = (ε₂ * c₂) • (v * (w * mi)) := by rw [smul_mul_assoc, smul_smul, mul_assoc]
      _ = v * (w * mi) := by rw [h₂, one_smul]

private theorem nab2_decomp [Module.Finite F V] (h2 : (2 : F) ≠ 0) (hd : Module.finrank F V = 2)
    {u v ui vi w : V →ₗ[F] V} (hu : u * ui = 1) (hui : ui * u = 1) (hv : v * vi = 1)
    (hvi : vi * v = 1) (huv : u * v = -(v * u)) {c₁ c₂ : F} (hc₁ : c₁ * c₁ = 1)
    (hc₂ : c₂ * c₂ = 1) (hwu : w * u = c₁ • (u * w)) (hwv : w * v = c₂ • (v * w)) :
    ∃ s : F, w = s • (1 : V →ₗ[F] V) ∨ w = s • u ∨ w = s • v ∨ w = s • (u * v) := by
  have hUu : IsUnit u := isUnit_iff_exists.mpr ⟨ui, hu, hui⟩
  have hUv : IsUnit v := isUnit_iff_exists.mpr ⟨vi, hv, hvi⟩
  have hvu : v * u = -(u * v) := by rw [huv, neg_neg]
  have F1 : ui * v = -(v * ui) := nab2_anti_inv hu hui huv
  have F2 : vi * u = -(u * vi) := nab2_anti_inv hv hvi hvu
  have huvi : u * vi = -(vi * u) := by rw [F2, neg_neg]
  rcases mul_self_eq_one_iff.mp hc₁ with rfl | rfl <;>
    rcases mul_self_eq_one_iff.mp hc₂ with rfl | rfl
  · have hwu' : w * u = u * w := by rw [hwu, one_smul]
    have hwv' : w * v = v * w := by rw [hwv, one_smul]
    obtain ⟨s, hs⟩ := commutant_anticomm_scalar h2 hd u v hUu hUv huv w hwu' hwv'
    exact ⟨s, Or.inl hs⟩
  · have hmu : ui * u = (1 : F) • (u * ui) := by rw [one_smul, hui, hu]
    have hmv : ui * v = (-1 : F) • (v * ui) := by rw [F1, neg_one_smul]
    obtain ⟨hcu, hcv⟩ := nab2_twist hwu hwv hmu hmv (by norm_num) (by norm_num)
    obtain ⟨s, hs⟩ := commutant_anticomm_scalar h2 hd u v hUu hUv huv (w * ui) hcu hcv
    have hw : w = s • u := by
      calc w = (w * ui) * u := by rw [mul_assoc, hui, mul_one]
        _ = (s • (1 : V →ₗ[F] V)) * u := by rw [hs]
        _ = s • u := by rw [smul_mul_assoc, one_mul]
    exact ⟨s, Or.inr (Or.inl hw)⟩
  · have hmu : vi * u = (-1 : F) • (u * vi) := by rw [F2, neg_one_smul]
    have hmv : vi * v = (1 : F) • (v * vi) := by rw [one_smul, hvi, hv]
    obtain ⟨hcu, hcv⟩ := nab2_twist hwu hwv hmu hmv (by norm_num) (by norm_num)
    obtain ⟨s, hs⟩ := commutant_anticomm_scalar h2 hd u v hUu hUv huv (w * vi) hcu hcv
    have hw : w = s • v := by
      calc w = (w * vi) * v := by rw [mul_assoc, hvi, mul_one]
        _ = (s • (1 : V →ₗ[F] V)) * v := by rw [hs]
        _ = s • v := by rw [smul_mul_assoc, one_mul]
    exact ⟨s, Or.inr (Or.inr (Or.inl hw))⟩
  · have G1 : u * (vi * ui) = -vi := by
      calc u * (vi * ui) = (u * vi) * ui := by rw [mul_assoc]
        _ = (-(vi * u)) * ui := by rw [huvi]
        _ = -(vi * (u * ui)) := by rw [neg_mul, mul_assoc]
        _ = -vi := by rw [hu, mul_one]
    have G2 : (vi * ui) * u = vi := by rw [mul_assoc, hui, mul_one]
    have G3 : v * (vi * ui) = ui := by rw [← mul_assoc, hv, one_mul]
    have G4 : (vi * ui) * v = -ui := by
      calc (vi * ui) * v = vi * (ui * v) := by rw [mul_assoc]
        _ = vi * (-(v * ui)) := by rw [F1]
        _ = -((vi * v) * ui) := by rw [mul_neg, ← mul_assoc]
        _ = -ui := by rw [hvi, one_mul]
    have hmu : (vi * ui) * u = (-1 : F) • (u * (vi * ui)) := by
      rw [G1, neg_one_smul, neg_neg, G2]
    have hmv : (vi * ui) * v = (-1 : F) • (v * (vi * ui)) := by
      rw [G3, neg_one_smul, G4]
    obtain ⟨hcu, hcv⟩ := nab2_twist hwu hwv hmu hmv (by norm_num) (by norm_num)
    obtain ⟨s, hs⟩ := commutant_anticomm_scalar h2 hd u v hUu hUv huv (w * (vi * ui)) hcu hcv
    have hprod : vi * ui * (u * v) = 1 := by
      rw [mul_assoc, ← mul_assoc ui u v, hui, one_mul, hvi]
    have hw : w = s • (u * v) := by
      calc w = (w * (vi * ui)) * (u * v) := by rw [mul_assoc, hprod, mul_one]
        _ = (s • (1 : V →ₗ[F] V)) * (u * v) := by rw [hs]
        _ = s • (u * v) := by rw [smul_mul_assoc, one_mul]
    exact ⟨s, Or.inr (Or.inr (Or.inr hw))⟩

private theorem nab2_move {z A B : V →ₗ[F] V} {c d : F} (hA : A * z = c • (z * A))
    (hB : B * z = d • (z * B)) : A * B * z = (c * d) • (z * (A * B)) := by
  calc A * B * z = A * (B * z) := by rw [mul_assoc]
    _ = A * (d • (z * B)) := by rw [hB]
    _ = d • (A * (z * B)) := by rw [mul_smul_comm]
    _ = d • ((A * z) * B) := by rw [mul_assoc]
    _ = d • ((c • (z * A)) * B) := by rw [hA]
    _ = d • (c • ((z * A) * B)) := by rw [smul_mul_assoc]
    _ = (d * c) • ((z * A) * B) := by rw [smul_smul]
    _ = (c * d) • (z * (A * B)) := by rw [mul_comm d c, mul_assoc]

private theorem nab2_slide {z P Q Pi Qi : V →ₗ[F] V} (hz : z ≠ 0) (hPP : P * Pi = 1)
    (hQQ : Q * Qi = 1) {s₁ s₂ s₃ s₄ : F} (h₁ : P * z = s₁ • (z * P))
    (h₂ : Q * z = s₂ • (z * Q)) (h₃ : Pi * z = s₃ • (z * Pi)) (h₄ : Qi * z = s₄ • (z * Qi)) :
    P * Q * Pi * Qi * z = z * (P * Q * Pi * Qi) := by
  have e₁ : s₁ * s₃ = 1 := by
    have h := nab2_move h₁ h₃
    rw [hPP, one_mul, mul_one] at h
    have h0 : (s₁ * s₃ - 1) • z = 0 := by rw [sub_smul, one_smul, ← h, sub_self]
    exact sub_eq_zero.mp ((smul_eq_zero.mp h0).resolve_right hz)
  have e₂ : s₂ * s₄ = 1 := by
    have h := nab2_move h₂ h₄
    rw [hQQ, one_mul, mul_one] at h
    have h0 : (s₂ * s₄ - 1) • z = 0 := by rw [sub_smul, one_smul, ← h, sub_self]
    exact sub_eq_zero.mp ((smul_eq_zero.mp h0).resolve_right hz)
  have hsc : s₁ * s₂ * s₃ * s₄ = 1 := by
    have : s₁ * s₂ * s₃ * s₄ = (s₁ * s₃) * (s₂ * s₄) := by ring
    rw [this, e₁, e₂, mul_one]
  have m₁ := nab2_move h₁ h₂
  have m₂ := nab2_move m₁ h₃
  have m₃ := nab2_move m₂ h₄
  rw [m₃, hsc, one_smul]

private abbrev nab2_cls (z : V →ₗ[F] V) : Set (V →ₗ[F] V) :=
  {t | ∃ s : F, s ≠ 0 ∧ t = s • z}

private theorem nab2_mem_cls_self (z : V →ₗ[F] V) : z ∈ nab2_cls z :=
  ⟨1, one_ne_zero, by simp⟩

private theorem nab2_cls_smul {s : F} (hs : s ≠ 0) (z : V →ₗ[F] V) :
    nab2_cls (s • z) = nab2_cls z := by
  ext t
  constructor
  · rintro ⟨r, hr, rfl⟩
    exact ⟨r * s, mul_ne_zero hr hs, by rw [smul_smul]⟩
  · rintro ⟨r, hr, rfl⟩
    refine ⟨r * s⁻¹, mul_ne_zero hr (inv_ne_zero hs), ?_⟩
    rw [smul_smul, mul_assoc, inv_mul_cancel₀ hs, mul_one]

private theorem nab2_image_cls (P Pi z : V →ₗ[F] V) :
    (fun t => P * t * Pi) '' nab2_cls z = nab2_cls (P * z * Pi) := by
  ext t
  constructor
  · rintro ⟨t', ⟨s, hs, rfl⟩, rfl⟩
    exact ⟨s, hs, by simp only [mul_smul_comm, smul_mul_assoc]⟩
  · rintro ⟨s, hs, rfl⟩
    exact ⟨s • z, ⟨s, hs, rfl⟩, by simp only [mul_smul_comm, smul_mul_assoc]⟩

private theorem nab2_ne_zero [Nontrivial V] {w w' : V →ₗ[F] V} (h : w * w' = 1) : w ≠ 0 := by
  rintro rfl
  rw [zero_mul] at h
  exact zero_ne_one h

private abbrev nab2_ClsSet (ρ : Representation F G V) (B : Subgroup G) : Type _ :=
  {C : Set (V →ₗ[F] V) // ∃ b ∈ B, (¬ ∃ c : F, ρ b = c • (1 : V →ₗ[F] V)) ∧ C = nab2_cls (ρ b)}

private def nab2_conj (ρ : Representation F G V) (B : Subgroup G) [B.Normal] (g : G)
    (s : nab2_ClsSet ρ B) : nab2_ClsSet ρ B :=
  ⟨(fun t => ρ g * t * ρ g⁻¹) '' s.1, by
    obtain ⟨b, hb, hns, hC⟩ := s.2
    refine ⟨g * b * g⁻¹, Subgroup.Normal.conj_mem inferInstance b hb g, ?_, ?_⟩
    · rintro ⟨c, hc⟩
      apply hns
      refine ⟨c, ?_⟩
      have hgi : ρ g⁻¹ * ρ g = 1 := by rw [← map_mul, inv_mul_cancel, map_one]
      have e : ρ b = ρ g⁻¹ * ρ (g * b * g⁻¹) * ρ g := by
        rw [← map_mul, ← map_mul]
        congr 1
        group
      rw [e, hc, mul_smul_comm, mul_one, smul_mul_assoc, hgi]
    · rw [hC, nab2_image_cls, map_mul, map_mul]⟩

private theorem nab2_conj_one (ρ : Representation F G V) (B : Subgroup G) [B.Normal]
    (s : nab2_ClsSet ρ B) : nab2_conj ρ B 1 s = s := by
  apply Subtype.ext
  show (fun t => ρ 1 * t * ρ 1⁻¹) '' s.1 = s.1
  simp only [inv_one, map_one, one_mul, mul_one, Set.image_id']

private theorem nab2_conj_mul (ρ : Representation F G V) (B : Subgroup G) [B.Normal]
    (m m' : G) (s : nab2_ClsSet ρ B) :
    nab2_conj ρ B (m * m') s = nab2_conj ρ B m (nab2_conj ρ B m' s) := by
  apply Subtype.ext
  show (fun t => ρ (m * m') * t * ρ (m * m')⁻¹) '' s.1 =
    (fun t => ρ m * t * ρ m⁻¹) '' ((fun t => ρ m' * t * ρ m'⁻¹) '' s.1)
  rw [Set.image_image]
  congr 1
  funext t
  simp only [map_mul, mul_inv_rev, mul_assoc]

private theorem nab2_card_le (ρ : Representation F G V) (B : Subgroup G) (u v : V →ₗ[F] V)
    (hcls : ∀ b ∈ B, (¬ ∃ c : F, ρ b = c • (1 : V →ₗ[F] V)) →
      nab2_cls (ρ b) = nab2_cls u ∨ nab2_cls (ρ b) = nab2_cls v ∨
        nab2_cls (ρ b) = nab2_cls (u * v)) :
    Finite (nab2_ClsSet ρ B) ∧ Nat.card (nab2_ClsSet ρ B) ≤ 3 := by
  classical
  let g : Fin 3 → Set (V →ₗ[F] V) := ![nab2_cls u, nab2_cls v, nab2_cls (u * v)]
  let f : nab2_ClsSet ρ B → Fin 3 := fun C =>
    if C.1 = nab2_cls u then 0 else if C.1 = nab2_cls v then 1 else 2
  have hf : ∀ C : nab2_ClsSet ρ B, C.1 = g (f C) := by
    intro C
    have hmem : C.1 = nab2_cls u ∨ C.1 = nab2_cls v ∨ C.1 = nab2_cls (u * v) := by
      obtain ⟨b, hb, hns, hC⟩ := C.2
      rw [hC]
      exact hcls b hb hns
    by_cases h1 : C.1 = nab2_cls u
    · have hf0 : f C = 0 := by simp only [f, if_pos h1]
      rw [hf0]
      simpa [g] using h1
    · by_cases h2 : C.1 = nab2_cls v
      · have hf1 : f C = 1 := by simp only [f, if_neg h1, if_pos h2]
        rw [hf1]
        simpa [g] using h2
      · have h3 : C.1 = nab2_cls (u * v) := (hmem.resolve_left h1).resolve_left h2
        have hf2 : f C = 2 := by simp only [f, if_neg h1, if_neg h2]
        rw [hf2]
        simpa [g] using h3
  have hinj : Function.Injective f := by
    intro C D hCD
    apply Subtype.ext
    rw [hf C, hf D, hCD]
  exact ⟨Finite.of_injective f hinj, by simpa using Nat.card_le_card_of_injective f hinj⟩

private theorem nab2_fix_scalar (ρ : Representation F G V) (B : Subgroup G) [B.Normal]
    (s : nab2_ClsSet ρ B) (z : V →ₗ[F] V) (hsz : s.1 = nab2_cls z) (k : G)
    (hk : nab2_conj ρ B k s = s) : ∃ t : F, ρ k * z = t • (z * ρ k) := by
  have h1 : (fun t => ρ k * t * ρ k⁻¹) '' s.1 = s.1 := congrArg Subtype.val hk
  rw [hsz] at h1
  have hmem : ρ k * z * ρ k⁻¹ ∈ nab2_cls z := by
    rw [← h1]
    exact ⟨z, nab2_mem_cls_self z, rfl⟩
  obtain ⟨t, _, ht⟩ := hmem
  have hki : ρ k⁻¹ * ρ k = 1 := by rw [← map_mul, inv_mul_cancel, map_one]
  refine ⟨t, ?_⟩
  calc ρ k * z = (ρ k * z * ρ k⁻¹) * ρ k := by
        rw [mul_assoc (ρ k * z) (ρ k⁻¹) (ρ k), hki, mul_one]
    _ = t • (z * ρ k) := by rw [ht, smul_mul_assoc]

private theorem nab2_commfix (ρ : Representation F G V) {K : Subgroup G} (hK : ⁅K, K⁆ = K)
    {z : V →ₗ[F] V} (hz : z ≠ 0) (hsl : ∀ g ∈ K, ∃ t : F, ρ g * z = t • (z * ρ g)) :
    ∀ k ∈ K, ρ k * z = z * ρ k := by
  let C : Subgroup G :=
    { carrier := {g | ρ g * z = z * ρ g}
      mul_mem' := fun {a b} ha hb => by
        have ha' : ρ a * z = z * ρ a := ha
        have hb' : ρ b * z = z * ρ b := hb
        show ρ (a * b) * z = z * ρ (a * b)
        rw [map_mul, mul_assoc, hb', ← mul_assoc (ρ a) z (ρ b), ha', mul_assoc]
      one_mem' := by
        show ρ 1 * z = z * ρ 1
        rw [map_one, one_mul, mul_one]
      inv_mem' := fun {a} ha => by
        have ha' : ρ a * z = z * ρ a := ha
        show ρ a⁻¹ * z = z * ρ a⁻¹
        have hi : ρ a⁻¹ * ρ a = 1 := by rw [← map_mul, inv_mul_cancel, map_one]
        have hi' : ρ a * ρ a⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel, map_one]
        symm
        calc z * ρ a⁻¹ = (ρ a⁻¹ * ρ a) * z * ρ a⁻¹ := by rw [hi, one_mul]
          _ = ρ a⁻¹ * (ρ a * z) * ρ a⁻¹ := by simp only [mul_assoc]
          _ = ρ a⁻¹ * (z * ρ a) * ρ a⁻¹ := by rw [ha']
          _ = ρ a⁻¹ * z * (ρ a * ρ a⁻¹) := by simp only [mul_assoc]
          _ = ρ a⁻¹ * z := by rw [hi', mul_one] }
  have hle : ⁅K, K⁆ ≤ C := by
    rw [Subgroup.commutator_le]
    intro x hx y hy
    show ρ ⁅x, y⁆ * z = z * ρ ⁅x, y⁆
    rw [commutatorElement_def, map_mul, map_mul, map_mul]
    obtain ⟨t₁, h₁⟩ := hsl x hx
    obtain ⟨t₂, h₂⟩ := hsl y hy
    obtain ⟨t₃, h₃⟩ := hsl x⁻¹ (inv_mem hx)
    obtain ⟨t₄, h₄⟩ := hsl y⁻¹ (inv_mem hy)
    exact nab2_slide hz (by rw [← map_mul, mul_inv_cancel, map_one])
      (by rw [← map_mul, mul_inv_cancel, map_one]) h₁ h₂ h₃ h₄
  intro k hk
  have hk' : k ∈ ⁅K, K⁆ := by rw [hK]; exact hk
  exact hle hk'

theorem nonabelian_two (h2 : (2 : F) ≠ 0) [Module.Finite F V] (hd : Module.finrank F V = 2)
    (ρ : Representation F G V) (B K : Subgroup G) [B.Normal]
    (hB' : ∀ x ∈ B, ∀ y ∈ B, ∃ c : F, ρ ⁅x, y⁆ = c • (1 : V →ₗ[F] V))
    (hnab : ∃ x ∈ B, ∃ y ∈ B, ρ x * ρ y ≠ ρ y * ρ x) (hK : ⁅K, K⁆ = K) :
    ∀ k ∈ K, ρ k = 1 := by
  classical
  obtain ⟨x, hx, y, hy, hxy⟩ := hnab
  haveI : Nontrivial V := Module.nontrivial_of_finrank_pos (R := F) (by rw [hd]; norm_num)
  have hu : ρ x * ρ x⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel, map_one]
  have hui : ρ x⁻¹ * ρ x = 1 := by rw [← map_mul, inv_mul_cancel, map_one]
  have hv : ρ y * ρ y⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel, map_one]
  have hvi : ρ y⁻¹ * ρ y = 1 := by rw [← map_mul, inv_mul_cancel, map_one]
  have hu0 : ρ x ≠ 0 := nab2_ne_zero hu
  have hv0 : ρ y ≠ 0 := nab2_ne_zero hv
  obtain ⟨c, hc⟩ := hB' x hx y hy
  have hc2 : c * c = 1 := nab2_sq hd ρ x y c hc
  have hcrel : ρ x * ρ y = c • (ρ y * ρ x) := nab2_rel ρ x y c hc
  have hc_eq : c = -1 := by
    rcases mul_self_eq_one_iff.mp hc2 with h | h
    · rw [h, one_smul] at hcrel
      exact absurd hcrel hxy
    · exact h
  have huv : ρ x * ρ y = -(ρ y * ρ x) := by rw [hcrel, hc_eq, neg_one_smul]
  have hxns : ¬ ∃ d : F, ρ x = d • (1 : V →ₗ[F] V) := by
    rintro ⟨d, hd'⟩
    apply hxy
    rw [hd']
    simp [smul_mul_assoc, mul_smul_comm]
  have hyns : ¬ ∃ d : F, ρ y = d • (1 : V →ₗ[F] V) := by
    rintro ⟨d, hd'⟩
    apply hxy
    rw [hd']
    simp [smul_mul_assoc, mul_smul_comm]
  have hcls : ∀ b ∈ B, (¬ ∃ d : F, ρ b = d • (1 : V →ₗ[F] V)) →
      nab2_cls (ρ b) = nab2_cls (ρ x) ∨ nab2_cls (ρ b) = nab2_cls (ρ y) ∨
        nab2_cls (ρ b) = nab2_cls (ρ x * ρ y) := by
    intro b hb hns
    obtain ⟨c₁, hc₁⟩ := hB' b hb x hx
    obtain ⟨c₂, hc₂⟩ := hB' b hb y hy
    have hbi : ρ b * ρ b⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel, map_one]
    obtain ⟨s, hs | hs | hs | hs⟩ :=
      nab2_decomp h2 hd hu hui hv hvi huv (nab2_sq hd ρ b x c₁ hc₁)
        (nab2_sq hd ρ b y c₂ hc₂) (nab2_rel ρ b x c₁ hc₁) (nab2_rel ρ b y c₂ hc₂)
    · exact (hns ⟨s, hs⟩).elim
    · have hs0 : s ≠ 0 := by
        rintro rfl
        exact nab2_ne_zero hbi (by rw [hs, zero_smul])
      left
      rw [hs, nab2_cls_smul hs0]
    · have hs0 : s ≠ 0 := by
        rintro rfl
        exact nab2_ne_zero hbi (by rw [hs, zero_smul])
      refine Or.inr (Or.inl ?_)
      rw [hs, nab2_cls_smul hs0]
    · have hs0 : s ≠ 0 := by
        rintro rfl
        exact nab2_ne_zero hbi (by rw [hs, zero_smul])
      refine Or.inr (Or.inr ?_)
      rw [hs, nab2_cls_smul hs0]
  obtain ⟨hfin, hcard⟩ := nab2_card_le ρ B (ρ x) (ρ y) hcls
  haveI := hfin
  have hS4 : Nat.card (nab2_ClsSet ρ B) ≤ 4 := le_trans hcard (by norm_num)
  have hfix : ∀ k ∈ K, ∀ s : nab2_ClsSet ρ B, nab2_conj ρ B k s = s := fun k hk s =>
    perfect_act_trivial hS4 (nab2_conj ρ B) (nab2_conj_one ρ B) (nab2_conj_mul ρ B) hK hk s
  have hslx : ∀ k ∈ K, ∃ t : F, ρ k * ρ x = t • (ρ x * ρ k) := fun k hk =>
    nab2_fix_scalar ρ B ⟨nab2_cls (ρ x), x, hx, hxns, rfl⟩ (ρ x) rfl k (hfix k hk _)
  have hsly : ∀ k ∈ K, ∃ t : F, ρ k * ρ y = t • (ρ y * ρ k) := fun k hk =>
    nab2_fix_scalar ρ B ⟨nab2_cls (ρ y), y, hy, hyns, rfl⟩ (ρ y) rfl k (hfix k hk _)
  have hcx : ∀ k ∈ K, ρ k * ρ x = ρ x * ρ k := nab2_commfix ρ hK hu0 hslx
  have hcy : ∀ k ∈ K, ρ k * ρ y = ρ y * ρ k := nab2_commfix ρ hK hv0 hsly
  have hUx : IsUnit (ρ x) := isUnit_iff_exists.mpr ⟨ρ x⁻¹, hu, hui⟩
  have hUy : IsUnit (ρ y) := isUnit_iff_exists.mpr ⟨ρ y⁻¹, hv, hvi⟩
  have hscal : ∀ k ∈ K, ∃ d : F, ρ k = d • (1 : V →ₗ[F] V) := fun k hk =>
    commutant_anticomm_scalar h2 hd (ρ x) (ρ y) hUx hUy huv (ρ k) (hcx k hk) (hcy k hk)
  refine perfect_trivial_of_comm ρ hK ?_
  intro a ha b hb
  obtain ⟨da, hda⟩ := hscal a ha
  obtain ⟨db, hdb⟩ := hscal b hb
  rw [hda, hdb]
  simp only [smul_mul_assoc, mul_smul_comm, one_mul, mul_one, smul_smul, mul_comm]

end Rep

end NonabelianPlane

end CFSG.RankThree.PartTwo.KFacts.NDC

end

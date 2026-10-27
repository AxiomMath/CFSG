module

public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyExcReflCartan
public import CFSG.LocalAnalysis.StandardType.GGCoxeterLabel
import Mathlib.LinearAlgebra.Dual.Lemmas

public section

namespace CFSG.StandardType

open Module CFSG.Assembly

section Conj

variable {p : ℕ} [Fact p.Prime] {E : Type*} [Group E] {V : Type*} [AddCommGroup V]
  [Module (ZMod p) V]

theorem ggLin_conj_apply (ι : Additive E ≃+ V) (u φ : MulAut E) {g : Module.Dual (ZMod p) V}
    {z : V} (hφ : ∀ v, ggLin (p := p) ι φ v = v - g v • z) (v : V) :
    ggLin (p := p) ι (u * φ * u⁻¹) v =
      v - g ((ggLin (p := p) ι u).symm v) • ggLin (p := p) ι u z := by
  rw [map_mul, map_mul, map_inv]
  show ggLin (p := p) ι u (ggLin (p := p) ι φ ((ggLin (p := p) ι u).symm v)) = _
  rw [hφ, map_sub, map_smul, LinearEquiv.apply_symm_apply]

end Conj

section Fixed

variable {p : ℕ} [Fact p.Prime] {E : Type*} [Group E] {V : Type*} [AddCommGroup V]
  [Module (ZMod p) V]

@[expose] noncomputable def ggFixedSubmodule (ι : Additive E ≃+ V) (N : Subgroup (MulAut E)) :
    Submodule (ZMod p) V :=
  ⨅ φ ∈ N, LinearMap.ker ((ggLin (p := p) ι φ).toLinearMap - LinearMap.id)

theorem mem_ggFixedSubmodule_iff {ι : Additive E ≃+ V} {N : Subgroup (MulAut E)} {v : V} :
    v ∈ ggFixedSubmodule (p := p) ι N ↔ ∀ φ ∈ N, ggLin (p := p) ι φ v = v := by
  simp [ggFixedSubmodule, Submodule.mem_iInf, sub_eq_zero]

end Fixed

section Comm

theorem reflection_comm_cross_eq_zero {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (h2 : (2 : K) ≠ 0) {f g : Module.Dual K V} {y z : V} (hfy : f y = 2) (hgz : g z = 2)
    (hyz : LinearIndependent K ![y, z])
    (hcomm : reflection hfy * reflection hgz = reflection hgz * reflection hfy) : f z = 0 := by
  have h := congrArg (fun T : V ≃ₗ[K] V => T z) hcomm
  simp only [LinearEquiv.mul_apply, reflection_apply, map_sub, map_smul, hgz, smul_eq_mul] at h
  have h' : (2 * f z) • y + (-(f z * g y)) • z = 0 := by
    rw [← sub_eq_zero] at h
    rw [← h]
    module
  exact (mul_eq_zero.mp (LinearIndependent.pair_iff.mp hyz _ _ h').1).resolve_left h2

variable {p : ℕ} [Fact p.Prime] {V : Type*} [AddCommGroup V] [Module (ZMod p) V]

theorem ggReflection_comm_cross_eq_zero (hp2 : p ≠ 2) {f g : Module.Dual (ZMod p) V} {y z : V}
    (hfy : f y = 2) (hgz : g z = 2) (hyz : LinearIndependent (ZMod p) ![y, z])
    (hcomm : reflection hfy * reflection hgz = reflection hgz * reflection hfy) : f z = 0 :=
  reflection_comm_cross_eq_zero (zmod_two_ne_zero hp2) hfy hgz hyz hcomm

end Comm

section Hyperplane

variable {K V Λ : Type*} [Field K] [AddCommGroup V] [Module K V] [Fintype Λ]

theorem not_linearIndependent_pair_of_mem [FiniteDimensional K V] (W : Submodule K V)
    (hW : Module.finrank K W ≤ 1) {a b : V} (ha : a ∈ W) (hb : b ∈ W) :
    ¬ LinearIndependent K ![a, b] := by
  intro hli
  have hli' : LinearIndependent K ![(⟨a, ha⟩ : W), ⟨b, hb⟩] := by
    refine LinearIndependent.of_comp W.subtype ?_
    convert hli using 1
    ext i
    fin_cases i <;> rfl
  have h := hli'.fintype_card_le_finrank
  rw [Fintype.card_fin] at h
  omega

theorem not_linearIndependent_pair_of_vanishing_of_codim_le [FiniteDimensional K V]
    (H : Submodule K V) (hdim : Module.finrank K V ≤ Module.finrank K H + 1)
    {f₁ f₂ : Module.Dual K V} (h₁ : ∀ w ∈ H, f₁ w = 0) (h₂ : ∀ w ∈ H, f₂ w = 0) :
    ¬ LinearIndependent K ![f₁, f₂] := by
  have hann := Subspace.finrank_add_finrank_dualAnnihilator_eq H
  exact not_linearIndependent_pair_of_mem H.dualAnnihilator (by omega)
    ((Submodule.mem_dualAnnihilator _).mpr h₁) ((Submodule.mem_dualAnnihilator _).mpr h₂)

omit [Fintype Λ] in
theorem apply_eq_zero_of_mem_span_range {h : Λ → V} {f : Module.Dual K V}
    (hf : ∀ k, f (h k) = 0) {w : V} (hw : w ∈ Submodule.span K (Set.range h)) : f w = 0 := by
  have hle : Submodule.span K (Set.range h) ≤ LinearMap.ker f := Submodule.span_le.mpr (by
    rintro _ ⟨k, rfl⟩
    exact hf k)
  exact hle hw

theorem not_linearIndependent_pair_of_vanishing [FiniteDimensional K V] {h : Λ → V}
    (hh : LinearIndependent K h) (hdim : Module.finrank K V = Fintype.card Λ + 1)
    {f₁ f₂ : Module.Dual K V} (h₁ : ∀ k, f₁ (h k) = 0) (h₂ : ∀ k, f₂ (h k) = 0) :
    ¬ LinearIndependent K ![f₁, f₂] :=
  not_linearIndependent_pair_of_vanishing_of_codim_le _
    (by rw [finrank_span_eq_card hh, hdim]) (fun _ => apply_eq_zero_of_mem_span_range h₁)
    (fun _ => apply_eq_zero_of_mem_span_range h₂)

end Hyperplane

section Orbit

variable {p : ℕ} [Fact p.Prime] {V : Type*} [AddCommGroup V] [Module (ZMod p) V]

theorem ggCartan_orbit_apply_eq_zero (hp2 : p ≠ 2) {Λ : Type} [Fintype Λ] {M : CoxeterMatrix Λ}
    (hM : GGIsWeylMatrix M) {C : Matrix Λ Λ ℤ} (hC : GGIntCartan M C)
    (h3 : 3 ≤ Fintype.card Λ) {h : Λ → V} {α : Λ → Module.Dual (ZMod p) V}
    (hpair : ∀ i j, α i (h j) = (C i j : ZMod p)) (A : Subgroup (V ≃ₗ[ZMod p] V))
    (R : Λ → (V ≃ₗ[ZMod p] V)) (hR : ∀ j w, R j w = w - α j w • h j) (hRA : ∀ j, R j ∈ A)
    (f : Module.Dual (ZMod p) V) {i₀ : Λ} (hi₀ : ∀ U ∈ A, f (U (h i₀)) = 0) :
    ∀ k, ∀ U ∈ A, f (U (h k)) = 0 := by
  have hS := ggCartan_closed_eq_univ hp2 hM hC h3
    (S := {k | ∀ U ∈ A, f (U (h k)) = 0}) ⟨i₀, hi₀⟩ (by
      intro k hk j hjk U hU
      have hRjk : R j (h k) = h k - (C j k : ZMod p) • h j := by rw [hR, hpair]
      have h1 : f (U (h k)) = 0 := hk U hU
      have h2 : f ((U * R j) (h k)) = 0 := hk (U * R j) (A.mul_mem hU (hRA j))
      rw [LinearEquiv.mul_apply, hRjk, map_sub, map_smul, map_sub, map_smul] at h2
      have h3 : f (U (h k)) = (C j k : ZMod p) • f (U (h j)) := sub_eq_zero.mp h2
      rw [h1] at h3
      exact (smul_eq_zero.mp h3.symm).resolve_left hjk)
  intro k
  have hk : k ∈ {k | ∀ U ∈ A, f (U (h k)) = 0} := hS ▸ Set.mem_univ k
  exact hk

end Orbit

end CFSG.StandardType

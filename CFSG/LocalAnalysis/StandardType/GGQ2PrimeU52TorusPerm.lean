module

public import CFSG.LocalAnalysis.StandardType.GGQ2PrimeU52TorusFrame
public import CFSG.RankThree.PartOne.KF.R9Perm

public section

namespace CFSG.GGQ2Prime

open Subgroup CFSG.Open CFSG.Models
open CFSG.RankThree.PartOne.KFU CFSG.ClassicalGroups.UnitaryFlag
  CFSG.LocalAnalysis.ComponentInitial

private theorem permGL_mem_normalizer_torusSU {n p : ℕ} {K : Type} [Field K]
    (σ : Equiv.Perm (Fin n)) :
    (permGL σ : GL (Fin n) K) ∈
      normalizer ((torusSU p n K : Subgroup (GL (Fin n) K)) : Set (GL (Fin n) K)) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨fun hx => (normPerm_permGL σ).1 x hx, fun hx => ?_⟩
  have h := (normPerm_permGL σ⁻¹ : NormPerm p (permGL σ⁻¹ : GL (Fin n) K) σ⁻¹).1 _ hx
  have e : (permGL σ : GL (Fin n) K)⁻¹ * (permGL σ * x * (permGL σ : GL (Fin n) K)⁻¹) *
      permGL σ = x := by group
  rwa [map_inv, inv_inv, e] at h

@[expose] noncomputable def U52TorusCarried.torusPermElt {G : Type} [Group G] {K : Type} [Field K]
    {X : Subgroup G} (hU : UnitaryFieldData 2 1 K) (ψ : unitarySU 2 1 K 5 ≃* X)
    (σ : Equiv.Perm (Fin 5)) : G :=
  ((ψ ⟨permGL σ, permGL_mem_unitarySU hU σ⟩ : X) : G)

theorem U52TorusCarried.torusPermElt_mem {G : Type} [Group G] {K : Type} [Field K]
    {X T : Subgroup G} {ψ : unitarySU 2 1 K 5 ≃* X} (hU : UnitaryFieldData 2 1 K) (hTX : T ≤ X)
    (hψ : U52TorusCarried X T ψ) (σ : Equiv.Perm (Fin 5)) :
    U52TorusCarried.torusPermElt hU ψ σ ∈ X ⊓ normalizer (T : Set G) :=
  Subgroup.mem_inf.2 ⟨(ψ ⟨permGL σ, permGL_mem_unitarySU hU σ⟩).2,
    (hψ.mem_normalizer_torus_iff hU hTX ⟨permGL σ, permGL_mem_unitarySU hU σ⟩).2
      (permGL_mem_normalizer_torusSU σ)⟩

theorem U52TorusCarried.torusPermElt_conj_inj {G : Type} [Group G] {K : Type} [Field K]
    {X T : Subgroup G} {ψ : unitarySU 2 1 K 5 ≃* X} (hU : UnitaryFieldData 2 1 K) (hTX : T ≤ X)
    (hψ : U52TorusCarried X T ψ) {σ₁ σ₂ : Equiv.Perm (Fin 5)}
    (h : ∀ b : T, U52TorusCarried.torusPermElt hU ψ σ₁ * (b : G) *
        (U52TorusCarried.torusPermElt hU ψ σ₁)⁻¹ =
      U52TorusCarried.torusPermElt hU ψ σ₂ * (b : G) * (U52TorusCarried.torusPermElt hU ψ σ₂)⁻¹) :
    σ₁ = σ₂ :=
  NormPerm.eq_of_conj_eq (torusSU_three_char_distinct hU) (normPerm_permGL σ₁)
    (normPerm_permGL σ₂) ((hψ.conj_torus_eq_iff hU hTX ⟨permGL σ₁, permGL_mem_unitarySU hU σ₁⟩
      ⟨permGL σ₂, permGL_mem_unitarySU hU σ₂⟩).1 h)

theorem U52TorusCarried.exists_torusPermElt_conj_eq {G : Type} [Group G] {K : Type} [Field K]
    {X T : Subgroup G} {ψ : unitarySU 2 1 K 5 ≃* X} (hU : UnitaryFieldData 2 1 K) (hTX : T ≤ X)
    (hψ : U52TorusCarried X T ψ) {y : G} (hy : y ∈ X ⊓ normalizer (T : Set G)) :
    ∃ σ : Equiv.Perm (Fin 5), ∀ b : T, y * (b : G) * y⁻¹ =
      U52TorusCarried.torusPermElt hU ψ σ * (b : G) * (U52TorusCarried.torusPermElt hU ψ σ)⁻¹ := by
  set s := ψ.symm ⟨y, hy.1⟩ with hs
  have hsy : ((ψ s : X) : G) = y := by simp [hs]
  have hn := (hψ.mem_normalizer_torus_iff hU hTX s).1 (by rw [hsy]; exact hy.2)
  rw [Subgroup.mem_normalizer_iff] at hn
  have hw : ∀ x ∈ torusSU 3 5 K, (s : GL (Fin 5) K) * x * (s : GL (Fin 5) K)⁻¹ ∈ torusSU 3 5 K :=
    fun x hx => (hn x).1 hx
  have hinv : ∀ x ∈ torusSU 3 5 K, (s : GL (Fin 5) K)⁻¹ * x * (s : GL (Fin 5) K) ∈ torusSU 3 5 K :=
    fun x hx => by
      have e : (s : GL (Fin 5) K) * ((s : GL (Fin 5) K)⁻¹ * x * (s : GL (Fin 5) K)) *
          (s : GL (Fin 5) K)⁻¹ = x := by group
      refine (hn _).2 ?_
      rwa [e]
  obtain ⟨τ, hτ⟩ := exists_normPerm (torusSU_three_char_distinct hU) hw hinv
  refine ⟨τ, fun b => ?_⟩
  rw [← hsy]
  refine (hψ.conj_torus_eq_iff hU hTX s ⟨permGL τ, permGL_mem_unitarySU hU τ⟩).2 (fun g hg => ?_) b
  exact ((normPerm_permGL τ).conj_eq hg (hτ.1 g hg) (hτ.ent_conj hg)).symm

end CFSG.GGQ2Prime

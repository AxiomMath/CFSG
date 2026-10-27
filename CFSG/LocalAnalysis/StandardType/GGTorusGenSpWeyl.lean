module

public import CFSG.LocalAnalysis.StandardType.GGTorusGenSpGen

public section

namespace CFSG.StandardType

open CFSG CFSG.SeitzReduction.SymplecticPilot
open CFSG.Open (StatedSp)

private lemma exists_conj_diagSp_of_mem_signedPerm {K : Type} [Field K] {m : ℕ} [CharP K 2]
    {p : ℕ} {w : StatedSp m K} (hw : w ∈ spSignedPermSp K m) :
    ∀ t : Fin m → Kˣ, t ^ p = 1 →
      ∃ t' : Fin m → Kˣ, t' ^ p = 1 ∧
        w * diagSp K m t * w⁻¹ = diagSp K m t' := by
  classical
  refine Subgroup.closure_induction'' (p := fun w _ => ∀ t : Fin m → Kˣ, t ^ p = 1 →
      ∃ t' : Fin m → Kˣ, t' ^ p = 1 ∧
        w * diagSp K m t * w⁻¹ = diagSp K m t') ?_ ?_ ?_ ?_ hw
  · intro x hx t ht
    rcases hx with ⟨π, rfl⟩ | ⟨i, rfl⟩
    · exact ⟨t ∘ π.symm, by
        funext j
        simpa [Pi.pow_apply] using congrFun ht (π.symm j), conj_permSp_diagSp π t⟩
    · exact ⟨Function.update t i (t i)⁻¹, by
        funext j
        by_cases hj : j = i
        · rw [hj, Pi.pow_apply, Function.update_self]
          simpa using congrFun ht i
        · simpa [Pi.pow_apply, Function.update_of_ne hj] using congrFun ht j,
        spSwapSp_conj_diagSp i t⟩
  · intro x hx t ht
    rcases hx with ⟨π, rfl⟩ | ⟨i, rfl⟩
    · refine ⟨t ∘ π, by
        funext j
        simpa [Pi.pow_apply] using congrFun ht (π j), ?_⟩
      have h := conj_permSp_diagSp (K := K) π (t ∘ π)
      rw [show (t ∘ π) ∘ π.symm = t from by funext j; simp] at h
      rw [← h]
      group
    · refine ⟨Function.update t i (t i)⁻¹, by
        funext j
        by_cases hj : j = i
        · rw [hj, Pi.pow_apply, Function.update_self]
          simpa using congrFun ht i
        · simpa [Pi.pow_apply, Function.update_of_ne hj] using congrFun ht j, ?_⟩
      have h := spSwapSp_conj_diagSp (K := K) (m := m) i
        (Function.update t i (t i)⁻¹)
      rw [show Function.update (Function.update t i (t i)⁻¹) i
            ((Function.update t i (t i)⁻¹) i)⁻¹ = t from by simp] at h
      rw [← h]
      group
  · intro t ht
    exact ⟨t, ht, by simp⟩
  · intro x y _ _ hx hy t ht
    obtain ⟨t₁, ht₁, h₁⟩ := hy t ht
    obtain ⟨t₂, ht₂, h₂⟩ := hx t₁ ht₁
    refine ⟨t₂, ht₂, ?_⟩
    calc x * y * diagSp K m t * (x * y)⁻¹
        = x * (y * diagSp K m t * y⁻¹) * x⁻¹ := by group
      _ = x * diagSp K m t₁ * x⁻¹ := by rw [h₁]
      _ = diagSp K m t₂ := h₂

private lemma conj_mem_of_mem_signedPerm {K : Type} [Field K] {m : ℕ} [CharP K 2]
    {p : ℕ} {M : Type} [Group M] {L' E : Subgroup M} {φ : StatedSp m K →* M}
    (hφL : φ.range = L')
    (hTE : ∀ t : Fin m → Kˣ, t ^ p = 1 → φ (diagSp K m t) ∈ E)
    (hEφ : ∀ e ∈ E, ∃ t : Fin m → Kˣ, t ^ p = 1 ∧
      e * (φ (diagSp K m t))⁻¹ ∈ Subgroup.centralizer (L' : Set M))
    {w : StatedSp m K} (hw : w ∈ spSignedPermSp K m) {e : M} (he : e ∈ E) :
    φ w * e * (φ w)⁻¹ ∈ E := by
  obtain ⟨t, ht, hz⟩ := hEφ e he
  obtain ⟨t', ht', hconj⟩ := exists_conj_diagSp_of_mem_signedPerm hw t ht
  have hφw : φ w ∈ L' := hφL ▸ (show φ w ∈ φ.range from ⟨w, rfl⟩)
  have hzw : φ w * (e * (φ (diagSp K m t))⁻¹) =
      (e * (φ (diagSp K m t))⁻¹) * φ w :=
    (Subgroup.mem_centralizer_iff.mp hz) (φ w) hφw
  have hstep : φ w * e * (φ w)⁻¹ =
      (e * (φ (diagSp K m t))⁻¹) * φ (w * diagSp K m t * w⁻¹) := by
    calc φ w * e * (φ w)⁻¹
        = φ w * ((e * (φ (diagSp K m t))⁻¹) * φ (diagSp K m t)) * (φ w)⁻¹ := by
          group
      _ = (φ w * (e * (φ (diagSp K m t))⁻¹)) * φ (diagSp K m t) * (φ w)⁻¹ := by
          group
      _ = ((e * (φ (diagSp K m t))⁻¹) * φ w) * φ (diagSp K m t) * (φ w)⁻¹ := by
          rw [hzw]
      _ = (e * (φ (diagSp K m t))⁻¹) * (φ w * φ (diagSp K m t) * (φ w)⁻¹) := by
          group
      _ = (e * (φ (diagSp K m t))⁻¹) * φ (w * diagSp K m t * w⁻¹) := by
          rw [map_mul, map_mul, map_inv]
  rw [hstep, hconj]
  exact E.mul_mem (E.mul_mem he (E.inv_mem (hTE t ht))) (hTE t' ht')

theorem spSignedPermSp_map_mem_normalizer {K : Type} [Field K] {m : ℕ} [CharP K 2] {p : ℕ}
    {M : Type} [Group M] {L' E : Subgroup M} {φ : StatedSp m K →* M} (hφL : φ.range = L')
    (hTE : ∀ t : Fin m → Kˣ, t ^ p = 1 → φ (diagSp K m t) ∈ E)
    (hEφ : ∀ e ∈ E, ∃ t : Fin m → Kˣ, t ^ p = 1 ∧
      e * (φ (diagSp K m t))⁻¹ ∈ Subgroup.centralizer (L' : Set M))
    {w : StatedSp m K} (hw : w ∈ spSignedPermSp K m) :
    φ w ∈ Subgroup.normalizer (E : Set M) := by
  rw [Subgroup.mem_normalizer_iff]
  intro e
  constructor
  · exact conj_mem_of_mem_signedPerm hφL hTE hEφ hw
  · intro he
    have hw' : w⁻¹ ∈ spSignedPermSp K m := (spSignedPermSp K m).inv_mem hw
    have hmem := conj_mem_of_mem_signedPerm hφL hTE hEφ hw' he
    have hval : φ w⁻¹ * (φ w * e * (φ w)⁻¹) * (φ w⁻¹)⁻¹ = e := by
      rw [map_inv]
      group
    rwa [hval] at hmem

end CFSG.StandardType

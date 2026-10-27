module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive.Invol.OmHeis
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive.Invol.OmIso

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive

open QuadraticMap CFSG.ClassicalGroups.Orthogonal CFSG.SignalizerFunctorTheorem.NonLocal.Orth
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear

variable {K : Type} [Field K] {d : ℕ} {Q : QuadraticForm K (Fin d → K)}

private theorem exists_singular_orthogonal_to_pair [Finite K] (hK2 : ringChar K ≠ 2)
    (hd : 7 ≤ d) (u w : Fin d → K) :
    ∃ u₂ : Fin d → K, Q u₂ = 0 ∧ polar Q u u₂ = 0 ∧ polar Q u₂ w = 0 ∧
      u₂ ∉ Submodule.span K {u, w} := by
  classical
  let f : (Fin d → K) →ₗ[K] K × K := (polarBilin Q u).prod (polarBilin Q w)
  let W : Submodule K (Fin d → K) := LinearMap.ker f
  have hWmem : ∀ x : Fin d → K, x ∈ W ↔ polar Q u x = 0 ∧ polar Q w x = 0 := by
    intro x
    simp [W, f, LinearMap.mem_ker, polarBilin_apply_apply]
  have hVdim : Module.finrank K (Fin d → K) = d := Module.finrank_fin_fun K
  have hWdim : d - 2 ≤ Module.finrank K W := by
    have h := LinearMap.finrank_range_add_finrank_ker f
    rw [hVdim] at h
    have hrange : Module.finrank K (LinearMap.range f) ≤ 2 := by
      have hle := Submodule.finrank_le (LinearMap.range f)
      rw [Module.finrank_prod, Module.finrank_self] at hle
      simpa using hle
    have hker : Module.finrank K W = Module.finrank K (LinearMap.ker f) := rfl
    omega
  obtain ⟨C, hC⟩ := Submodule.exists_isCompl (Submodule.span K ({u, w} : Set (Fin d → K)))
  have hCdim : d - 2 ≤ Module.finrank K C := by
    have h := Submodule.finrank_add_eq_of_isCompl hC
    rw [hVdim] at h
    have hspan : Module.finrank K (Submodule.span K ({u, w} : Set (Fin d → K))) ≤ 2 := by
      have hle := finrank_span_le_card (R := K) ({u, w} : Set (Fin d → K))
      have h2 : ({u, w} : Set (Fin d → K)).toFinset.card ≤ 2 := by
        rw [Set.toFinset_insert, Set.toFinset_singleton]
        exact Finset.card_insert_le _ _
      omega
    omega
  have hUdim : 3 ≤ Module.finrank K ↥(W ⊓ C) := by
    have h := Submodule.finrank_sup_add_finrank_inf_eq W C
    have hsup : Module.finrank K ↥(W ⊔ C) ≤ d := by
      have hle := Submodule.finrank_le (W ⊔ C)
      rwa [hVdim] at hle
    omega
  obtain ⟨u₂, hu₂U, hu₂0, hu₂Q⟩ :=
    exists_singular_of_three_le_finrank (k := K) (V := Fin d → K) (W := W ⊓ C) hK2 Q hUdim
  have hu₂W : u₂ ∈ W := (Submodule.mem_inf.mp hu₂U).1
  have hmem := (hWmem u₂).mp hu₂W
  have hUinf : (W ⊓ C) ⊓ Submodule.span K ({u, w} : Set (Fin d → K)) = ⊥ := by
    have hWC : W ⊓ C ≤ C := inf_le_right
    refine le_antisymm ?_ bot_le
    calc (W ⊓ C) ⊓ Submodule.span K ({u, w} : Set (Fin d → K))
        ≤ C ⊓ Submodule.span K ({u, w} : Set (Fin d → K)) := inf_le_inf_right _ hWC
      _ = ⊥ := by
          rw [inf_comm]
          exact hC.inf_eq_bot
  have hu₂out : u₂ ∉ Submodule.span K ({u, w} : Set (Fin d → K)) := by
    intro hmem'
    have h' : u₂ ∈ (W ⊓ C) ⊓ Submodule.span K ({u, w} : Set (Fin d → K)) := ⟨hu₂U, hmem'⟩
    rw [hUinf] at h'
    exact hu₂0 ((Submodule.mem_bot K).mp h')
  exact ⟨u₂, hu₂Q, hmem.1, by rw [polar_comm]; exact hmem.2, hu₂out⟩

theorem exists_line_orthogonal_of_notMem_span [Finite K] (hK2 : ringChar K ≠ 2) (hd : 7 ≤ d)
    {u w : Fin d → K} (hw : w ∉ Submodule.span K {u}) :
    ∃ u₂ : Fin d → K, Q u₂ = 0 ∧ polar Q u u₂ = 0 ∧ polar Q u₂ w = 0 ∧
      u₂ ∉ Submodule.span K {u} ∧ w ∉ Submodule.span K {u, u₂} := by
  classical
  obtain ⟨u₂, hu₂Q, hu₂u, hu₂w, hu₂out⟩ :=
    exists_singular_orthogonal_to_pair (Q := Q) hK2 hd u w
  have hu₂s : u₂ ∉ Submodule.span K {u} := by
    intro hmem
    refine hu₂out (Submodule.span_mono ?_ hmem)
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    rw [hx]
    simp
  have hwu₂ : w ∉ Submodule.span K {u, u₂} := by
    intro hmem
    obtain ⟨α, β, hαβ⟩ := Submodule.mem_span_pair.mp hmem
    have hβ : β ≠ 0 := by
      intro hβ0
      apply hw
      rw [← hαβ, hβ0, zero_smul, add_zero]
      exact Submodule.smul_mem _ _ (Submodule.subset_span (by simp))
    apply hu₂out
    have hu₂eq : u₂ = β⁻¹ • (w - α • u) := by
      rw [← hαβ, add_sub_cancel_left, smul_smul, inv_mul_cancel₀ hβ, one_smul]
    rw [hu₂eq]
    refine Submodule.smul_mem _ _ (Submodule.sub_mem _ ?_ ?_)
    · exact Submodule.subset_span (by simp)
    · exact Submodule.smul_mem _ _ (Submodule.subset_span (by simp))
  exact ⟨u₂, hu₂Q, hu₂u, hu₂w, hu₂s, hwu₂⟩

theorem good_omegaEichler [Finite K] {p e : ℕ} [CharP K p] (hp : p.Prime) (hp2 : p ≠ 2)
    (hK : Nat.card K = p ^ e) (h3 : 3 < p ^ e) (hQ : (polarBilin Q).Nondegenerate)
    (hex : ∀ u w : Fin d → K, ∃ x : matrixDerived Q,
      matrixLinearIso (d := d) (K := K) x.val = eichler Q u w)
    (hd : 7 ≤ d) {u w : Fin d → K} (hu0 : u ≠ 0) (hu : Q u = 0) (huw : polar Q u w = 0)
    (hw : w ∉ Submodule.span K {u}) :
    orderOf (matrixProjectiveProjection Q (eMat hex u w)) = p ∧
      IsSpecialGood p (matrixProjectiveProjection Q (eMat hex u w)) := by
  have hK2 : ringChar K ≠ 2 := by rw [ringChar.eq K p]; exact hp2
  obtain ⟨u₂, hu₂Q, hu₂u, hu₂w, hu₂s, hwu₂⟩ :=
    exists_line_orthogonal_of_notMem_span (Q := Q) hK2 hd hw
  have h := good_omegaHeis (u₁ := u) (u₂ := u₂) (z₁ := w) (z₂ := 0)
    hp hp2 hK h3 hQ hex hu0 hu hu₂Q hu₂u hu₂s huw hu₂w
    (polar_zero_right Q u) (polar_zero_right Q u₂) (polar_zero_right Q w) hwu₂
  rw [eMat_zero hex u₂, mul_one] at h
  exact h

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive

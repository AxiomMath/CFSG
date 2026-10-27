module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporLatO2

public section

namespace CFSG.Quasithin.H13.NQCat.T3

open CFSG.QuasithinUnique.Ch1.SporLat CFSG.QuasithinUnique.K1.SporadicPerm

theorem not_le_normalizer_of_label {Γ : Type} [Group Γ] [Finite Γ] {n : ℕ}
    [MulAction Γ (Fin n)] {Lab : Type} [DecidableEq Lab] [Hashable Lab] [Inhabited Lab]
    (C : LatCtx Γ n Lab) {j : ℕ} (hj : j < C.J)
    (h : ∃ ℓ ∈ (C.D.Om[j]!).lbl.toList, ∃ s ∈ C.D.sTabs, C.A.act s ℓ ≠ ℓ) :
    ¬ C.Y j ≤ Subgroup.normalizer (C.S : Set Γ) := by
  intro hle
  obtain ⟨ℓ, hℓ, s, hs, hsℓ⟩ := h
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hℓ
  have hi' : i < (C.Λ j).length := hi
  obtain ⟨y, hy, hyl⟩ := C.exists_elt_of_label hj (by simpa [LatCtx.Λ] using hi')
  rw [← C.hsg] at hs
  obtain ⟨σ, hσ, rfl⟩ := List.mem_map.mp hs
  have h1 : y⁻¹ * σ * y ∈ C.S := by
    have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ (hle hy)) σ).mp
      (C.sg_mem_S σ hσ)
    rwa [inv_inv] at this
  have h2 := (C.conj_mem_S_iff σ y).mp h1
  rw [hyl, ← C.Λ_getElem i hi'] at h2
  exact hsℓ h2

end CFSG.Quasithin.H13.NQCat.T3

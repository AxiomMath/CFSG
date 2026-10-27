module

public import CFSG.Quasithin.H13.GoldschmidtC137H6Ctx
public import CFSG.Quasithin.H13.GoldschmidtC137S6Std

public section

namespace CFSG.Quasithin.H13.U3.GC137

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.B3

variable {G : Type} [Group G]

namespace H6Ctx

variable [Finite G] {X T V L P : Subgroup G} (h : H6Ctx X T V L P)
include h

theorem kmodel : ∃ k, (k = Mod.ut0 ∨ k = Mod.u0) ∧ Nonempty (KModel k (autI h.hVe L)) :=
  h.hmod

theorem autI_X_eq {k : Mod} (N : KModel k (autI h.hVe L)) :
    (⊤ : Subgroup (Gp 6)).map N.ρ = autI h.hVe X := by
  have hLX : autI h.hVe L ≤ autI h.hVe X := autI_mono h.hVe h.hLX
  have hrange : ∀ x ∈ autI h.hVe X, ∃ σ, N.ρ σ = x := fun x hx =>
    N.le_range x (autI_le_normalizer_autI_gc h.hVe h.hn hx)
  have hρA : ∀ γ ∈ alternatingGroup (Fin 6), N.ρ γ ∈ autI h.hVe L := fun γ hγ => by
    have : N.ρ γ ∈ (alternatingGroup (Fin 6)).map N.ρ := ⟨γ, hγ, rfl⟩
    rwa [N.ρ_alt] at this
  have hnin : ¬ autI h.hVe T ≤ autI h.hVe L := h.hnin
  apply le_antisymm
  · rintro _ ⟨σ, -, rfl⟩
    by_cases hσ : σ ∈ alternatingGroup (Fin 6)
    · exact hLX (hρA σ hσ)
    · obtain ⟨y, hyT, hyL⟩ := IsConcreteLE.not_le_iff_exists.1 hnin
      obtain ⟨τ, hτ⟩ := hrange y (autI_mono h.hVe h.hT.1 hyT)
      have hτA : τ ∉ alternatingGroup (Fin 6) := fun hτA => hyL (hτ ▸ hρA τ hτA)
      have hσA : σ * τ⁻¹ ∈ alternatingGroup (Fin 6) := by
        rw [Equiv.Perm.mem_alternatingGroup] at hσ hτA ⊢
        have h1 : Equiv.Perm.sign σ = -1 := by
          rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h1 | h1
          · exact absurd h1 hσ
          · exact h1
        have h2 : Equiv.Perm.sign τ = -1 := by
          rcases Int.units_eq_one_or (Equiv.Perm.sign τ) with h2 | h2
          · exact absurd h2 hτA
          · exact h2
        rw [map_mul, map_inv, h1, h2]
        decide
      have hρσ : N.ρ σ = N.ρ (σ * τ⁻¹) * y := by
        rw [← hτ, ← map_mul]
        congr 1
        group
      rw [hρσ]
      exact (autI h.hVe X).mul_mem (hLX (hρA _ hσA)) (autI_mono h.hVe h.hT.1 hyT)
  · intro x hx
    obtain ⟨σ, rfl⟩ := hrange x hx
    exact ⟨σ, trivial, rfl⟩

end H6Ctx

end CFSG.Quasithin.H13.U3.GC137

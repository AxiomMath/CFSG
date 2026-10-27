module

public import CFSG.RankThree.GF2n.Smith81.S81VDefs

public section

namespace CFSG.RankThree.GF2n.Smith81.S81V

open CFSG.ClassicalGroups.Unitary CFSG.RankThree.GF2n.Smith81.U6Cube Module

variable {F : Type} [Field F] {σ : F ≃+* F}

theorem nonDeg_sup_span (hσ : ∀ c, σ (σ c) = c) {L : Submodule F (Fin 6 → F)}
    {p₄ r p' : Fin 6 → F} (hp4i : herm σ p₄ p₄ = 0)
    (hr1 : ∀ l ∈ L, herm σ p₄ l = 0 → l ∈ Submodule.span F {r})
    (hr2 : herm σ r r ≠ 0) (hr3 : herm σ p₄ r = 0) (hp'L : p' ∈ L) (hp' : herm σ p' p₄ ≠ 0) :
    NonDeg σ (L ⊔ Submodule.span F {p₄}) := by
  rintro v hv hperp
  obtain ⟨l, hl, z, hz, rfl⟩ := Submodule.mem_sup.mp hv
  obtain ⟨t, rfl⟩ := Submodule.mem_span_singleton.mp hz
  have hp4mem : p₄ ∈ L ⊔ Submodule.span F {p₄} :=
    Submodule.mem_sup_right (Submodule.mem_span_singleton_self p₄)
  have hl0 : herm σ p₄ l = 0 := by
    have h1 := hperp p₄ hp4mem
    simp only [herm_add_right, herm_smul_right, hp4i, mul_zero, add_zero] at h1
    exact h1
  obtain ⟨ρ, rfl⟩ := Submodule.mem_span_singleton.mp (hr1 l hl hl0)
  have hr4 : herm σ r p₄ = 0 := herm_eq_zero_comm σ hσ hr3
  have e1 : herm σ (ρ • r) (ρ • r + t • p₄) =
      σ ρ * ρ * herm σ r r + t * (σ ρ * herm σ r p₄) := by
    simp only [herm_add_right, herm_smul_right, herm_smul_left]
    ring
  have hσρ : σ ρ * ρ * herm σ r r = 0 := by
    have h2 := hperp (ρ • r) (Submodule.mem_sup_left hl)
    rw [e1] at h2
    simp only [hr4, mul_zero, add_zero] at h2
    exact h2
  have hρ0 : ρ = 0 := by
    rcases mul_eq_zero.mp hσρ with h | h
    · rcases mul_eq_zero.mp h with h' | h'
      · have hh := hσ ρ
        rw [h', map_zero] at hh
        exact hh.symm
      · exact h'
    · exact absurd h hr2
  subst hρ0
  have ht : t = 0 := by
    have h3 := hperp p' (Submodule.mem_sup_left hp'L)
    simp only [zero_smul, zero_add, herm_smul_right] at h3
    rcases mul_eq_zero.mp h3 with h | h
    · exact h
    · exact absurd h hp'
  subst ht
  simp

end CFSG.RankThree.GF2n.Smith81.S81V

module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X3AutIso
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.ComponentClassification.PresentationLocalSymplecticSix

public section

namespace CFSG.Quasithin

namespace Sp4Inf

open Equiv

noncomputable def conjAlt6 : Perm (Fin 6) →* MulAut ↥(alternatingGroup (Fin 6)) :=
  MulAut.conjNormal (H := alternatingGroup (Fin 6))

theorem coe_conjAlt6 (g : Perm (Fin 6)) (x : ↥(alternatingGroup (Fin 6))) :
    ((conjAlt6 g x : ↥(alternatingGroup (Fin 6))) : Perm (Fin 6)) = g * x * g⁻¹ :=
  MulAut.conjNormal_apply g x

theorem conjAlt6_injective : Function.Injective conjAlt6 := by
  rw [injective_iff_map_eq_one]
  intro g hg
  have hc : g ∈ Subgroup.centralizer ((alternatingGroup (Fin 6) : Subgroup (Perm (Fin 6))) :
      Set (Perm (Fin 6))) := by
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    have := congrArg (fun φ : MulAut ↥(alternatingGroup (Fin 6)) =>
      ((φ ⟨a, ha⟩ : ↥(alternatingGroup (Fin 6))) : Perm (Fin 6))) hg
    simp only [coe_conjAlt6, MulAut.one_apply] at this
    calc a * g = (g * a * g⁻¹) * g := by rw [this]
      _ = g * a := by group
  rw [CFSG.ComponentClassification.PresentationLocal.centralizer_alternatingGroup_eq_bot (by simp)]
    at hc
  exact Subgroup.mem_bot.mp hc

theorem index_range_conjAlt6 : conjAlt6.range.index = 2 := by
  have h1 := conjAlt6.range.card_mul_index
  have hcard : Nat.card conjAlt6.range = 720 := by
    rw [Nat.card_congr (MonoidHom.ofInjective conjAlt6_injective).toEquiv.symm,
      Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]
    decide
  rw [hcard, CFSG.QuasithinUnique.Setup.X3Aut.card_mulAut_alt6] at h1
  omega

theorem exists_conj_mul_of_not_induced {τ θ : MulAut ↥(alternatingGroup (Fin 6))}
    (hτ : τ ∉ conjAlt6.range) (hθ : θ ∉ conjAlt6.range) :
    ∃ g : Perm (Fin 6), θ = conjAlt6 g * τ := by
  obtain ⟨a, ha⟩ := Subgroup.index_eq_two_iff.mp index_range_conjAlt6
  have h1 : τ * a ∈ conjAlt6.range := by
    rcases ha τ with h | h
    · exact h.1
    · exact absurd h.1 hτ
  have h2 : θ * a ∈ conjAlt6.range := by
    rcases ha θ with h | h
    · exact h.1
    · exact absurd h.1 hθ
  have h3 : θ * τ⁻¹ ∈ conjAlt6.range := by
    have := conjAlt6.range.mul_mem h2 (conjAlt6.range.inv_mem h1)
    simpa [mul_assoc] using this
  obtain ⟨g, hg⟩ := h3
  exact ⟨g, by rw [hg]; group⟩

end Sp4Inf

end CFSG.Quasithin

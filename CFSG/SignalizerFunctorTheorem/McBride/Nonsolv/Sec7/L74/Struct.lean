module

public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.Sec7.StructA
public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.Sec7.StructB

public section

open CFSG.Open

universe u

namespace CFSG.SignalizerFunctorTheorem.McBride.Nonsolv

namespace L74

variable {p : ℕ} {G : Type u} [Group G] [Finite G] {A : Subgroup G} {θ : G → Subgroup G}
  {r : ℕ}

theorem exists_isRegFam_ind
    (h : Counterexample p A θ) {a : G} (ha : a ∈ A) (ha1 : a ≠ 1)
    (hT : TypeA p A θ ∨ ∃ E K : Subgroup G, TypeBCore p A θ E K ∧ a ∉ E) :
    ∃ N : Subgroup G, IsRegFam A (θ a) (Ind (θ a)) N := by
  have hE := h.zpowers_mem_E1 ha ha1
  have hθ := h.isFunctor.thetaOf_zpowers ha ha1
  rcases hT with hA | ⟨E, K, hB, haE⟩
  · refine ⟨Subgroup.zpowers a, ?_⟩
    rw [← hθ, h.ind_eq_lcal_line_of_typeA hA hE]
    exact h.isRegFam_line_of_typeA hA hE
  · have hFE : Subgroup.zpowers a ≠ E := fun heq => haE (heq ▸ Subgroup.mem_zpowers a)
    refine ⟨E ⊔ Subgroup.zpowers a, ?_⟩
    rw [← hθ, h.ind_eq_lcal_line_of_typeB hB hE hFE]
    exact h.isRegFam_line_of_typeB hB hE hFE

theorem dvd_card_apply
    (h : Counterexample p A θ) (hr : InPiTheta A θ r) {a : G} (ha : a ∈ A)
    (ha1 : a ≠ 1) (hT : TypeA p A θ ∨ ∃ E K : Subgroup G, TypeBCore p A θ E K ∧ a ∉ E) :
    r ∣ Nat.card (θ a) := by
  obtain ⟨hrp, b, hb, hb1, hrb⟩ := hr
  have hD : Nat.card (thetaOf θ A) ∣ Nat.card (θ a) :=
    Subgroup.card_dvd_of_le (thetaOf_le_apply ha ha1)
  rcases hT with hA | ⟨E, K, hB, haE⟩
  · have h1 := h.card_line_of_typeA hA (h.zpowers_mem_E1 ha ha1)
    have h2 := h.card_line_of_typeA hA (h.zpowers_mem_E1 hb hb1)
    rw [h.isFunctor.thetaOf_zpowers ha ha1] at h1
    rw [h.isFunctor.thetaOf_zpowers hb hb1] at h2
    exact (h1.trans h2.symm) ▸ hrb
  · have hFE : Subgroup.zpowers a ≠ E := fun heq => haE (heq ▸ Subgroup.mem_zpowers a)
    by_cases hbE : Subgroup.zpowers b = E
    · have h3 := h.card_E_of_typeB hB
      rw [← hbE, h.isFunctor.thetaOf_zpowers hb hb1] at h3
      rw [h3] at hrb
      exact (hrp.dvd_of_dvd_pow hrb).trans hD
    · have h1 := h.card_line_of_typeB hB (h.zpowers_mem_E1 ha ha1) hFE
      have h2 := h.card_line_of_typeB hB (h.zpowers_mem_E1 hb hb1) hbE
      rw [h.isFunctor.thetaOf_zpowers ha ha1] at h1
      rw [h.isFunctor.thetaOf_zpowers hb hb1] at h2
      exact (h1.trans h2.symm) ▸ hrb

end L74

end CFSG.SignalizerFunctorTheorem.McBride.Nonsolv

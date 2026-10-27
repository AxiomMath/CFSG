module

public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.Sec7.T73.InfInd

public section

open CFSG.Open

universe u

namespace CFSG.SignalizerFunctorTheorem.McBride.Nonsolv

namespace Counterexample

variable {p : ℕ} {G : Type u} [Group G] [Finite G] {A : Subgroup G} {θ : G → Subgroup G}
  {r : ℕ} {S : Subgroup G} {E K : Subgroup G}

theorem inf_zOf_le
    (h : Counterexample p A θ) (hr : InPiTheta A θ r) (hS : IsSr p A θ r S)
    (hB : TypeBCore p A θ E K) {F : Subgroup G} (hF : F ∈ signalizerFunctorEk p 1 A)
    (hFE : F ≠ E) :
    zOf (S ⊓ Subgroup.centralizer (E : Set G)) ⊓ zOf (S ⊓ Subgroup.centralizer (F : Set G)) ≤
      zOf S := by
  intro x hx
  have hπ := h.sup_mem_E2_of_ne hB.mem hF hFE.symm
  have hxY := T73Inf.inf_zOf_le_iSup_projIn h hr hS hB hF hFE hx
  have hline : ∀ b ∈ E ⊔ F, b ≠ 1 → ∀ w ∈ S ⊓ Subgroup.centralizer {b}, w * x = x * w := by
    intro b hb hb1 w hw
    by_cases hbE : b ∈ E
    · have hEb := h.line_eq_zpowers hB.mem hbE hb1
      have hw' : w ∈ S ⊓ Subgroup.centralizer (E : Set G) := by
        rw [hEb, centralizer_zpowers_eq_singleton]
        exact hw
      exact (mem_zOf_iff.mp (Subgroup.mem_inf.mp hx).1).2 w hw'
    ·
      have hT : Subgroup.zpowers b ∈ signalizerFunctorEk p 1 A := h.zpowers_mem_E1 (hπ.1 hb) hb1
      have hTE : Subgroup.zpowers b ≠ E := fun heq => hbE (heq ▸ Subgroup.mem_zpowers b)
      have hπ' := h.sup_mem_E2_of_ne hB.mem hT hTE.symm
      have hsup : E ⊔ Subgroup.zpowers b = E ⊔ F :=
        Subgroup.eq_of_le_of_card_ge (sup_le le_sup_left (Subgroup.zpowers_le.mpr hb))
          (by rw [hπ.2, hπ'.2])
      have hI := T73Inf.iSup_projIn_le_inf_zOf h hr hS hB hT hTE
      rw [hsup] at hI
      have hxT := (Subgroup.mem_inf.mp (hI hxY)).2
      refine (mem_zOf_iff.mp hxT).2 w ?_
      rw [centralizer_zpowers_eq_singleton]
      exact hw
  have hSx : S ≤ Subgroup.centralizer {x} := by
    refine (eq_iSup_inf_centralizer_of_isSr h hr hS hπ).le.trans ?_
    refine iSup_le fun b => iSup_le fun hb => iSup_le fun hb1 w hw => ?_
    exact Subgroup.mem_centralizer_singleton_iff.mpr (hline b hb hb1 w hw)
  refine mem_zOf_iff.mpr ⟨(zOf_le _ (Subgroup.mem_inf.mp hx).1).1, fun w hw => ?_⟩
  exact Subgroup.mem_centralizer_singleton_iff.mp (hSx hw)

end Counterexample

end CFSG.SignalizerFunctorTheorem.McBride.Nonsolv

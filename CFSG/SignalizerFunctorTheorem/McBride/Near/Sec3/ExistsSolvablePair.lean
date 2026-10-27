module

public import CFSG.SignalizerFunctorTheorem.McBride.Near.Sec3.IntrThm32

public section

open CFSG.Open

namespace CFSG.SignalizerFunctorTheorem.McBride.Near

variable {G : Type*} [Group G] [Finite G] {p : ℕ} {A : Subgroup G} {θ : G → Subgroup G}

theorem exists_solvable_pair'
    (hθ : NearFunctor p A θ) {Y : Subgroup G}
    (_hY : Y ∈ dset p A θ) {X₁ X₂ : Subgroup G} (h : (X₁, X₂) ∈ pairsY p A θ Y) :
    ∃ Z₁ Z₂ : Subgroup G, Z₁ ≤ X₁ ∧ Z₂ ≤ X₂ ∧ (Z₁, Z₂) ∈ pairsY p A θ Y ∧
      Group.IsSolvable Z₂ ∧ CyclicMod A (secCenIn A Z₁ Z₂) := by
  have hXm : X₁ ⊔ dsub A θ ∈ mtil p A θ := sup_dsub_mem_mtil hθ h.1.1
  have hact : NearAsolvAction p A (X₁ ⊔ dsub A θ) :=
    { prime := hθ.prime
      odd := hθ.odd
      elemAbelian := hθ.elemAbelian
      admits := hXm.1.1
      nearPSolvable := hXm.1.2.2.2.1
      solvable_cen := hXm.1.2.2.2.2 }
  have heq := pairsYX_eq_iPairsY (Y := Y) hθ hXm
  have hP : (X₁, X₂) ∈ iPairsY A (X₁ ⊔ dsub A θ) Y := by
    rw [← heq]
    exact ⟨h, le_sup_left⟩
  obtain ⟨Z₁, Z₂, hZ₁, hZ₂, hZ, hs, hc⟩ := iThm32 hact hP
  rw [← heq] at hZ
  exact ⟨Z₁, Z₂, hZ₁, hZ₂, hZ.1, hs, hc⟩

end CFSG.SignalizerFunctorTheorem.McBride.Near

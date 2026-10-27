module

public import CFSG.Quasithin.Vol2.GoldschmidtF431Un5OutLieSet
public import CFSG.Quasithin.Vol2.GoldschmidtF431Un5LieC

public noncomputable section

namespace CFSG.Quasithin.H13.F431.Un.OL5

set_option linter.unusedSectionVars false

open Matrix Subgroup CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.RankThree.PartOne.U5K.Hyp CFSG.Quasithin.H13.Sec53F.Unit CFSG.LocalAnalysis.EvenBN.U5
  CFSG.Quasithin.H13.F431.Un

variable {f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 f K)

theorem fStab5_U : FStab5 h (hypProjUnitriangular h 2 1) := fun φ x => fieldP_stab_U h φ x

theorem fieldAut_mem_u5PtStab (φ : K ≃+* K) (g : hypSU h 2 1) :
    fieldAut h φ g ∈ u5PtStab h ↔ g ∈ u5PtStab h := by
  rw [mem_u5PtStab_iff, mem_u5PtStab_iff]
  constructor
  · intro H a ha
    have := H a ha
    rw [mat_fieldAut] at this
    exact φ.injective (by simpa using this)
  · intro H a ha
    rw [mat_fieldAut]
    simp [H a ha]

theorem fieldAut_mem_u5LnStab (φ : K ≃+* K) (g : hypSU h 2 1) :
    fieldAut h φ g ∈ u5LnStab h ↔ g ∈ u5LnStab h := by
  rw [mem_u5LnStab_iff, mem_u5LnStab_iff]
  constructor
  · intro H a b hb ha
    have := H a b hb ha
    rw [mat_fieldAut] at this
    exact φ.injective (by simpa using this)
  · intro H a b hb ha
    rw [mat_fieldAut]
    simp [H a b hb ha]

theorem fStab5_Pt : FStab5 h (u5PtP h) := fun φ x =>
  fieldP_stab h φ (u5PtStab h) (fieldAut_mem_u5PtStab h φ) x

theorem fStab5_Ln : FStab5 h (u5LnP h) := fun φ x =>
  fieldP_stab h φ (u5LnStab h) (fieldAut_mem_u5LnStab h φ) x

theorem cj5_mem_autStab {B : Subgroup (hypPSU h 2 1)} {s : hypPSU h 2 1} (hs : s ∈ B) :
    cj5 h s ∈ autStab B := fun x => by
  change x ∈ B ↔ s * x * s⁻¹ ∈ B
  exact ⟨fun hx => B.mul_mem (B.mul_mem hs hx) (B.inv_mem hs), fun hx => by
    have := B.mul_mem (B.mul_mem (B.inv_mem hs) hx) hs
    simpa [mul_assoc] using this⟩

theorem fa5_mem_autStab {B : Subgroup (hypPSU h 2 1)} (hB : FStab5 h B) (φ : K ≃+* K) :
    fa5 h φ ∈ autStab B := fun x => (hB φ x).symm

theorem Ssd5_le_autStab {B B' : Subgroup (hypPSU h 2 1)} {hB : FStab5 h B} (hB' : FStab5 h B')
    (hBB' : B ≤ B') (F : Subgroup (K ≃+* K)) : Ssd5 h B hB F ≤ autStab B' := by
  rintro _ ⟨s, hs, φ, -, rfl⟩
  exact (autStab B').mul_mem (cj5_mem_autStab h (hBB' hs)) (fa5_mem_autStab h hB' φ)

end CFSG.Quasithin.H13.F431.Un.OL5

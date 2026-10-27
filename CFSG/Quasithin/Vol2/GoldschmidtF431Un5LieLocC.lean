module

public import CFSG.Quasithin.Vol2.GoldschmidtF431Un5LieLocB

public noncomputable section

namespace CFSG.Quasithin.H13.F431.Un.L5

open Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.RankThree.PartOne.U5K.Hyp
  CFSG.LocalAnalysis.EvenBN.U5 CFSG.LocalAnalysis.ComponentInitial
open scoped commutatorElement

variable {f : ℕ} {K : Type} [Field K] {h : UnitaryFieldData 2 f K}

theorem isHerm_add {Y Y' : Matrix (Fin 2) (Fin 2) K} (hY : IsHerm h Y) (hY' : IsHerm h Y') :
    IsHerm h (Y + Y') := by
  unfold IsHerm at *
  have : Y + Y' + ((Y + Y').map h.bar)ᵀ = (Y + (Y.map h.bar)ᵀ) + (Y' + (Y'.map h.bar)ᵀ) := by
    simp only [Matrix.map_add _ (map_add h.bar), Matrix.transpose_add]
    abel
  rw [this, hY, hY', add_zero]

theorem vSU_mul {Y Y' : Matrix (Fin 2) (Fin 2) K} (hY : IsHerm h Y) (hY' : IsHerm h Y') :
    vSU h Y hY * vSU h Y' hY' = vSU h (Y + Y') (isHerm_add hY hY') := by
  apply mat_injective
  rw [mat_mul, mat_vSU, mat_vSU, mat_vSU, oddUni_mul]
  simp

theorem Yof_mul_Vsub {g g' : hypSU h 2 1} (hg : g ∈ Vsub h) (hg' : g' ∈ Vsub h) :
    Yof (g * g') = Yof g + Yof g' := by
  obtain ⟨-, Y, hY⟩ := hg
  obtain ⟨-, Y', hY'⟩ := hg'
  have : mat (g * g') = oddUni h 0 (Y + Y') := by
    rw [mat_mul, hY, hY', oddUni_mul]
    simp
  rw [Yof_eq this, Yof_eq hY, Yof_eq hY']

theorem inv_eq_self_of_mem_Vsub {g : hypSU h 2 1} (hg : g ∈ Vsub h) : g⁻¹ = g :=
  inv_eq_of_mul_eq_one_right (Vsub_sq hg)

theorem Yof_inv_Vsub {g : hypSU h 2 1} (hg : g ∈ Vsub h) : Yof g⁻¹ = Yof g := by
  rw [inv_eq_self_of_mem_Vsub hg]

theorem commutator_levHom_Vsub (A : SpecialLinearGroup (Fin 2) h.fixedField) {v : hypSU h 2 1}
    (hv : v ∈ Vsub h) : ⁅levHom h A, v⁆ ∈ Vsub h ∧
      Yof ⁅levHom h A, v⁆ = slM A * Yof v * (slM A)ᵀ + Yof v := by
  obtain ⟨h1, h2⟩ := Yof_levHom_conj A hv
  rw [commutatorElement_def]
  refine ⟨mul_mem h1 (inv_mem hv), ?_⟩
  rw [Yof_mul_Vsub h1 (inv_mem hv), h2, Yof_inv_Vsub hv]

@[expose] def vE11 (c : h.fixedField) : hypSU h 2 1 :=
  vSU h (hermM h c 0 0) (hermM_isHerm (h.mem_fixedField.1 c.2) (map_zero h.bar))

@[expose] def vE22 (c : h.fixedField) : hypSU h 2 1 :=
  vSU h (hermM h 0 c 0) (hermM_isHerm (map_zero h.bar) (h.mem_fixedField.1 c.2))

@[expose] def vJ (c : h.fixedField) : hypSU h 2 1 :=
  vSU h (hermM h 0 0 c) (hermM_isHerm (map_zero h.bar) (map_zero h.bar))

theorem Yof_vE11 (c : h.fixedField) : Yof (vE11 c) = !![(c : K), 0; 0, 0] := by
  rw [vE11, Yof_vSU]
  simp [hermM]

theorem Yof_vE22 (c : h.fixedField) : Yof (vE22 c) = !![0, 0; 0, (c : K)] := by
  rw [vE22, Yof_vSU]
  simp [hermM]

theorem Yof_vJ (c : h.fixedField) : Yof (vJ c) = !![0, (c : K); (c : K), 0] := by
  have hc := h.mem_fixedField.1 c.2
  rw [vJ, Yof_vSU]
  simp [hermM, hc]

theorem vE11_mem_Vt (c : h.fixedField) : vE11 c ∈ Vt h :=
  vSU_mem_Vt _ (by simp [hermM])

theorem vE22_mem_Vt (c : h.fixedField) : vE22 c ∈ Vt h :=
  vSU_mem_Vt _ (by simp [hermM])

theorem vJ_mem_Vt (c : h.fixedField) : vJ c ∈ Vt h :=
  vSU_mem_Vt _ (by simp [hermM, h.mem_fixedField.1 c.2])

theorem vJ_mem_Uct (c : h.fixedField) : vJ c ∈ Uct h :=
  vSU_mem_Uct _ ⟨by simp [hermM], by simp [hermM], by simp [hermM, h.mem_fixedField.1 c.2]⟩

theorem vE11_add (c c' : h.fixedField) : vE11 (c + c') = vE11 c * vE11 c' := by
  rw [vE11, vE11, vE11, vSU_mul]
  congr 1
  rw [hermM_add]
  simp

theorem mem_Vt_iff {g : hypSU h 2 1} :
    g ∈ Vt h ↔ ∃ a d b : h.fixedField, g = vE11 a * vE22 d * vJ b := by
  constructor
  · intro hg
    obtain ⟨Y, hY, hs, rfl⟩ := mem_vsub_iff.1 hg
    obtain ⟨h00, h11, h10⟩ := isHerm_iff.1 hY
    have hb : h.bar (Y 0 1) = Y 0 1 := by rw [← h10, hs]
    refine ⟨⟨Y 0 0, h.mem_fixedField.2 h00⟩, ⟨Y 1 1, h.mem_fixedField.2 h11⟩,
      ⟨Y 0 1, h.mem_fixedField.2 hb⟩, ?_⟩
    rw [vE11, vE22, vJ, vSU_mul, vSU_mul]
    congr 1
    rw [hermM_add, hermM_add]
    simpa using eq_hermM hY
  · rintro ⟨a, d, b, rfl⟩
    exact mul_mem (mul_mem (vE11_mem_Vt a) (vE22_mem_Vt d)) (vJ_mem_Vt b)

end CFSG.Quasithin.H13.F431.Un.L5

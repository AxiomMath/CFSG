module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LieType.SteinbergBRParabolicTransport
public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherSubflag

public section

namespace CFSG.Quasithin.QP

open Matrix Module CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.LieType.SteinbergBR.BlockPar

variable {F : Type} [Field F]

theorem mem_stabilizer_flag1_iff (g : SpecialLinearGroup (Fin 3) F) :
    g ∈ stabilizer (flagSpace 3 F 1) ↔
      (g : Matrix (Fin 3) (Fin 3) F) 1 0 = 0 ∧ (g : Matrix (Fin 3) (Fin 3) F) 2 0 = 0 := by
  constructor
  · intro hg
    have he : (Pi.single 0 1 : Fin 3 → F) ∈ flagSpace 3 F 1 := by
      rw [mem_flagSpace]
      intro k hk
      have : k ≠ 0 := fun h => by subst h; simp at hk
      simp [this]
    have hmem : (g : Matrix (Fin 3) (Fin 3) F) *ᵥ Pi.single 0 1 ∈ flagSpace 3 F 1 := by
      have h := mem_stabilizer.1 hg
      rw [← h]
      exact Submodule.mem_map_of_mem (f := mulVecLin (g : Matrix (Fin 3) (Fin 3) F)) he
    have h1 := mem_flagSpace.1 hmem 1 (le_refl _)
    have h2 := mem_flagSpace.1 hmem 2 (by decide)
    simp at h1 h2
    exact ⟨h1, h2⟩
  · rintro ⟨h10, h20⟩
    apply mem_stabilizer_of_map_le
    rintro _ ⟨v, hv, rfl⟩
    rw [mulVecLin_apply]
    have hv' : v ∈ flagSpace 3 F 1 := hv
    have hv1 := mem_flagSpace.1 hv' 1 (le_refl _)
    have hv2 := mem_flagSpace.1 hv' 2 (by decide)
    rw [mem_flagSpace]
    intro k hk
    have hk' : k = 1 ∨ k = 2 := by
      fin_cases k <;> simp_all
    rcases hk' with rfl | rfl <;>
      simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three, h10, h20, hv1, hv2]

@[expose] def leviMat : ↥(stabilizer (flagSpace 3 F 1)) →* Matrix (Fin 2) (Fin 2) F where
  toFun g := Matrix.of fun i j => (g : SpecialLinearGroup (Fin 3) F).1 i.succ j.succ
  map_one' := by
    ext i j
    simp [Matrix.one_apply, Fin.succ_inj]
  map_mul' g h := by
    ext i j
    obtain ⟨hg1, hg2⟩ := (mem_stabilizer_flag1_iff _).1 g.2
    have hg : ∀ i : Fin 2, (g : SpecialLinearGroup (Fin 3) F).1 i.succ 0 = 0 := fun i => by
      fin_cases i
      · exact hg1
      · exact hg2
    simp only [Subgroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, Matrix.of_apply, Matrix.mul_apply,
      Fin.sum_univ_succ, hg i, zero_mul, zero_add]

@[expose] def levi : ↥(stabilizer (flagSpace 3 F 1)) →* GL (Fin 2) F := leviMat.toHomUnits

theorem coe_levi (g : ↥(stabilizer (flagSpace 3 F 1))) :
    ((levi g : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) = leviMat g := rfl

theorem leviMat_apply (g : ↥(stabilizer (flagSpace 3 F 1))) (i j : Fin 2) :
    leviMat g i j = (g : SpecialLinearGroup (Fin 3) F).1 i.succ j.succ := rfl

theorem levi_surjective : Function.Surjective (levi (F := F)) := by
  intro A
  set u : Fˣ := Matrix.GeneralLinearGroup.det A with hu
  set M : Matrix (Fin 3) (Fin 3) F :=
    !![((u⁻¹ : Fˣ) : F), 0, 0; 0, (A : Matrix (Fin 2) (Fin 2) F) 0 0, (A : Matrix (Fin 2) (Fin 2) F) 0 1;
      0, (A : Matrix (Fin 2) (Fin 2) F) 1 0, (A : Matrix (Fin 2) (Fin 2) F) 1 1] with hM
  have hdet : M.det = 1 := by
    rw [det_fin_three]
    have h2 : ((u : Fˣ) : F) = (A : Matrix (Fin 2) (Fin 2) F).det := by
      rw [hu, Matrix.GeneralLinearGroup.val_det_apply]
    have h3 : (A : Matrix (Fin 2) (Fin 2) F).det =
        (A : Matrix (Fin 2) (Fin 2) F) 0 0 * (A : Matrix (Fin 2) (Fin 2) F) 1 1 -
          (A : Matrix (Fin 2) (Fin 2) F) 0 1 * (A : Matrix (Fin 2) (Fin 2) F) 1 0 := det_fin_two _
    have h4 : ((u⁻¹ : Fˣ) : F) * ((u : Fˣ) : F) = 1 := by
      rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
    simp [hM, Units.val_inv_eq_inv_val]
    rw [h2, h3, Units.val_inv_eq_inv_val] at h4
    linear_combination h4
  have hg : (⟨M, hdet⟩ : SpecialLinearGroup (Fin 3) F) ∈ stabilizer (flagSpace 3 F 1) :=
    (mem_stabilizer_flag1_iff _).2 ⟨by show M 1 0 = 0; simp [hM], by show M 2 0 = 0; simp [hM]⟩
  refine ⟨⟨⟨M, hdet⟩, hg⟩, ?_⟩
  apply Units.ext
  ext i j
  rw [coe_levi, leviMat_apply]
  fin_cases i <;> fin_cases j <;> simp [hM]

theorem levi_eq_one_iff {g : SpecialLinearGroup (Fin 3) F} (hg : g ∈ stabilizer (flagSpace 3 F 1)) :
    levi ⟨g, hg⟩ = 1 ↔ g ∈ radU F (flagSpace 3 F 1) := by
  obtain ⟨hg1, hg2⟩ := (mem_stabilizer_flag1_iff g).1 hg
  constructor
  · intro h
    have hb : ∀ i j : Fin 2, (g : Matrix (Fin 3) (Fin 3) F) i.succ j.succ = (1 : Matrix (Fin 2) (Fin 2) F) i j :=
      fun i j => by
        have := congrArg (fun A : GL (Fin 2) F => (A : Matrix (Fin 2) (Fin 2) F) i j) h
        simpa [coe_levi, leviMat_apply] using this
    have h11 : (g : Matrix (Fin 3) (Fin 3) F) 1 1 = 1 := by simpa using hb 0 0
    have h12 : (g : Matrix (Fin 3) (Fin 3) F) 1 2 = 0 := by simpa using hb 0 1
    have h21 : (g : Matrix (Fin 3) (Fin 3) F) 2 1 = 0 := by simpa using hb 1 0
    have h22 : (g : Matrix (Fin 3) (Fin 3) F) 2 2 = 1 := by simpa using hb 1 1
    have h00 : (g : Matrix (Fin 3) (Fin 3) F) 0 0 = 1 := by
      have hd : (g : Matrix (Fin 3) (Fin 3) F).det = 1 := g.2
      rw [det_fin_three, hg1, hg2, h11, h12, h21, h22] at hd
      linear_combination hd
    refine ⟨fun v => ?_, fun w hw => ?_⟩
    · rw [mem_flagSpace]
      intro k hk
      have hk' : k = 1 ∨ k = 2 := by fin_cases k <;> simp_all
      rcases hk' with rfl | rfl <;>
        simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three, hg1, hg2, h11, h12, h21, h22]
    · have hw1 := mem_flagSpace.1 hw 1 (le_refl _)
      have hw2 := mem_flagSpace.1 hw 2 (by decide)
      funext k
      fin_cases k <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three, hg1, hg2, h00, hw1, hw2]
  · intro hr
    apply Units.ext
    ext i j
    rw [coe_levi, leviMat_apply]
    have h := mem_flagSpace.1 (hr.1 (Pi.single j.succ 1)) i.succ (by fin_cases i <;> simp)
    simp [Pi.single_apply] at h
    simp [Matrix.one_apply]
    exact sub_eq_zero.1 h

end CFSG.Quasithin.QP

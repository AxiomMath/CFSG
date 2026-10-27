module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherSubflag

public section

namespace CFSG.Quasithin.H13.Ch4.T425C27.SL3

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag

variable {F : Type} [Field F]

theorem mulVec_three (g : Matrix (Fin 3) (Fin 3) F) (v : Fin 3 → F) (j : Fin 3) :
    (g *ᵥ v) j = g j 0 * v 0 + g j 1 * v 1 + g j 2 * v 2 := by
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three]

theorem mem_stab_one_iff {g : SpecialLinearGroup (Fin 3) F} :
    g ∈ stabilizer (flagSpace 3 F 1) ↔
      (g : Matrix (Fin 3) (Fin 3) F) 1 0 = 0 ∧ (g : Matrix (Fin 3) (Fin 3) F) 2 0 = 0 := by
  constructor
  · intro hg
    have he : (Pi.single 0 1 : Fin 3 → F) ∈ flagSpace 3 F 1 := by
      rw [mem_flagSpace]
      intro j hj
      have : j ≠ 0 := fun h => by subst h; simp at hj
      simp [this]
    have hm : (g : Matrix (Fin 3) (Fin 3) F) *ᵥ Pi.single 0 1 ∈ flagSpace 3 F 1 := by
      rw [← mem_stabilizer.mp hg]
      exact ⟨_, he, rfl⟩
    rw [mem_flagSpace] at hm
    have h1 := hm 1 (by decide)
    have h2 := hm 2 (by decide)
    simp [mulVec_three] at h1 h2
    exact ⟨h1, h2⟩
  · rintro ⟨h1, h2⟩
    refine mem_stabilizer_of_map_le ?_
    rintro _ ⟨v, hv, rfl⟩
    rw [SetLike.mem_coe, mem_flagSpace] at hv
    rw [mem_flagSpace]
    intro j hj
    rw [mulVecLin_apply, mulVec_three, hv 1 (by decide), hv 2 (by decide)]
    fin_cases j
    · simp at hj
    · simp [h1]
    · simp [h2]

theorem mem_stab_two_iff {g : SpecialLinearGroup (Fin 3) F} :
    g ∈ stabilizer (flagSpace 3 F 2) ↔
      (g : Matrix (Fin 3) (Fin 3) F) 2 0 = 0 ∧ (g : Matrix (Fin 3) (Fin 3) F) 2 1 = 0 := by
  constructor
  · intro hg
    have hm : ∀ k : Fin 3, (k : ℕ) < 2 →
        (g : Matrix (Fin 3) (Fin 3) F) *ᵥ Pi.single k 1 ∈ flagSpace 3 F 2 := by
      intro k hk
      rw [← mem_stabilizer.mp hg]
      refine ⟨_, ?_, rfl⟩
      rw [SetLike.mem_coe, mem_flagSpace]
      intro j hj
      have : j ≠ k := fun h => by subst h; omega
      simp [this]
    have h0 := mem_flagSpace.mp (hm 0 (by decide)) 2 (by decide)
    have h1 := mem_flagSpace.mp (hm 1 (by decide)) 2 (by decide)
    simp [mulVec_three] at h0 h1
    exact ⟨h0, h1⟩
  · rintro ⟨h0, h1⟩
    refine mem_stabilizer_of_map_le ?_
    rintro _ ⟨v, hv, rfl⟩
    rw [SetLike.mem_coe, mem_flagSpace] at hv
    rw [mem_flagSpace]
    intro j hj
    rw [mulVecLin_apply, mulVec_three, hv 2 (by decide)]
    fin_cases j
    · simp at hj
    · simp at hj
    · simp [h0, h1]

@[expose] def blkOne (g : Matrix (Fin 3) (Fin 3) F) : Matrix (Fin 2) (Fin 2) F :=
  g.submatrix Fin.succ Fin.succ

@[expose] def blkTwo (g : Matrix (Fin 3) (Fin 3) F) : Matrix (Fin 2) (Fin 2) F :=
  g.submatrix Fin.castSucc Fin.castSucc

theorem blkOne_mul {g h : Matrix (Fin 3) (Fin 3) F} (hg : g 1 0 = 0 ∧ g 2 0 = 0) :
    blkOne (g * h) = blkOne g * blkOne h := by
  ext i j
  have : g i.succ 0 = 0 := by fin_cases i; exacts [hg.1, hg.2]
  show (g * h) i.succ j.succ = ∑ k : Fin 2, g i.succ k.succ * h k.succ j.succ
  rw [mul_apply, Fin.sum_univ_succ, this, zero_mul, zero_add]

theorem blkTwo_mul {g h : Matrix (Fin 3) (Fin 3) F} (hh : h 2 0 = 0 ∧ h 2 1 = 0) :
    blkTwo (g * h) = blkTwo g * blkTwo h := by
  ext i j
  have : h (Fin.last 2) j.castSucc = 0 := by fin_cases j; exacts [hh.1, hh.2]
  show (g * h) i.castSucc j.castSucc =
    ∑ k : Fin 2, g i.castSucc k.castSucc * h k.castSucc j.castSucc
  rw [mul_apply, Fin.sum_univ_castSucc, this, mul_zero, add_zero]

theorem det_eq_blkOne {g : Matrix (Fin 3) (Fin 3) F} (hg : g 1 0 = 0 ∧ g 2 0 = 0) :
    g.det = g 0 0 * (blkOne g).det := by
  rw [det_fin_three, det_fin_two]
  simp [blkOne, hg.1, hg.2]
  ring

theorem det_eq_blkTwo {g : Matrix (Fin 3) (Fin 3) F} (hg : g 2 0 = 0 ∧ g 2 1 = 0) :
    g.det = (blkTwo g).det * g 2 2 := by
  rw [det_fin_three, det_fin_two]
  simp [blkTwo, hg.1, hg.2]
  ring

theorem det_blkOne_ne_zero {g : SpecialLinearGroup (Fin 3) F}
    (hg : g ∈ stabilizer (flagSpace 3 F 1)) : (blkOne (g : Matrix (Fin 3) (Fin 3) F)).det ≠ 0 :=
  fun h0 => by
    have h := det_eq_blkOne (mem_stab_one_iff.mp hg)
    rw [h0, mul_zero] at h
    exact one_ne_zero (g.prop.symm.trans h)

theorem det_blkTwo_ne_zero {g : SpecialLinearGroup (Fin 3) F}
    (hg : g ∈ stabilizer (flagSpace 3 F 2)) : (blkTwo (g : Matrix (Fin 3) (Fin 3) F)).det ≠ 0 :=
  fun h0 => by
    have h := det_eq_blkTwo (mem_stab_two_iff.mp hg)
    rw [h0, zero_mul] at h
    exact one_ne_zero (g.prop.symm.trans h)

@[expose] noncomputable def rhoOne : ↥(stabilizer (flagSpace 3 F 1)) →* GL (Fin 2) F where
  toFun x := GeneralLinearGroup.mkOfDetNeZero (blkOne ((x : SpecialLinearGroup (Fin 3) F) :
    Matrix (Fin 3) (Fin 3) F)) (det_blkOne_ne_zero x.2)
  map_one' := Units.ext (show blkOne (1 : Matrix (Fin 3) (Fin 3) F) = 1 from
    submatrix_one _ (Fin.succ_injective _))
  map_mul' x _ := Units.ext (blkOne_mul (mem_stab_one_iff.mp x.2))

@[expose] noncomputable def rhoTwo : ↥(stabilizer (flagSpace 3 F 2)) →* GL (Fin 2) F where
  toFun x := GeneralLinearGroup.mkOfDetNeZero (blkTwo ((x : SpecialLinearGroup (Fin 3) F) :
    Matrix (Fin 3) (Fin 3) F)) (det_blkTwo_ne_zero x.2)
  map_one' := Units.ext (show blkTwo (1 : Matrix (Fin 3) (Fin 3) F) = 1 from
    submatrix_one _ (Fin.castSucc_injective _))
  map_mul' _ y := Units.ext (blkTwo_mul (mem_stab_two_iff.mp y.2))

end CFSG.Quasithin.H13.Ch4.T425C27.SL3

module

public import CFSG.RankThree.PartOne.KC.UnitaryCrossPrimeGroup
public import CFSG.RankThree.PartOne.KC.UnitaryCrossPrimeLinear

public section

namespace CFSG.RankThree.PartOne.KCLinComm

open Matrix
open scoped commutatorElement

section PiGL

variable {ι : Type*} [DecidableEq ι] {E : ι → Type*} [∀ b, Field (E b)] {m : ι → ℕ}

abbrev PiGL (E : ι → Type*) [∀ b, Field (E b)] (m : ι → ℕ) : Type _ :=
  ∀ b, GL (Fin (m b)) (E b)

variable (E m) in
@[expose] def blockEmbed (b : ι) : SpecialLinearGroup (Fin (m b)) (E b) →* PiGL E m :=
  (MonoidHom.mulSingle (fun c => GL (Fin (m c)) (E c)) b).comp SpecialLinearGroup.toGL

theorem blockEmbed_injective (b : ι) : Function.Injective (blockEmbed E m b) :=
  (Pi.mulSingle_injective (M := fun c => GL (Fin (m c)) (E c)) b).comp
    SpecialLinearGroup.toGL_injective

@[simp] theorem blockEmbed_apply_self (b : ι) (s : SpecialLinearGroup (Fin (m b)) (E b)) :
    blockEmbed E m b s b = SpecialLinearGroup.toGL s := by
  simp [blockEmbed]

theorem blockEmbed_apply_of_ne {b c : ι} (hcb : c ≠ b)
    (s : SpecialLinearGroup (Fin (m b)) (E b)) : blockEmbed E m b s c = 1 := by
  simp [blockEmbed, hcb]

variable (E m) in
@[expose] def blockSL (b : ι) : Subgroup (PiGL E m) := (blockEmbed E m b).range

theorem mem_blockSL {b : ι} {w : PiGL E m} :
    w ∈ blockSL E m b ↔ ∃ s : SpecialLinearGroup (Fin (m b)) (E b), blockEmbed E m b s = w :=
  Iff.rfl

theorem conj_mem_blockSL (b : ι) (w : PiGL E m) {g : PiGL E m} (hg : g ∈ blockSL E m b) :
    w * g * w⁻¹ ∈ blockSL E m b := by
  obtain ⟨s, rfl⟩ := hg
  have hdet : GeneralLinearGroup.det (w b * SpecialLinearGroup.toGL s * (w b)⁻¹) = 1 := by
    rw [map_mul, map_mul, map_inv, SpecialLinearGroup.coeToGL_det, mul_one, mul_inv_cancel]
  obtain ⟨s', hs'⟩ : w b * SpecialLinearGroup.toGL s * (w b)⁻¹ ∈
      (SpecialLinearGroup.toGL : SpecialLinearGroup (Fin (m b)) (E b) →* _).range := by
    rw [SpecialLinearGroup.range_toGL_eq_ker_det]
    exact hdet
  refine ⟨s', ?_⟩
  funext c
  by_cases hc : c = b
  · subst hc
    rw [blockEmbed_apply_self, hs']
    simp [blockEmbed]
  · rw [blockEmbed_apply_of_ne hc]
    simp [blockEmbed, hc]

theorem isQuasisimple_blockSL (b : ι) (hm : 2 ≤ m b)
    (hE : 3 ≤ m b ∨ ∃ s : Finset (E b), s.card = 4) : CFSG.IsQuasisimple (blockSL E m b) :=
  CFSG.LocalCores.isQuasisimple_of_mulEquiv
    (MonoidHom.ofInjective (blockEmbed_injective b)) (KCUnitary.isQuasisimple_SL hm hE)

theorem isPerfect_blockSL (b : ι) (hm : 2 ≤ m b)
    (hE : 3 ≤ m b ∨ ∃ s : Finset (E b), s.card = 4) : Group.IsPerfect (blockSL E m b) :=
  (isQuasisimple_blockSL b hm hE).1

theorem commute_of_le_one {F : Type*} [Field F] {k : ℕ} (hk : k ≤ 1) (u v : GL (Fin k) F) :
    u * v = v * u := by
  refine Units.ext ?_
  rw [Units.val_mul, Units.val_mul]
  ext i j
  have hi : i = j := by
    apply Fin.ext
    have := i.2
    have := j.2
    omega
  subst hi
  simp only [Matrix.mul_apply]
  rw [Finset.sum_eq_single i, Finset.sum_eq_single i]
  · exact mul_comm _ _
  · intro l _ hl
    exact absurd (Fin.ext (by have := l.2; have := i.2; omega)) hl
  · intro h
    exact absurd (Finset.mem_univ i) h
  · intro l _ hl
    exact absurd (Fin.ext (by have := l.2; have := i.2; omega)) hl
  · intro h
    exact absurd (Finset.mem_univ i) h

theorem commutator_top_eq_iSup [Finite ι]
    (hE : ∀ b, 2 ≤ m b → 3 ≤ m b ∨ ∃ s : Finset (E b), s.card = 4) :
    ⁅(⊤ : Subgroup (PiGL E m)), ⊤⁆ = ⨆ b : {b : ι // 2 ≤ m b}, blockSL E m b.1 := by
  apply le_antisymm
  · rw [Subgroup.commutator_le]
    intro u _ v _
    refine Subgroup.pi_mem_of_mulSingle_mem _ fun b => ?_
    by_cases hb : 2 ≤ m b
    · refine Subgroup.mem_iSup_of_mem ⟨b, hb⟩ ?_
      have hdet : GeneralLinearGroup.det ⁅u b, v b⁆ = 1 := by
        rw [map_commutatorElement, commutatorElement_eq_one_iff_commute]
        exact (Commute.all _ _)
      obtain ⟨s, hs⟩ : ⁅u b, v b⁆ ∈
          (SpecialLinearGroup.toGL : SpecialLinearGroup (Fin (m b)) (E b) →* _).range := by
        rw [SpecialLinearGroup.range_toGL_eq_ker_det]
        exact hdet
      refine ⟨s, ?_⟩
      have : (⁅u, v⁆ : PiGL E m) b = ⁅u b, v b⁆ := by
        simp [commutatorElement_def]
      simp only [blockEmbed, MonoidHom.coe_comp, MonoidHom.mulSingle_apply, Function.comp_apply]
      rw [this, hs]
    · have hcomm : ⁅u b, v b⁆ = 1 := by
        rw [commutatorElement_eq_one_iff_mul_comm]
        exact commute_of_le_one (by omega) _ _
      have : (⁅u, v⁆ : PiGL E m) b = 1 := by
        rw [show (⁅u, v⁆ : PiGL E m) b = ⁅u b, v b⁆ by simp [commutatorElement_def], hcomm]
      rw [this, Pi.mulSingle_one]
      exact Subgroup.one_mem _
  · refine iSup_le fun b => ?_
    have hperf := isPerfect_blockSL (E := E) (m := m) b.1 b.2 (hE b.1 b.2)
    calc blockSL E m b.1 = ⁅blockSL E m b.1, blockSL E m b.1⁆ :=
          (KCUnitary.commutator_eq_of_isPerfect hperf).symm
      _ ≤ ⁅(⊤ : Subgroup (PiGL E m)), ⊤⁆ := Subgroup.commutator_mono le_top le_top

variable (E m) in
@[expose] def scalarGLPi : Subgroup (PiGL E m) :=
  Subgroup.pi Set.univ fun b => (GeneralLinearGroup.scalar (Fin (m b))).range

omit [DecidableEq ι] in
theorem mem_scalarGLPi {w : PiGL E m} :
    w ∈ scalarGLPi E m ↔ ∀ b, ∃ c : (E b)ˣ, GeneralLinearGroup.scalar (Fin (m b)) c = w b := by
  simp [scalarGLPi, Subgroup.mem_pi]

omit [DecidableEq ι] in
theorem commute_of_mem_scalarGLPi {z : PiGL E m} (hz : z ∈ scalarGLPi E m) (w : PiGL E m) :
    z * w = w * z := by
  funext b
  obtain ⟨c, hc⟩ := (mem_scalarGLPi.mp hz) b
  have hmem : z b ∈ Subgroup.center (GL (Fin (m b)) (E b)) := by
    rw [GeneralLinearGroup.center_eq_range_scalar]
    exact ⟨c, hc⟩
  exact (Subgroup.mem_center_iff.mp hmem (w b)).symm

theorem mem_scalarGLPi_of_commute_blockEmbed {w : PiGL E m}
    (hw : ∀ b, 2 ≤ m b → ∀ s : SpecialLinearGroup (Fin (m b)) (E b),
      blockEmbed E m b s * w = w * blockEmbed E m b s) : w ∈ scalarGLPi E m := by
  rw [mem_scalarGLPi]
  intro b
  by_cases hb : 2 ≤ m b
  · have hcomm : ∀ s : SpecialLinearGroup (Fin (m b)) (E b),
        Commute (s : Matrix (Fin (m b)) (Fin (m b)) (E b))
          ((w b : GL (Fin (m b)) (E b)) : Matrix (Fin (m b)) (Fin (m b)) (E b)) := by
      intro s
      have h1 := congrFun (hw b hb s) b
      simp only [Pi.mul_apply, blockEmbed_apply_self] at h1
      have h2 := congrArg (fun g : GL (Fin (m b)) (E b) =>
        (g : Matrix (Fin (m b)) (Fin (m b)) (E b))) h1
      have h3 : (s : Matrix (Fin (m b)) (Fin (m b)) (E b)) *
          ((w b : GL (Fin (m b)) (E b)) : Matrix (Fin (m b)) (Fin (m b)) (E b)) =
          ((w b : GL (Fin (m b)) (E b)) : Matrix (Fin (m b)) (Fin (m b)) (E b)) * s := by
        simpa using h2
      exact h3
    have hsc : ((w b : GL (Fin (m b)) (E b)) : Matrix (Fin (m b)) (Fin (m b)) (E b)) ∈
        Set.range (Matrix.scalar (Fin (m b))) := by
      refine Matrix.mem_range_scalar_of_commute_transvectionStruct fun t => ?_
      exact hcomm ⟨t.toMatrix, t.det⟩
    have hmem : w b ∈ Subgroup.center (GL (Fin (m b)) (E b)) :=
      GeneralLinearGroup.mem_center_iff_val_mem_range_scalar.mpr hsc
    rw [GeneralLinearGroup.center_eq_range_scalar] at hmem
    exact hmem
  · have hmem : w b ∈ Subgroup.center (GL (Fin (m b)) (E b)) :=
      Subgroup.mem_center_iff.mpr fun g => commute_of_le_one (by omega) g (w b)
    rw [GeneralLinearGroup.center_eq_range_scalar] at hmem
    exact hmem

end PiGL

end CFSG.RankThree.PartOne.KCLinComm

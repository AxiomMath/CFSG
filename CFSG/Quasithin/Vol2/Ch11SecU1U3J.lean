module

public import CFSG.RankThree.PartOne.KF.F1322OmegaSeven
public import CFSG.LinearAlgebra.LinearGroups.Perfect
public import CFSG.LocalAnalysis.ComponentInitial.FourGroupOddBilinear

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecU1.U3

open Matrix CFSG.RankThree.SubgroupLists CFSG.RankThree.PartOne.LIT CFSG.RankThree.PartOne.KFBloom
open CFSG.LocalAnalysis.ComponentInitial.FourGroupOddBilinear (isometrySL mem_isometrySL)
open scoped MatrixGroups

section Commutator

variable {X Y : Type*} [Group X] [Group Y]

@[expose] noncomputable def commutatorTopEquiv (H : Subgroup X) :
    ↥(commutator ↥H) ≃* ↥(⁅H, H⁆) :=
  (Subgroup.equivMapOfInjective _ H.subtype H.subtype_injective).trans
    (MulEquiv.subgroupCongr (by
      rw [commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map,
        Subgroup.range_subtype]))

theorem map_commutator_top (E : X ≃* Y) :
    (commutator X).map E.toMonoidHom = commutator Y := by
  rw [commutator_def, commutator_def, Subgroup.map_commutator,
    Subgroup.map_top_of_surjective _ E.surjective]

@[expose] noncomputable def commutatorTopEquivOfEquiv (E : X ≃* Y) :
    ↥(commutator X) ≃* ↥(commutator Y) :=
  (Subgroup.equivMapOfInjective _ E.toMonoidHom E.injective).trans
    (MulEquiv.subgroupCongr (map_commutator_top E))

theorem mem_commutator_top_iff {H : Subgroup X} (x : ↥H) :
    x ∈ commutator ↥H ↔ (x : X) ∈ ⁅H, H⁆ := by
  rw [← Subgroup.mem_map_iff_mem H.subtype_injective, commutator_def, Subgroup.map_commutator,
    ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  rfl

end Commutator

variable {p : ℕ} [Fact p.Prime] {F : Type} [Field F] (e : ZMod p ≃+* F)
  (R : Matrix (Fin 3) (Fin 3) F)

theorem map_mem_soGL (g : isometrySL R) :
    GeneralLinearGroup.map e.symm.toRingHom (SpecialLinearGroup.toGL (g : SL(3, F))) ∈
      soGL (R.map e.symm.toRingHom) := by
  have hg : ((g : SL(3, F)) : Matrix (Fin 3) (Fin 3) F)ᵀ * R * (g : SL(3, F)) = R :=
    mem_isometrySL.mp g.2
  rw [mem_soGL]
  change (((g : SL(3, F)) : Matrix (Fin 3) (Fin 3) F).map e.symm.toRingHom)ᵀ *
      R.map e.symm.toRingHom * ((g : SL(3, F)) : Matrix (Fin 3) (Fin 3) F).map e.symm.toRingHom =
        R.map e.symm.toRingHom ∧
      (((g : SL(3, F)) : Matrix (Fin 3) (Fin 3) F).map e.symm.toRingHom).det = 1
  refine ⟨?_, ?_⟩
  · rw [← Matrix.transpose_map, ← Matrix.map_mul, ← Matrix.map_mul, hg]
  · rw [← RingHom.mapMatrix_apply, ← RingHom.map_det, (g : SL(3, F)).2, map_one]

@[expose] noncomputable def isometryToSO : isometrySL R →* soGL (R.map e.symm.toRingHom) :=
  ((GeneralLinearGroup.map e.symm.toRingHom).comp
    (SpecialLinearGroup.toGL.comp (isometrySL R).subtype)).codRestrict _ (map_mem_soGL e R)

theorem coe_isometryToSO (g : isometrySL R) :
    (((isometryToSO e R g : soGL (R.map e.symm.toRingHom)) : GL (Fin 3) (ZMod p)) :
      Matrix (Fin 3) (Fin 3) (ZMod p)) =
        ((g : SL(3, F)) : Matrix (Fin 3) (Fin 3) F).map e.symm.toRingHom := rfl

theorem isometryToSO_bijective : Function.Bijective (isometryToSO e R) := by
  refine ⟨fun a b hab => ?_, fun w => ?_⟩
  · have h1 := congrArg (fun g : soGL (R.map e.symm.toRingHom) =>
      ((g : GL (Fin 3) (ZMod p)) : Matrix (Fin 3) (Fin 3) (ZMod p))) hab
    simp only [coe_isometryToSO] at h1
    apply Subtype.ext
    apply Subtype.ext
    exact Matrix.map_injective e.symm.injective h1
  · set W := ((w : GL (Fin 3) (ZMod p)) : Matrix (Fin 3) (Fin 3) (ZMod p)) with hW
    have hw := mem_soGL.mp w.2
    have hWW : (W.map e.toRingHom).map e.symm.toRingHom = W := by
      ext i j
      simp
    have hRR : (R.map e.symm.toRingHom).map e.toRingHom = R := by
      ext i j
      simp
    have hdet : (W.map e.toRingHom).det = 1 := by
      rw [← RingHom.mapMatrix_apply, ← RingHom.map_det, hw.2, map_one]
    have hiso : (W.map e.toRingHom)ᵀ * R * W.map e.toRingHom = R := by
      rw [← hRR, ← Matrix.transpose_map, ← Matrix.map_mul, ← Matrix.map_mul, hw.1]
    refine ⟨⟨⟨W.map e.toRingHom, hdet⟩, mem_isometrySL.mpr hiso⟩, ?_⟩
    apply Subtype.ext
    apply Units.ext
    rw [coe_isometryToSO]
    exact hWW

@[expose] noncomputable def isometryEquivSO : isometrySL R ≃* soGL (R.map e.symm.toRingHom) :=
  MulEquiv.ofBijective (isometryToSO e R) (isometryToSO_bijective e R)

variable {R}

theorem transpose_map_symm (hRt : Rᵀ = R) :
    (R.map e.symm.toRingHom)ᵀ = R.map e.symm.toRingHom := by
  rw [← Matrix.transpose_map, hRt]

theorem det_map_symm_ne_zero (hRdet : R.det ≠ 0) : (R.map e.symm.toRingHom).det ≠ 0 := by
  rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
  exact (map_ne_zero _).mpr hRdet

include e in
theorem nonempty_commutator_equiv_psl2 (hp5 : 5 ≤ p) (hRt : Rᵀ = R) (hRdet : R.det ≠ 0) :
    Nonempty (↥(commutator ↥(isometrySL R)) ≃*
      Matrix.ProjectiveSpecialLinearGroup (Fin 2) (ZMod p)) := by
  obtain ⟨e2⟩ := CFSG.RankThree.PartOne.KF1322.nonempty_omegaGL_equiv_psl2 hp5
    (transpose_map_symm e hRt) (det_map_symm_ne_zero e hRdet)
  exact ⟨((commutatorTopEquivOfEquiv (isometryEquivSO e R)).trans
    (commutatorTopEquiv _)).trans e2⟩

include e in
theorem isSimpleGroup_commutator_isometry (hp5 : 5 ≤ p) (hRt : Rᵀ = R) (hRdet : R.det ≠ 0) :
    IsSimpleGroup ↥(commutator ↥(isometrySL R)) := by
  obtain ⟨E⟩ := nonempty_commutator_equiv_psl2 e hp5 hRt hRdet
  have : IsSimpleGroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (ZMod p)) :=
    Matrix.ProjectiveSpecialLinearGroup.rank_two_simple (by rw [Nat.card_zmod]; omega)
  exact E.isSimpleGroup

include e in
theorem isPerfect_commutator_isometry (hp5 : 5 ≤ p) (hRt : Rᵀ = R) (hRdet : R.det ≠ 0) :
    Group.IsPerfect ↥(commutator ↥(isometrySL R)) := by
  obtain ⟨E⟩ := nonempty_commutator_equiv_psl2 e hp5 hRt hRdet
  have h4 : ∃ s : Finset (ZMod p), s.card = 4 := by
    obtain ⟨s, -, hs⟩ := Finset.exists_subset_card_eq (s := (Finset.univ : Finset (ZMod p)))
      (n := 4) (by rw [Finset.card_univ, ZMod.card]; omega)
    exact ⟨s, hs⟩
  have : Group.IsPerfect (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (ZMod p)) :=
    CFSG.LinearGroups.linear_projective_perfect (le_refl 2) (Or.inr h4)
  exact Group.IsPerfect.ofSurjective (f := E.symm.toMonoidHom) E.symm.surjective

theorem exists_omega_elements (hp5 : 5 ≤ p) (hRt : Rᵀ = R) (hRdet : R.det ≠ 0) :
    ∃ g₀ : GL (Fin 3) (ZMod p), ∀ u : SL(2, ZMod p), ∃ w : isometrySL R,
      w ∈ commutator ↥(isometrySL R) ∧
        ((w : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) =
          ((g₀ * adGL u * g₀⁻¹ : GL (Fin 3) (ZMod p)) : Matrix (Fin 3) (Fin 3) (ZMod p)).map
            e.toRingHom := by
  have hp2 : p ≠ 2 := by omega
  obtain ⟨g₀, c, hc, hg₀⟩ := exists_congr_splitForm hp2 (R.map e.symm.toRingHom)
    (transpose_map_symm e hRt) (det_map_symm_ne_zero e hRdet)
  refine ⟨g₀, fun u => ?_⟩
  have hω : g₀ * adGL u * g₀⁻¹ ∈ omegaGL (R.map e.symm.toRingHom) := by
    have h1 : adGL u ∈ omegaGL ((g₀ : Matrix (Fin 3) (Fin 3) (ZMod p))ᵀ *
        R.map e.symm.toRingHom * (g₀ : Matrix (Fin 3) (Fin 3) (ZMod p))) := by
      rw [hg₀, omegaGL_smul _ hc, omegaGL_splitForm_eq_range hp5]
      exact ⟨u, rfl⟩
    rw [omegaGL_congr] at h1
    exact h1
  set E := isometryEquivSO e R with hE
  set ω : soGL (R.map e.symm.toRingHom) := ⟨_, omegaGL_le_soGL _ hω⟩ with hωdef
  refine ⟨E.symm ω, ?_, ?_⟩
  · have hmem : ω ∈ commutator ↥(soGL (R.map e.symm.toRingHom)) :=
      (mem_commutator_top_iff ω).mpr hω
    rw [← map_commutator_top E.symm]
    exact ⟨ω, hmem, rfl⟩
  · have h1 := coe_isometryToSO e R (E.symm ω)
    have h2 : isometryToSO e R (E.symm ω) = ω := E.apply_symm_apply ω
    rw [h2] at h1
    show _ = ((ω : GL (Fin 3) (ZMod p)) : Matrix (Fin 3) (Fin 3) (ZMod p)).map e.toRingHom
    rw [h1]
    ext i j
    simp

end CFSG.Quasithin.Vol2.Ch11.SecU1.U3

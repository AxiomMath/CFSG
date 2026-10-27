module

public import CFSG.RankThree.PartTwo.Sec16.KSL3TwoTailProofKP1Two

public section

namespace CFSG.RankThree.PartTwo.Sec16

namespace ProofKS1624KP1

open CFSG CFSG.RankThree.PartTwo
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag CFSG.LieType.SteinbergBR.BlockPar
open Matrix Module

variable {F : Type} [Field F]

theorem transpose_inv_eq (g : SpecialLinearGroup (Fin 3) F) :
    SpecialLinearGroup.transpose g⁻¹ = (SpecialLinearGroup.transpose g)⁻¹ := by
  apply eq_inv_of_mul_eq_one_left
  apply Subtype.ext
  show ((g⁻¹).val)ᵀ * (g.val)ᵀ = 1
  rw [← Matrix.transpose_mul,
    show g.val * (g⁻¹).val = 1 from congrArg Subtype.val (mul_inv_cancel g),
    Matrix.transpose_one]

theorem transpose_transpose' (g : SpecialLinearGroup (Fin 3) F) :
    SpecialLinearGroup.transpose (SpecialLinearGroup.transpose g) = g :=
  Subtype.ext (Matrix.transpose_transpose g.val)

@[expose] def thetaSL (F : Type) [Field F] :
    SpecialLinearGroup (Fin 3) F ≃* SpecialLinearGroup (Fin 3) F where
  toFun g := SpecialLinearGroup.transpose g⁻¹
  invFun g := SpecialLinearGroup.transpose g⁻¹
  left_inv g := by
    show SpecialLinearGroup.transpose (SpecialLinearGroup.transpose g⁻¹)⁻¹ = g
    rw [transpose_inv_eq g, inv_inv, transpose_transpose']
  right_inv g := by
    show SpecialLinearGroup.transpose (SpecialLinearGroup.transpose g⁻¹)⁻¹ = g
    rw [transpose_inv_eq g, inv_inv, transpose_transpose']
  map_mul' g h := by
    apply Subtype.ext
    show (((g * h)⁻¹).val)ᵀ = ((g⁻¹).val)ᵀ * ((h⁻¹).val)ᵀ
    rw [_root_.mul_inv_rev, ← Matrix.transpose_mul]
    rfl

theorem thetaSL_val (g : SpecialLinearGroup (Fin 3) F) : (thetaSL F g).val = ((g⁻¹).val)ᵀ :=
  rfl

@[expose] noncomputable def thetaP (F : Type) [Field F] : projectiveSL 3 F ≃* projectiveSL 3 F :=
  QuotientGroup.congr (scalars 3 F) (scalars 3 F) (thetaSL F) (by
    rw [scalars_eq_center]
    exact Subgroup.map_center_eq (thetaSL F))

theorem thetaP_proj (g : SpecialLinearGroup (Fin 3) F) :
    thetaP F (proj 3 F g) = proj 3 F (thetaSL F g) :=
  rfl

theorem thetaSL_entries {x : SpecialLinearGroup (Fin 3) F}
    (hx : x ∈ stabilizer (flagSpace 3 F 1)) :
    (thetaSL F x).val 0 1 = 0 ∧ (thetaSL F x).val 0 2 = 0 := by
  have hx' := mem_stabilizer_flagSpace_iff.mp (inv_mem hx)
  rw [thetaSL_val]
  exact ⟨hx' 1 0 (by norm_num) (by norm_num), hx' 2 0 (by norm_num) (by norm_num)⟩

@[expose] def cycSL (F : Type) [Field F] : SpecialLinearGroup (Fin 3) F :=
  ⟨!![0, 1, 0; 0, 0, 1; 1, 0, 0], by simp [Matrix.det_fin_three]⟩

@[expose] def cycInvSL (F : Type) [Field F] : SpecialLinearGroup (Fin 3) F :=
  ⟨!![0, 0, 1; 1, 0, 0; 0, 1, 0], by simp [Matrix.det_fin_three]⟩

theorem cycSL_inv : (cycSL F)⁻¹ = cycInvSL F := by
  apply inv_eq_of_mul_eq_one_right
  apply Subtype.ext
  show !![(0 : F), 1, 0; 0, 0, 1; 1, 0, 0] * !![0, 0, 1; 1, 0, 0; 0, 1, 0] = 1
  ext i j
  simp only [Matrix.mul_apply, Fin.sum_univ_three]
  fin_cases i <;> fin_cases j <;> simp

theorem cyc_conj_mem_stabilizer {y : SpecialLinearGroup (Fin 3) F} (h1 : y.val 0 1 = 0)
    (h2 : y.val 0 2 = 0) : cycSL F * y * (cycSL F)⁻¹ ∈ stabilizer (flagSpace 3 F 2) := by
  rw [mem_stabilizer_flagSpace_iff, cycSL_inv]
  intro i j hi hj
  have hi2 : i = 2 := by
    ext
    have := i.2
    simp only [Fin.val_two]
    omega
  subst hi2
  show ((cycSL F).val * y.val * (cycInvSL F).val) 2 j = 0
  simp only [Matrix.mul_apply, Fin.sum_univ_three]
  fin_cases j
  · simp [cycSL, cycInvSL, h1]
  · simp [cycSL, cycInvSL, h2]
  · exact absurd hj (by decide)

theorem conj_mem_stabilizer_of_map {d : ℕ} {C : Submodule F (Fin 3 → F)}
    {g n : SpecialLinearGroup (Fin 3) F}
    (hg : (flagSpace 3 F d).map (mulVecLin (g : Matrix (Fin 3) (Fin 3) F)) = C)
    (hn : ∀ w ∈ C, n.val *ᵥ w ∈ C) : g⁻¹ * n * g ∈ stabilizer (flagSpace 3 F d) := by
  rw [mem_stabilizer_iff_map_le]
  rintro _ ⟨w, hw, rfl⟩
  have h1 : g.val *ᵥ w ∈ C := by
    rw [← hg]
    exact ⟨w, hw, rfl⟩
  have h2 := hn _ h1
  rw [← hg] at h2
  obtain ⟨w', hw', hw'eq⟩ := h2
  have hgi : (g⁻¹).val * g.val = 1 := congrArg Subtype.val (inv_mul_cancel g)
  have hw'eq' : g.val *ᵥ w' = n.val *ᵥ (g.val *ᵥ w) := hw'eq
  have : (g⁻¹ * n * g).val *ᵥ w = w' := by
    rw [show (g⁻¹ * n * g).val = (g⁻¹).val * n.val * g.val from rfl, ← mulVec_mulVec,
      ← mulVec_mulVec, ← hw'eq', mulVec_mulVec, hgi, one_mulVec]
  show (mulVecLin (g⁻¹ * n * g).val) w ∈ flagSpace 3 F d
  rw [mulVecLin_apply, this]
  exact hw'

theorem exists_mulEquiv_normalizer_le [Finite F] [CharP F 2] {V0 : Subgroup (projectiveSL 3 F)}
    (hV2 : IsPGroup 2 V0) (hV1 : V0 ≠ ⊥) :
    ∃ α : projectiveSL 3 F ≃* projectiveSL 3 F,
      (Subgroup.normalizer (V0 : Set (projectiveSL 3 F))).map α.toMonoidHom ≤
        (stabilizer (flagSpace 3 F 2)).map (proj 3 F) := by
  obtain ⟨S, hS2, hSR, hSN⟩ := exists_two_lift_subgroup hV2
  have hCinv : ∀ n : SpecialLinearGroup (Fin 3) F,
      proj 3 F n ∈ Subgroup.normalizer (V0 : Set (projectiveSL 3 F)) →
      ∀ w ∈ fixVec S, n.val *ᵥ w ∈ fixVec S := by
    intro n hn w hw
    refine mulVec_mem_fixVec (fun x hx => ?_) hw
    have := hSN n⁻¹ (by rw [map_inv]; exact inv_mem hn) x hx
    rwa [inv_inv] at this
  obtain ⟨v, hvC, hv0⟩ := exists_ne_zero_mem_fixVec (by norm_num) hS2
  have hCbot : fixVec S ≠ ⊥ := by
    intro h
    rw [h] at hvC
    exact hv0 ((Submodule.mem_bot F).mp hvC)
  have hCtop : fixVec S ≠ ⊤ := by
    intro h
    apply hV1
    rw [← hSR, eq_bot_iff]
    rintro _ ⟨s, hs, rfl⟩
    have : s = 1 := Subtype.ext (eq_one_of_forall_mulVec' fun w =>
      (show w ∈ fixVec S by rw [h]; exact Submodule.mem_top) s hs)
    rw [this, map_one]
    exact one_mem _
  have hr0 : finrank F (fixVec S) ≠ 0 := fun h => hCbot (Submodule.finrank_eq_zero.mp h)
  have hr3 : finrank F (fixVec S) < 3 := by
    have := Submodule.finrank_lt hCtop
    rwa [Module.finrank_fin_fun] at this
  obtain ⟨g, hg⟩ := exists_map_flagSpace_eq (fixVec S)
  have hconj : ∀ n : SpecialLinearGroup (Fin 3) F,
      proj 3 F n ∈ Subgroup.normalizer (V0 : Set (projectiveSL 3 F)) →
      g⁻¹ * n * g ∈ stabilizer (flagSpace 3 F (finrank F (fixVec S))) :=
    fun n hn => conj_mem_stabilizer_of_map hg (hCinv n hn)
  have hr : finrank F (fixVec S) = 1 ∨ finrank F (fixVec S) = 2 := by omega
  rcases hr with hr | hr
  · rw [hr] at hconj
    refine ⟨(MulAut.conj ((proj 3 F g)⁻¹)).trans
      ((thetaP F).trans (MulAut.conj (proj 3 F (cycSL F)))), ?_⟩
    rintro _ ⟨y, hy, rfl⟩
    obtain ⟨n, rfl⟩ := proj_surjective 3 F y
    have h1 := thetaSL_entries (hconj n hy)
    refine ⟨_, cyc_conj_mem_stabilizer h1.1 h1.2, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulEquiv.trans_apply, MulAut.conj_apply, map_mul,
      map_inv, thetaP_proj, MulAut.conj_inv_apply]
    group
  · rw [hr] at hconj
    refine ⟨MulAut.conj ((proj 3 F g)⁻¹), ?_⟩
    rintro _ ⟨y, hy, rfl⟩
    obtain ⟨n, rfl⟩ := proj_surjective 3 F y
    refine ⟨_, hconj n hy, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, map_mul, map_inv, MulAut.conj_inv_apply]

end ProofKS1624KP1

end CFSG.RankThree.PartTwo.Sec16

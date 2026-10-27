module

public import CFSG.LocalAnalysis.SeitzReduction.TwistedE6PilotQ2SwapRowOverlap
public import CFSG.LocalAnalysis.SeitzReduction.TwistedE6PilotFieldNormalizeXModel

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.TwistedE6Pilot

open Subgroup Matrix CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Chevalley.E6GraphLevi CFSG.LocalAnalysis.ComponentInitial
open CFSG.LieType.Universal.Unitary (antidiag)
open CFSG.ComponentClassification.CatalogueBHigherLinearAction (slConjugation)
open CFSG.SeitzReduction.UnitaryPilot (toPSL graphFieldAut graphFieldSL barRingEquiv)

section Graph4

variable (K : Type) [Field K]

theorem antidiag_four_mul_mul (A : Matrix (Fin 4) (Fin 4) K) :
    (antidiag 4 : Matrix (Fin 4) (Fin 4) K) * A * antidiag 4 = A.submatrix Fin.rev Fin.rev := by
  ext i k
  have hk : ∀ j : Fin 4, (k = Fin.rev j) ↔ (j = Fin.rev k) := fun j =>
    ⟨fun h => by rw [h, Fin.rev_rev], fun h => by rw [h, Fin.rev_rev]⟩
  simp [antidiag, Matrix.mul_apply, hk]

theorem antidiag_four_mul_self : (antidiag 4 : Matrix (Fin 4) (Fin 4) K) * antidiag 4 = 1 := by
  have h := antidiag_four_mul_mul K 1
  rw [Matrix.mul_one] at h
  rw [h]
  ext i k
  simp [Matrix.one_apply, Fin.rev_inj]

theorem det_antidiag_four_sq :
    (antidiag 4 : Matrix (Fin 4) (Fin 4) K).det * (antidiag 4 : Matrix (Fin 4) (Fin 4) K).det =
      1 := by
  rw [← Matrix.det_mul, antidiag_four_mul_self, Matrix.det_one]

@[expose] def graphSL4 : SpecialLinearGroup (Fin 4) K →* SpecialLinearGroup (Fin 4) K where
  toFun B := ⟨antidiag 4 * ((B⁻¹ : SpecialLinearGroup (Fin 4) K) : Matrix (Fin 4) (Fin 4) K)ᵀ *
    antidiag 4, by
      rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, (B⁻¹).2, mul_one,
        det_antidiag_four_sq]⟩
  map_one' := Subtype.ext (by
    change (antidiag 4 : Matrix (Fin 4) (Fin 4) K) * (((1 : SpecialLinearGroup (Fin 4) K)⁻¹ :
      SpecialLinearGroup (Fin 4) K) : Matrix (Fin 4) (Fin 4) K)ᵀ * antidiag 4 = 1
    rw [inv_one, Matrix.SpecialLinearGroup.coe_one, Matrix.transpose_one, Matrix.mul_one,
      antidiag_four_mul_self])
  map_mul' B C := Subtype.ext (by
    change (antidiag 4 : Matrix (Fin 4) (Fin 4) K) * (((B * C)⁻¹ : SpecialLinearGroup (Fin 4) K) :
      Matrix (Fin 4) (Fin 4) K)ᵀ * antidiag 4 =
      antidiag 4 * ((B⁻¹ : SpecialLinearGroup (Fin 4) K) : Matrix (Fin 4) (Fin 4) K)ᵀ *
        antidiag 4 * (antidiag 4 * ((C⁻¹ : SpecialLinearGroup (Fin 4) K) :
          Matrix (Fin 4) (Fin 4) K)ᵀ * antidiag 4)
    rw [_root_.mul_inv_rev, Matrix.SpecialLinearGroup.coe_mul, Matrix.transpose_mul]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (antidiag 4 : Matrix (Fin 4) (Fin 4) K) (antidiag 4),
      antidiag_four_mul_self, Matrix.one_mul])

theorem coe_graphSL4 (B : SpecialLinearGroup (Fin 4) K) :
    (graphSL4 K B : Matrix (Fin 4) (Fin 4) K) = antidiag 4 *
      ((B⁻¹ : SpecialLinearGroup (Fin 4) K) : Matrix (Fin 4) (Fin 4) K)ᵀ * antidiag 4 :=
  rfl

variable {K} (σ : K →+* K)

@[expose] def twist4 : SpecialLinearGroup (Fin 4) K →* SpecialLinearGroup (Fin 4) K :=
  (graphSL4 K).comp (Matrix.SpecialLinearGroup.map σ)

end Graph4

section Embed

variable {K : Type} [Field K]

theorem ovl_rev_check : ∀ p : Fin 3, (∀ x : Fin 6, x ∈ ovlSet p ↔ Fin.rev x ∈ ovlSet p) ∧
    ∀ x ∈ ovlSet p, ovlPos p (Fin.rev x) = Fin.rev (ovlPos p x) := by
  decide

theorem ovlEmbed_map (p : Fin 3) (σ : K →+* K) (A : SpecialLinearGroup (Fin 4) K) :
    ovlEmbed p (Matrix.SpecialLinearGroup.map σ A) =
      Matrix.SpecialLinearGroup.map σ (ovlEmbed p A) := by
  apply Subtype.ext
  ext x y
  have h1 := ovlEmbed_apply p (Matrix.SpecialLinearGroup.map σ A) x y
  have h2 := ovlEmbed_apply p A x y
  simp only [Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply,
    Matrix.map_apply] at h1 ⊢
  rw [h1, h2]
  split_ifs
  · rfl
  · rw [Matrix.one_apply]
    split_ifs <;> simp

theorem graphSL_ovlEmbed (p : Fin 3) (A : SpecialLinearGroup (Fin 4) K) :
    graphSL K (ovlEmbed p A) = ovlEmbed p (graphSL4 K A) := by
  obtain ⟨hS, hpos⟩ := ovl_rev_check p
  apply Subtype.ext
  rw [coe_graphSL, antiId_mul_mul_antiId, ← map_inv]
  ext x y
  rw [Matrix.submatrix_apply, Matrix.transpose_apply, ovlEmbed_apply, ovlEmbed_apply,
    coe_graphSL4, antidiag_four_mul_mul, Matrix.submatrix_apply, Matrix.transpose_apply]
  by_cases hxy : x ∈ ovlSet p ∧ y ∈ ovlSet p
  · have h' : Fin.rev y ∈ ovlSet p ∧ Fin.rev x ∈ ovlSet p :=
      ⟨(hS y).1 hxy.2, (hS x).1 hxy.1⟩
    rw [ite_eq_left h', ite_eq_left hxy, hpos y hxy.2, hpos x hxy.1]
  · have h' : ¬(Fin.rev y ∈ ovlSet p ∧ Fin.rev x ∈ ovlSet p) := fun h =>
      hxy ⟨(hS x).2 h.2, (hS y).2 h.1⟩
    rw [ite_eq_right h', ite_eq_right hxy, Matrix.one_apply, Matrix.one_apply]
    by_cases h : x = y
    · subst h
      simp
    · rw [ite_eq_right (fun h'' => h (Fin.rev_injective h''.symm)), ite_eq_right h]

theorem unitaryTwist_ovlEmbed (p : Fin 3) (σ : K →+* K) (A : SpecialLinearGroup (Fin 4) K) :
    unitaryTwist σ (ovlEmbed p A) = ovlEmbed p (twist4 σ A) := by
  change graphSL K (Matrix.SpecialLinearGroup.map σ (ovlEmbed p A)) =
    ovlEmbed p (graphSL4 K (Matrix.SpecialLinearGroup.map σ A))
  rw [← ovlEmbed_map, graphSL_ovlEmbed]

end Embed

section Witt

variable {K : Type} [Field K]

theorem witt_identities_gen {n : ℕ} {σ : K →+* K} {P : GL (Fin n) K}
    {J : Matrix (Fin n) (Fin n) K} (hJJ : J * J = 1)
    (hP : ((P : Matrix (Fin n) (Fin n) K).map σ)ᵀ * (P : Matrix (Fin n) (Fin n) K) = J) :
    J * ((P : Matrix (Fin n) (Fin n) K).map σ)ᵀ =
        ((P⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) ∧
      (((P⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).map σ)ᵀ * J =
        (P : Matrix (Fin n) (Fin n) K) := by
  have hPP : (P : Matrix (Fin n) (Fin n) K) * ((P⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      1 := by rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hPP' : ((P⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * (P : Matrix (Fin n) (Fin n) K) =
      1 := by rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  have h1 : ((P : Matrix (Fin n) (Fin n) K).map σ)ᵀ =
      J * ((P⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
    rw [← hP, Matrix.mul_assoc, hPP, Matrix.mul_one]
  refine ⟨by rw [h1, ← Matrix.mul_assoc, hJJ, Matrix.one_mul], ?_⟩
  have h2 : (((P⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).map σ)ᵀ *
      ((P : Matrix (Fin n) (Fin n) K).map σ)ᵀ = 1 := by
    rw [← Matrix.transpose_mul, ← Matrix.map_mul, hPP, Matrix.map_one _ (map_zero σ) (map_one σ),
      Matrix.transpose_one]
  rw [h1, ← Matrix.mul_assoc] at h2
  calc (((P⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).map σ)ᵀ * J =
        (((P⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).map σ)ᵀ * J *
          (((P⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * (P : Matrix (Fin n) (Fin n) K)) := by
        rw [hPP', Matrix.mul_one]
    _ = ((((P⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).map σ)ᵀ * J *
          ((P⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) * (P : Matrix (Fin n) (Fin n) K) := by
        simp only [Matrix.mul_assoc]
    _ = (P : Matrix (Fin n) (Fin n) K) := by rw [h2, Matrix.one_mul]

theorem twist4_slConjugation {f : ℕ} (h : UnitaryFieldData 2 f K) {σ : K →+* K}
    (hbar : ∀ c, h.bar c = σ c) {P : GL (Fin 4) K}
    (hP : ((P : Matrix (Fin 4) (Fin 4) K).map σ)ᵀ * (P : Matrix (Fin 4) (Fin 4) K) = antidiag 4)
    (B : SpecialLinearGroup (Fin 4) K) :
    twist4 σ (slConjugation 4 K P⁻¹ B) = slConjugation 4 K P⁻¹ (graphFieldSL h 4 B) := by
  obtain ⟨hJ1, hJ2⟩ := witt_identities_gen (antidiag_four_mul_self K) hP
  apply Subtype.ext
  change antidiag 4 * (((Matrix.SpecialLinearGroup.map σ (slConjugation 4 K P⁻¹ B))⁻¹ :
    SpecialLinearGroup (Fin 4) K) : Matrix (Fin 4) (Fin 4) K)ᵀ * antidiag 4 = _
  rw [← map_inv, ← map_inv, Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply,
    CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation_matrix,
    CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation_matrix, inv_inv,
    UnitaryPilot.graphFieldSL_apply, Matrix.SpecialLinearGroup.map_apply_coe,
    RingHom.mapMatrix_apply, Matrix.map_mul, Matrix.map_mul, Matrix.transpose_mul,
    Matrix.transpose_mul]
  have hb : (barRingEquiv h).toRingHom = σ := by
    ext c
    exact hbar c
  rw [Matrix.SpecialLinearGroup.coe_transpose, hb, Matrix.transpose_map]
  calc (antidiag 4 : Matrix (Fin 4) (Fin 4) K) * (((P : Matrix (Fin 4) (Fin 4) K).map σ)ᵀ *
        ((((B⁻¹ : SpecialLinearGroup (Fin 4) K) : Matrix (Fin 4) (Fin 4) K).map σ)ᵀ *
          (((P⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K).map σ)ᵀ)) * antidiag 4 =
        ((antidiag 4 : Matrix (Fin 4) (Fin 4) K) * ((P : Matrix (Fin 4) (Fin 4) K).map σ)ᵀ) *
          (((B⁻¹ : SpecialLinearGroup (Fin 4) K) : Matrix (Fin 4) (Fin 4) K).map σ)ᵀ *
          ((((P⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K).map σ)ᵀ * antidiag 4) := by
        simp only [Matrix.mul_assoc]
    _ = _ := by rw [hJ1, hJ2]

end Witt

section Levi

variable {K : Type} [Field K]

@[expose] noncomputable def ovlLevi (h2 : (2 : K) = 0) (p : Fin 3) :
    Subgroup (ModGL TwistTag.E6.tag K) :=
  (LinearPilot.blockSpecialLinear (ovlSet p)).map (realize h2)

theorem ovlLevi_eq_range (h2 : (2 : K) = 0) (p : Fin 3) :
    ovlLevi h2 p = ((realize h2).comp (ovlEmbed p)).range := by
  rw [MonoidHom.range_comp, range_ovlEmbed, ovlLevi]

@[expose] noncomputable def ovlLeviEquiv (h2 : (2 : K) = 0) (p : Fin 3) :
    SpecialLinearGroup (Fin 4) K ≃* ovlLevi h2 p :=
  (MonoidHom.ofInjective (realize_ovlEmbed_injective h2 p)).trans
    (MulEquiv.subgroupCongr (ovlLevi_eq_range h2 p).symm)

theorem coe_ovlLeviEquiv (h2 : (2 : K) = 0) (p : Fin 3) (A : SpecialLinearGroup (Fin 4) K) :
    ((ovlLeviEquiv h2 p A : ovlLevi h2 p) : ModGL TwistTag.E6.tag K) =
      realize h2 (ovlEmbed p A) :=
  rfl

theorem ovlGroup_le_ovlLevi (h2 : (2 : K) = 0) (σ : K →+* K) (p : Fin 3) :
    ovlGroup h2 σ p ≤ ovlLevi h2 p :=
  Subgroup.map_mono inf_le_right

theorem center_ovlLevi [CharP K 2] (h2 : (2 : K) = 0) (p : Fin 3) : center (ovlLevi h2 p) = ⊥ := by
  have h := LinearCover.scalars_four_eq_bot K
  rw [LinearFlag.scalars_eq_center] at h
  rw [eq_bot_iff]
  intro z hz
  rw [mem_bot]
  have hz' : (ovlLeviEquiv h2 p).symm z ∈ center (SpecialLinearGroup (Fin 4) K) := by
    rw [mem_center_iff]
    intro g
    apply (ovlLeviEquiv h2 p).injective
    rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
    exact mem_center_iff.1 hz _
  rw [h, mem_bot] at hz'
  rw [← (ovlLeviEquiv h2 p).apply_symm_apply z, hz', map_one]

theorem ovlLevi_perfect (h2 : (2 : K) = 0) (p : Fin 3) :
    ⁅ovlLevi h2 p, ovlLevi h2 p⁆ = ovlLevi h2 p := by
  have hP := CFSG.ClassicalModels.specialLinear_isPerfect_of_three_le (K := K) (n := 4)
    (by norm_num)
  rw [ovlLevi_eq_range, MonoidHom.range_eq_map, ← Subgroup.map_commutator, ← commutator_def,
    hP.commutator_eq_top]

theorem ovlLevi_le_subsystemGroup (h2 : (2 : K) = 0) (p : Fin 3) :
    ovlLevi h2 p ≤ subsystemGroup TwistTag.E6.tag K E6GraphLevi.setA := by
  rw [← E6GraphLevi.range_realize h2]
  rintro _ ⟨B, -, rfl⟩
  exact ⟨B, rfl⟩

theorem twist4_twist4 {σ : K →+* K} (hσσ : ∀ c, σ (σ c) = c) (A : SpecialLinearGroup (Fin 4) K) :
    twist4 σ (twist4 σ A) = A := by
  apply ovlEmbed_injective (K := K) 0
  rw [← unitaryTwist_ovlEmbed, ← unitaryTwist_ovlEmbed, unitaryTwist_unitaryTwist hσσ]

@[expose] def twist4Equiv {σ : K →+* K} (hσσ : ∀ c, σ (σ c) = c) :
    MulAut (SpecialLinearGroup (Fin 4) K) :=
  MonoidHom.toMulEquiv (twist4 σ) (twist4 σ) (MonoidHom.ext fun A => twist4_twist4 hσσ A)
    (MonoidHom.ext fun A => twist4_twist4 hσσ A)

@[expose] noncomputable def ovlLeviTwist (h2 : (2 : K) = 0) {σ : K →+* K}
    (hσσ : ∀ c, σ (σ c) = c) (p : Fin 3) : MulAut (ovlLevi h2 p) :=
  ((ovlLeviEquiv h2 p).symm.trans (twist4Equiv hσσ)).trans (ovlLeviEquiv h2 p)

theorem twistHom_realize_ovlEmbed (h2 : (2 : K) = 0) (σ : K →+* K) (p : Fin 3)
    (A : SpecialLinearGroup (Fin 4) K) :
    twistHom TwistTag.E6 K σ (realize h2 (ovlEmbed p A)) =
      realize h2 (ovlEmbed p (twist4 σ A)) := by
  rw [E6GraphLevi.twistHom_realize σ h2, unitaryTwist_ovlEmbed]

theorem ovlLeviTwist_coe (h2 : (2 : K) = 0) {σ : K →+* K} (hσσ : ∀ c, σ (σ c) = c) (p : Fin 3)
    (y : ovlLevi h2 p) :
    ((ovlLeviTwist h2 hσσ p y : ovlLevi h2 p) : ModGL TwistTag.E6.tag K) =
      twistHom TwistTag.E6 K σ (y : ModGL TwistTag.E6.tag K) := by
  obtain ⟨A, rfl⟩ := (ovlLeviEquiv h2 p).surjective y
  change ((ovlLeviEquiv h2 p (twist4Equiv hσσ ((ovlLeviEquiv h2 p).symm (ovlLeviEquiv h2 p A))) :
    ovlLevi h2 p) : ModGL TwistTag.E6.tag K) = _
  rw [MulEquiv.symm_apply_apply, coe_ovlLeviEquiv, coe_ovlLeviEquiv, twistHom_realize_ovlEmbed]
  rfl

end Levi

section Model

variable {K : Type} [Field K]

@[expose] noncomputable def ovlModelEquiv [CharP K 2] (h2 : (2 : K) = 0) (p : Fin 3)
    (P : GL (Fin 4) K) : LinearFlag.projectiveSL 4 K ≃* ovlLevi h2 p :=
  (LinearFlag.conjAut 4 K P⁻¹).trans
    ((LinearCover.projectiveSLFourEquivSL K).trans (ovlLeviEquiv h2 p))

theorem ovlModelEquiv_proj [CharP K 2] (h2 : (2 : K) = 0) (p : Fin 3) (P : GL (Fin 4) K)
    (B : SpecialLinearGroup (Fin 4) K) :
    ovlModelEquiv h2 p P (LinearFlag.proj 4 K B) = ovlLeviEquiv h2 p (slConjugation 4 K P⁻¹ B) := by
  rw [ovlModelEquiv, MulEquiv.trans_apply, LinearFlag.conjAut_proj, MulEquiv.trans_apply]
  rfl

theorem ovlModelEquiv_toPSL_mem [CharP K 2] {f : ℕ} (h : UnitaryFieldData 2 f K) (h2 : (2 : K) = 0)
    {σ : K →+* K} (hbar : ∀ c, h.bar c = σ c) (p : Fin 3) {P : GL (Fin 4) K}
    (hP : ((P : Matrix (Fin 4) (Fin 4) K).map σ)ᵀ * (P : Matrix (Fin 4) (Fin 4) K) = antidiag 4)
    (x : CFSG.ClassicalGroups.UnitaryFlag.unitaryPSU h 4) :
    ((ovlModelEquiv h2 p P (toPSL h 4 x) : ovlLevi h2 p) : ModGL TwistTag.E6.tag K) ∈
      ovlGroup h2 σ p := by
  obtain ⟨A, rfl⟩ := CFSG.ClassicalGroups.UnitaryFlag.unitaryProj_surjective h 4 x
  rw [UnitaryPilot.toPSL_unitaryProj, ovlModelEquiv_proj, coe_ovlLeviEquiv]
  obtain ⟨-, hJ2⟩ := witt_identities_gen (antidiag_four_mul_self K) hP
  have hu := UnitaryPilot.unitary_toSL h A
  have hmap : ∀ M : Matrix (Fin 4) (Fin 4) K, M.map h.bar = M.map σ := fun M => by
    ext i j
    exact hbar _
  rw [hmap] at hu
  set C := slConjugation 4 K P⁻¹ (UnitaryPilot.toSL h 4 A) with hC
  have hCm : (C : Matrix (Fin 4) (Fin 4) K) =
      ((P⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) *
        ((UnitaryPilot.toSL h 4 A : SpecialLinearGroup (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) *
          (P : Matrix (Fin 4) (Fin 4) K) := by
    rw [hC, LinearFlag.coe_slConjugation, inv_inv]
  refine ⟨ovlEmbed p C, ⟨(ovlEmbed_mem_unitarySL_iff p C).2 ?_, ?_⟩, rfl⟩
  · rw [hCm, Matrix.map_mul, Matrix.map_mul, Matrix.transpose_mul, Matrix.transpose_mul]
    set A' := ((UnitaryPilot.toSL h 4 A : SpecialLinearGroup (Fin 4) K) : Matrix (Fin 4) (Fin 4) K)
    calc ((P : Matrix (Fin 4) (Fin 4) K).map σ)ᵀ * ((A'.map σ)ᵀ *
          (((P⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K).map σ)ᵀ) * antidiag 4 *
          (((P⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) * A' *
            (P : Matrix (Fin 4) (Fin 4) K)) =
        ((P : Matrix (Fin 4) (Fin 4) K).map σ)ᵀ * (A'.map σ)ᵀ *
          ((((P⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K).map σ)ᵀ * antidiag 4) *
          ((P⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) * A' *
            (P : Matrix (Fin 4) (Fin 4) K) := by simp only [Matrix.mul_assoc]
      _ = ((P : Matrix (Fin 4) (Fin 4) K).map σ)ᵀ * ((A'.map σ)ᵀ *
          ((P : Matrix (Fin 4) (Fin 4) K) * ((P⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K)) *
            A') * (P : Matrix (Fin 4) (Fin 4) K) := by rw [hJ2]; simp only [Matrix.mul_assoc]
      _ = antidiag 4 := by
        rw [← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.mul_one, hu, Matrix.mul_one, hP]
  · rw [← range_ovlEmbed p]
    exact ⟨C, rfl⟩

theorem fixRigid_toPSL_four {f : ℕ} (h : UnitaryFieldData 2 f K) :
    FixRigid (toPSL h 4) (graphFieldAut h 4) := by
  intro α hα
  obtain ⟨n, hn⟩ := mem_zpowers_iff.1
    (UnitaryPilot.mem_zpowers_graphFieldAut_of_forall_toPSL h (by norm_num) hα)
  have hθ2 : graphFieldAut h 4 ^ (2 : ℤ) = 1 := by
    rw [zpow_two]
    exact UnitaryPilot.graphFieldAut_mul_self h
  rw [zpow_eq_zpow_emod n hθ2] at hn
  rcases Int.emod_two_eq_zero_or_one n with h0 | h1
  · left
    rw [← hn, h0, zpow_zero]
  · right
    rw [← hn, h1, zpow_one]

end Model

section Rigid

variable
  {K : Type} [Field K]

theorem ovlLevi_rigid [Finite K] (hK : Nat.card K = (2 ^ 1) ^ 2) (h2 : (2 : K) = 0)
    {σ : K →+* K} (hσ : ∀ c, σ c = c ^ 2 ^ 1) (hσσ : ∀ c, σ (σ c) = c) (p : Fin 3)
    (α : MulAut (ovlLevi h2 p))
    (hα : ∀ u : ovlGroup h2 σ p, α ⟨u, ovlGroup_le_ovlLevi h2 σ p u.2⟩ =
      ⟨u, ovlGroup_le_ovlLevi h2 σ p u.2⟩) :
    α = 1 ∨ α = ovlLeviTwist h2 hσσ p := by
  have : CharP K 2 := charP_two_of_card le_rfl hK
  set h := unitaryFieldData_twistedE6Field (K := K) le_rfl hK with hh
  have hbar : ∀ c, h.bar c = σ c := fun c => by rw [UnitaryFieldData.bar_apply, hσ]
  obtain ⟨P, hP⟩ := CFSG.LieType.Universal.Unitary.exists_wittMatrix (p := 2) (f := 1) hK 4
  have hP' : ((P : Matrix (Fin 4) (Fin 4) K).map σ)ᵀ * (P : Matrix (Fin 4) (Fin 4) K) =
      antidiag 4 := by
    have e : (P : Matrix (Fin 4) (Fin 4) K).map σ = (P : Matrix (Fin 4) (Fin 4) K).map
        (CFSG.LieType.BorelTits.unitaryInvolution K 2 1) := by
      ext i j
      exact sigma_eq_unitaryInvolution_ovl hσ _
    rw [e]
    exact hP
  set Ξ := ovlModelEquiv h2 p P with hΞ
  have hc : MulAut.congr Ξ (graphFieldAut h 4) = ovlLeviTwist h2 hσσ p := by
    refine MulEquiv.ext fun y => ?_
    obtain ⟨A, rfl⟩ := (ovlLeviEquiv h2 p).surjective y
    have hA : ovlLeviEquiv h2 p A = Ξ (LinearFlag.proj 4 K (slConjugation 4 K P A)) := by
      rw [hΞ, ovlModelEquiv_proj, ← MulAut.mul_apply, ← map_mul, inv_mul_cancel, map_one,
        MulAut.one_apply]
    change Ξ (graphFieldAut h 4 (Ξ.symm (ovlLeviEquiv h2 p A))) =
      ovlLeviTwist h2 hσσ p (ovlLeviEquiv h2 p A)
    rw [hA, MulEquiv.symm_apply_apply, UnitaryPilot.graphFieldAut_proj, hΞ, ovlModelEquiv_proj,
      ovlModelEquiv_proj]
    apply Subtype.ext
    rw [ovlLeviTwist_coe, coe_ovlLeviEquiv, coe_ovlLeviEquiv, twistHom_realize_ovlEmbed,
      twist4_slConjugation h hbar hP']
  set α' := MulAut.congr Ξ.symm α with hα'def
  have hα' : ∀ x, α' (toPSL h 4 x) = toPSL h 4 x := by
    intro x
    change Ξ.symm (α (Ξ.symm.symm (toPSL h 4 x))) = toPSL h 4 x
    rw [MulEquiv.symm_symm]
    have hmem := ovlModelEquiv_toPSL_mem h h2 hbar p hP' x
    have h1 := hα ⟨_, hmem⟩
    have e : (⟨((Ξ (toPSL h 4 x) : ovlLevi h2 p) : ModGL TwistTag.E6.tag K),
        ovlGroup_le_ovlLevi h2 σ p hmem⟩ : ovlLevi h2 p) = Ξ (toPSL h 4 x) := rfl
    rw [e] at h1
    rw [h1, MulEquiv.symm_apply_apply]
  have hback : MulAut.congr Ξ α' = α := MulEquiv.ext fun y => by
    change Ξ (Ξ.symm (α (Ξ.symm.symm (Ξ.symm y)))) = α y
    rw [MulEquiv.symm_symm, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply]
  rcases fixRigid_toPSL_four h α' hα' with h1 | h1
  · left
    rw [← hback, h1, map_one]
  · right
    rw [← hback, h1, hc]

end Rigid

end CFSG.SeitzReduction.TwistedE6Pilot

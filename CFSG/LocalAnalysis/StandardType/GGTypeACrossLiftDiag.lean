module

public import CFSG.LocalAnalysis.StandardType.GGTypeACompatDiagCompat
public import CFSG.LocalAnalysis.StandardType.GGTypeAEndNode

public section

namespace CFSG.StandardType

open CFSG.ComponentClassification Matrix

private theorem ggDiagConj_eq_conjSL_diagGL {m : ℕ} {F : Type} [Field F]
    (h : Fin (m + 1) → Fˣ) (s : SpecialLinearGroup (Fin (m + 1)) F) :
    ggDiagConj h s = InnerDiagA.conjSL (InnerDiagA.diagGL h) s := by
  apply Subtype.ext
  rw [coe_ggDiagConj, InnerDiagA.coe_conjSL, InnerDiagA.coe_diagGL, InnerDiagA.coe_diagGL_inv]

private theorem conjSL_eq_slConjugation {m : ℕ} {F : Type} [Field F]
    (A : GL (Fin (m + 1)) F) (s : SpecialLinearGroup (Fin (m + 1)) F) :
    InnerDiagA.conjSL A s =
      CatalogueBHigherLinearAction.slConjugation (m + 1) F A s := by
  apply Subtype.ext
  rw [InnerDiagA.coe_conjSL, CatalogueBHigherLinearAction.slConjugation_matrix]

private theorem slConjugation_conj_field {m : ℕ} {F : Type} [Field F]
    (A : GL (Fin (m + 1)) F) (σ : F ≃+* F) (Y : GL (Fin (m + 1)) F) :
    CatalogueBHigherLinearAction.slConjugation (m + 1) F A *
        (CatalogueBHigherLinearField.slFieldAut (Fin (m + 1)) F σ *
          CatalogueBHigherLinearAction.slConjugation (m + 1) F Y *
          (CatalogueBHigherLinearField.slFieldAut (Fin (m + 1)) F σ)⁻¹) *
        (CatalogueBHigherLinearAction.slConjugation (m + 1) F A)⁻¹ =
      CatalogueBHigherLinearAction.slConjugation (m + 1) F
        (A * CatalogueBHigherLinearField.glFieldEquiv (Fin (m + 1)) σ Y * A⁻¹) := by
  rw [CFSG.LocalAnalysis.ComponentInitial.LinearFlag.slField_mul_slConjugation_mul_inv,
    ← map_inv, ← map_mul, ← map_mul]

private theorem slConjugation_conj_graph {m : ℕ} {F : Type} [Field F]
    (A : GL (Fin (m + 1)) F) (σ : F ≃+* F) (Y : GL (Fin (m + 1)) F) :
    CatalogueBHigherLinearAction.slConjugation (m + 1) F A *
        (CatalogueBHigherLinearField.slFieldAut (Fin (m + 1)) F σ *
          (CatalogueBGraphForm.slGraphAut (m + 1) F *
            CatalogueBHigherLinearAction.slConjugation (m + 1) F Y *
            CatalogueBGraphForm.slGraphAut (m + 1) F) *
          (CatalogueBHigherLinearField.slFieldAut (Fin (m + 1)) F σ)⁻¹) *
        (CatalogueBHigherLinearAction.slConjugation (m + 1) F A)⁻¹ =
      CatalogueBHigherLinearAction.slConjugation (m + 1) F
        (A * CatalogueBHigherLinearField.glFieldEquiv (Fin (m + 1)) σ
          (Matrix.GeneralLinearGroup.inverseTranspose Y) * A⁻¹) := by
  rw [CFSG.LocalAnalysis.ComponentInitial.LinearFlag.slGraph_mul_slConjugation_mul_slGraph,
    CFSG.LocalAnalysis.ComponentInitial.LinearFlag.slField_mul_slConjugation_mul_inv,
    ← map_inv, ← map_mul, ← map_mul]

theorem exists_conjSL_of_mulAut_sl {m : ℕ} {F : Type} [Field F] [Finite F]
    (hm : 3 ≤ m + 1) (β : MulAut (SpecialLinearGroup (Fin (m + 1)) F))
    (D : GL (Fin (m + 1)) F) :
    ∃ X : GL (Fin (m + 1)) F, ∀ s,
      β (InnerDiagA.conjSL X s) = InnerDiagA.conjSL D (β s) := by
  obtain ⟨A, σ, ε, hε, hβ⟩ :=
    CFSG.RankThree.PartOne.AUTSL.exists_eq_std_of_mulAut_sl hm β
  have hγγ : CatalogueBGraphForm.slGraphAut (m + 1) F *
      CatalogueBGraphForm.slGraphAut (m + 1) F = 1 := by
    rw [← pow_two]
    exact CatalogueBGraphForm.slGraphAut_sq (m + 1) F
  have hγinv : (CatalogueBGraphForm.slGraphAut (m + 1) F)⁻¹ =
      CatalogueBGraphForm.slGraphAut (m + 1) F :=
    (eq_inv_of_mul_eq_one_left hγγ).symm
  interval_cases ε
  · refine ⟨CatalogueBHigherLinearField.glFieldEquiv (Fin (m + 1)) σ.symm (A⁻¹ * D * A),
      fun s => ?_⟩
    have hX : CatalogueBHigherLinearField.glFieldEquiv (Fin (m + 1)) σ
        (CatalogueBHigherLinearField.glFieldEquiv (Fin (m + 1)) σ.symm (A⁻¹ * D * A)) =
        A⁻¹ * D * A := by
      ext i j
      rw [CatalogueBHigherLinearField.glFieldEquiv_entry,
        CatalogueBHigherLinearField.glFieldEquiv_entry]
      exact σ.apply_symm_apply _
    have hconj : β * CatalogueBHigherLinearAction.slConjugation (m + 1) F
          (CatalogueBHigherLinearField.glFieldEquiv (Fin (m + 1)) σ.symm (A⁻¹ * D * A)) *
          β⁻¹ = CatalogueBHigherLinearAction.slConjugation (m + 1) F D := by
      calc β * CatalogueBHigherLinearAction.slConjugation (m + 1) F
              (CatalogueBHigherLinearField.glFieldEquiv (Fin (m + 1)) σ.symm (A⁻¹ * D * A)) *
            β⁻¹
          = CatalogueBHigherLinearAction.slConjugation (m + 1) F A *
              (CatalogueBHigherLinearField.slFieldAut (Fin (m + 1)) F σ *
                CatalogueBHigherLinearAction.slConjugation (m + 1) F
                  (CatalogueBHigherLinearField.glFieldEquiv (Fin (m + 1)) σ.symm
                    (A⁻¹ * D * A)) *
                (CatalogueBHigherLinearField.slFieldAut (Fin (m + 1)) F σ)⁻¹) *
              (CatalogueBHigherLinearAction.slConjugation (m + 1) F A)⁻¹ := by
            rw [hβ, pow_zero, mul_one]
            group
        _ = CatalogueBHigherLinearAction.slConjugation (m + 1) F
              (A * CatalogueBHigherLinearField.glFieldEquiv (Fin (m + 1)) σ
                (CatalogueBHigherLinearField.glFieldEquiv (Fin (m + 1)) σ.symm
                  (A⁻¹ * D * A)) * A⁻¹) :=
            slConjugation_conj_field A σ _
        _ = CatalogueBHigherLinearAction.slConjugation (m + 1) F D := by
            rw [hX]
            congr 1
            group
    have hpt : β (InnerDiagA.conjSL
        (CatalogueBHigherLinearField.glFieldEquiv (Fin (m + 1)) σ.symm (A⁻¹ * D * A)) s) =
        InnerDiagA.conjSL D (β s) := by
      have h1 := congrArg (fun φ : MulAut (SpecialLinearGroup (Fin (m + 1)) F) => φ (β s)) hconj
      rw [conjSL_eq_slConjugation, conjSL_eq_slConjugation]
      simpa only [MulAut.mul_apply, MulAut.inv_apply, MulEquiv.symm_apply_apply] using h1
    exact hpt
  · refine ⟨Matrix.GeneralLinearGroup.inverseTranspose
        (CatalogueBHigherLinearField.glFieldEquiv (Fin (m + 1)) σ.symm (A⁻¹ * D * A)),
      fun s => ?_⟩
    have hX : CatalogueBHigherLinearField.glFieldEquiv (Fin (m + 1)) σ
        (Matrix.GeneralLinearGroup.inverseTranspose
          (Matrix.GeneralLinearGroup.inverseTranspose
            (CatalogueBHigherLinearField.glFieldEquiv (Fin (m + 1)) σ.symm
              (A⁻¹ * D * A)))) =
        A⁻¹ * D * A := by
      rw [Matrix.GeneralLinearGroup.inverseTranspose_inverseTranspose]
      ext i j
      rw [CatalogueBHigherLinearField.glFieldEquiv_entry,
        CatalogueBHigherLinearField.glFieldEquiv_entry]
      exact σ.apply_symm_apply _
    have hconj : β * CatalogueBHigherLinearAction.slConjugation (m + 1) F
          (Matrix.GeneralLinearGroup.inverseTranspose
            (CatalogueBHigherLinearField.glFieldEquiv (Fin (m + 1)) σ.symm (A⁻¹ * D * A))) *
          β⁻¹ = CatalogueBHigherLinearAction.slConjugation (m + 1) F D := by
      calc β * CatalogueBHigherLinearAction.slConjugation (m + 1) F
              (Matrix.GeneralLinearGroup.inverseTranspose
                (CatalogueBHigherLinearField.glFieldEquiv (Fin (m + 1)) σ.symm
                  (A⁻¹ * D * A))) * β⁻¹
          = CatalogueBHigherLinearAction.slConjugation (m + 1) F A *
              (CatalogueBHigherLinearField.slFieldAut (Fin (m + 1)) F σ *
                (CatalogueBGraphForm.slGraphAut (m + 1) F *
                  CatalogueBHigherLinearAction.slConjugation (m + 1) F
                    (Matrix.GeneralLinearGroup.inverseTranspose
                      (CatalogueBHigherLinearField.glFieldEquiv (Fin (m + 1)) σ.symm
                        (A⁻¹ * D * A))) *
                  CatalogueBGraphForm.slGraphAut (m + 1) F) *
                (CatalogueBHigherLinearField.slFieldAut (Fin (m + 1)) F σ)⁻¹) *
              (CatalogueBHigherLinearAction.slConjugation (m + 1) F A)⁻¹ := by
            rw [hβ, pow_one, _root_.mul_inv_rev, _root_.mul_inv_rev, hγinv]
            group
        _ = CatalogueBHigherLinearAction.slConjugation (m + 1) F
              (A * CatalogueBHigherLinearField.glFieldEquiv (Fin (m + 1)) σ
                (Matrix.GeneralLinearGroup.inverseTranspose
                  (Matrix.GeneralLinearGroup.inverseTranspose
                    (CatalogueBHigherLinearField.glFieldEquiv (Fin (m + 1)) σ.symm
                      (A⁻¹ * D * A)))) * A⁻¹) :=
            slConjugation_conj_graph A σ _
        _ = CatalogueBHigherLinearAction.slConjugation (m + 1) F D := by
            rw [hX]
            congr 1
            group
    have hpt : β (InnerDiagA.conjSL
        (Matrix.GeneralLinearGroup.inverseTranspose
          (CatalogueBHigherLinearField.glFieldEquiv (Fin (m + 1)) σ.symm (A⁻¹ * D * A))) s) =
        InnerDiagA.conjSL D (β s) := by
      have h1 := congrArg (fun φ : MulAut (SpecialLinearGroup (Fin (m + 1)) F) => φ (β s)) hconj
      rw [conjSL_eq_slConjugation, conjSL_eq_slConjugation]
      simpa only [MulAut.mul_apply, MulAut.inv_apply, MulEquiv.symm_apply_apply] using h1
    exact hpt

private theorem exists_slCompat_lift_comp {X : Type} [Group X] {n : ℕ} {F : Type} [Field F]
    [Finite F] (hn : 3 ≤ n) {φ₁ φ₂ : SpecialLinearGroup (Fin (n + 1)) F →* X}
    (hker₁ : φ₁.ker ≤ Subgroup.center (SpecialLinearGroup (Fin (n + 1)) F))
    (hker₂ : φ₂.ker ≤ Subgroup.center (SpecialLinearGroup (Fin (n + 1)) F))
    (hJ : (φ₁.comp (slLowerBlockHom n F)).range = (φ₂.comp (slUpperBlockHom n F)).range) :
    ∃ β' : MulAut (SpecialLinearGroup (Fin (n + 1)) F),
      (φ₂.comp β'.toMonoidHom).range = φ₂.range ∧
      (φ₂.comp β'.toMonoidHom).ker ≤ Subgroup.center (SpecialLinearGroup (Fin (n + 1)) F) ∧
      φ₁.comp (slLowerBlockHom n F) = (φ₂.comp β'.toMonoidHom).comp (slUpperBlockHom n F) := by
  have hθ₁ := injective_comp_slLowerBlockHom hker₁
  have hθ₂ := injective_comp_slUpperBlockHom hker₂
  let β : MulAut (SpecialLinearGroup (Fin n) F) :=
    ((MonoidHom.ofInjective hθ₁).trans (MulEquiv.subgroupCongr hJ)).trans
      (MonoidHom.ofInjective hθ₂).symm
  have hβ : ∀ g, φ₂ (slUpperBlockHom n F (β g)) = φ₁ (slLowerBlockHom n F g) := by
    intro g
    have e := MulEquiv.apply_symm_apply (MonoidHom.ofInjective hθ₂)
      ((MulEquiv.subgroupCongr hJ) (MonoidHom.ofInjective hθ₁ g))
    have e' := congrArg Subtype.val e
    rw [MonoidHom.ofInjective_apply] at e'
    exact e'.trans (by rw [MulEquiv.subgroupCongr_apply, MonoidHom.ofInjective_apply]; rfl)
  obtain ⟨β', hβ'⟩ := exists_mulAut_slUpperBlockHom hn β
  refine ⟨β', ?_, ?_, ?_⟩
  · rw [MonoidHom.range_comp, MonoidHom.range_eq_top.mpr β'.surjective, ← MonoidHom.range_eq_map]
  · intro g hg
    have hc : β' g ∈ Subgroup.center (SpecialLinearGroup (Fin (n + 1)) F) := hker₂ hg
    rw [Subgroup.mem_center_iff] at hc ⊢
    intro h
    apply β'.injective
    rw [map_mul, map_mul]
    exact hc (β' h)
  · ext g
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, hβ', hβ]

theorem exists_slCompat_lift_actsDiag {X : Type} [Group X] {n : ℕ} {F : Type} [Field F]
    [Finite F] (hn : 3 ≤ n) {φ₁ φ₂ : SpecialLinearGroup (Fin (n + 1)) F →* X}
    (hker₁ : φ₁.ker ≤ Subgroup.center (SpecialLinearGroup (Fin (n + 1)) F))
    (hker₂ : φ₂.ker ≤ Subgroup.center (SpecialLinearGroup (Fin (n + 1)) F))
    (hJ : (φ₁.comp (slLowerBlockHom n F)).range = (φ₂.comp (slUpperBlockHom n F)).range)
    {S : Set X} (h₁ : ∀ b ∈ S, GGActsDiag φ₁ b) (h₂ : ∀ b ∈ S, GGActsDiag φ₂ b) :
    ∃ φ₂' : SpecialLinearGroup (Fin (n + 1)) F →* X, φ₂'.range = φ₂.range ∧
      φ₂'.ker ≤ Subgroup.center (SpecialLinearGroup (Fin (n + 1)) F) ∧
      φ₁.comp (slLowerBlockHom n F) = φ₂'.comp (slUpperBlockHom n F) ∧
      ∀ b ∈ S, GGActsDiag φ₂' b := by
  obtain ⟨β', hrange, hker, hcomp⟩ := exists_slCompat_lift_comp hn hker₁ hker₂ hJ
  refine ⟨φ₂.comp β'.toMonoidHom, hrange, hker, hcomp, fun b hb => ?_⟩
  obtain ⟨h, hh⟩ := h₂ b hb
  obtain ⟨X, hX⟩ := exists_conjSL_of_mulAut_sl (m := n) (F := F) (by omega) β'
    (InnerDiagA.diagGL h)
  have hpair : (b, X) ∈ LinFusion.ggInducedPairs (φ₂.comp β'.toMonoidHom) := by
    rw [LinFusion.mem_ggInducedPairs]
    intro u
    calc b * (φ₂.comp β'.toMonoidHom) u * b⁻¹
        = b * φ₂ (β' u) * b⁻¹ := rfl
      _ = φ₂ (ggDiagConj h (β' u)) := hh (β' u)
      _ = φ₂ (InnerDiagA.conjSL (InnerDiagA.diagGL h) (β' u)) := by
            rw [ggDiagConj_eq_conjSL_diagGL]
      _ = φ₂ (β' (InnerDiagA.conjSL X u)) := by rw [hX u]
      _ = (φ₂.comp β'.toMonoidHom) (InnerDiagA.conjSL X u) := rfl
  exact ggActsDiag_of_compat hn hker hcomp (h₁ b hb) ⟨X, hpair⟩

end CFSG.StandardType

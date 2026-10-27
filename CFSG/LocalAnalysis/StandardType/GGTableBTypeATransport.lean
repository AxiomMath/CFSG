module

public import CFSG.LocalAnalysis.StandardType.GGTableBTypeAEndNode

public section

namespace CFSG.StandardType.TypeA

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.Assembly

section Recipe

variable {d : ℕ} {K : Type} [Field K]

theorem mem_largeEvenSLGroup_iff {A : GL (Fin d) K} :
    A ∈ LargeEvenSLGroup (Fin d) K ↔ (A : Matrix (Fin d) (Fin d) K).det = 1 := by
  rw [LargeEvenSLGroup, MonoidHom.mem_ker, Units.ext_iff, Matrix.GeneralLinearGroup.val_det_apply,
    Units.val_one]

variable (d K) in
@[expose] noncomputable def slKerEquiv :
    ↥(LargeEvenSLGroup (Fin d) K) ≃* SpecialLinearGroup (Fin d) K where
  toFun h := ⟨((h : GL (Fin d) K) : Matrix (Fin d) (Fin d) K), mem_largeEvenSLGroup_iff.mp h.2⟩
  invFun g := ⟨Matrix.SpecialLinearGroup.toGL g, mem_largeEvenSLGroup_iff.mpr g.2⟩
  left_inv h := by
    apply Subtype.ext
    apply Units.ext
    rfl
  right_inv g := by
    apply Subtype.ext
    rfl
  map_mul' h h' := by
    apply Subtype.ext
    rfl

theorem coe_slKerEquiv (h : LargeEvenSLGroup (Fin d) K) :
    ((slKerEquiv d K h : SpecialLinearGroup (Fin d) K) : Matrix (Fin d) (Fin d) K) =
      ((h : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) :=
  rfl

theorem map_scalars_slKerEquiv :
    ((LargeEvenScalars (Fin d) K).subgroupOf (LargeEvenSLGroup (Fin d) K)).map
      (slKerEquiv d K : ↥(LargeEvenSLGroup (Fin d) K) →* SpecialLinearGroup (Fin d) K) =
        scalars d K := by
  ext g
  constructor
  · rintro ⟨h, hh, rfl⟩
    have hh' : (h : GL (Fin d) K) ∈ LargeEvenScalars (Fin d) K := hh
    obtain ⟨u, hu⟩ := hh'
    refine ⟨u, ?_, ?_⟩
    · have h1 := mem_largeEvenSLGroup_iff.mp h.2
      rw [← hu, Matrix.GeneralLinearGroup.coe_scalar, scalar_apply, det_diagonal,
        Finset.prod_const, Finset.card_univ, Fintype.card_fin] at h1
      exact Units.ext (by rw [Units.val_pow_eq_pow_val, h1, Units.val_one])
    · change ((h : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) = scalar (Fin d) (u : K)
      rw [← hu]
      rfl
  · rintro ⟨c, -, hg⟩
    refine ⟨(slKerEquiv d K).symm g, ?_, by simp⟩
    change (((slKerEquiv d K).symm g : LargeEvenSLGroup (Fin d) K) : GL (Fin d) K) ∈
      LargeEvenScalars (Fin d) K
    refine ⟨c, Units.ext ?_⟩
    rw [Matrix.GeneralLinearGroup.coe_scalar]
    exact hg.symm

@[expose] noncomputable def recipeEquiv (d : ℕ) (K : Type) [Field K] :
    LargeEvenProj (LargeEvenSLGroup (Fin d) K) ≃* projectiveSL d K :=
  QuotientGroup.congr _ _ (slKerEquiv d K) map_scalars_slKerEquiv

theorem recipeEquiv_mk (h : LargeEvenSLGroup (Fin d) K) :
    recipeEquiv d K (LargeEvenProjMk (LargeEvenSLGroup (Fin d) K) h) =
      proj d K (slKerEquiv d K h) :=
  rfl

theorem congr_recipeEquiv_mem {φ : MulAut (LargeEvenProj (LargeEvenSLGroup (Fin d) K))}
    (hφ : φ ∈ LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSLGroup (Fin d) K)) Set.univ) :
    MulAut.congr (recipeEquiv d K) φ ∈ Set.range (conjAut d K) := by
  obtain ⟨A, -, hA⟩ := hφ
  refine ⟨A, ?_⟩
  ext x
  obtain ⟨g, rfl⟩ := proj_surjective d K x
  set h : LargeEvenSLGroup (Fin d) K := (slKerEquiv d K).symm g with hh
  have hg : proj d K g = recipeEquiv d K (LargeEvenProjMk (LargeEvenSLGroup (Fin d) K) h) := by
    rw [recipeEquiv_mk, hh, MulEquiv.apply_symm_apply]
  have hdet : A * (h : GL (Fin d) K) * A⁻¹ ∈ LargeEvenSLGroup (Fin d) K := by
    rw [mem_largeEvenSLGroup_iff, Units.val_mul, Units.val_mul, det_mul, det_mul,
      mem_largeEvenSLGroup_iff.mp h.2, mul_one, ← det_mul, ← Units.val_mul, mul_inv_cancel,
      Units.val_one, det_one]
  set h' : LargeEvenSLGroup (Fin d) K := ⟨A * (h : GL (Fin d) K) * A⁻¹, hdet⟩ with hh'
  have h1 := hA h h' rfl
  rw [MulAut.congr_apply, hg, MulEquiv.trans_apply, MulEquiv.symm_apply_apply,
    MulEquiv.trans_apply, h1, recipeEquiv_mk, conjAut_proj]
  apply congrArg (proj d K)
  ext i j
  rw [coe_slConjugation', coe_slKerEquiv]
  rfl

end Recipe

section Transport

variable {p r : ℕ} {R R' : Type} [Group R] [Group R']

theorem ker_comp_mulEquiv (e : R ≃* R') {L' : Type} [Group L'] (ψ : L' →* R) :
    (e.toMonoidHom.comp ψ).ker = ψ.ker := by
  ext l
  simp [MonoidHom.mem_ker]

theorem ggTorusLift_of_mulEquiv (e : R ≃* R') (h : GGTorusLift p r R') : GGTorusLift p r R := by
  intro L' _ _ ψ hψ hker hperf
  obtain ⟨U, E, hU, hU2, hEU, hE, hcard, hEker⟩ := h L' (e.toMonoidHom.comp ψ)
    (e.surjective.comp hψ) ((ker_comp_mulEquiv e ψ).symm ▸ hker) hperf
  exact ⟨U, E, hU, hU2, hEU, hE, hcard, ker_comp_mulEquiv e ψ ▸ hEker⟩

variable {I : Set (MulAut R)} {I' : Set (MulAut R')}

theorem ggEndNode_of_mulEquiv (e : R ≃* R') (hI : ∀ φ ∈ I, MulAut.congr e φ ∈ I')
    (h : GGEndNode p r R' I') :
    GGEndNode p r R I := by
  intro L' _ _ ψ hψ hker hperf A hA hAI hr h3
  refine h L' (e.toMonoidHom.comp ψ) (e.surjective.comp hψ)
    ((ker_comp_mulEquiv e ψ).symm ▸ hker) hperf A hA (fun a ha => ?_) hr h3
  obtain ⟨φ, hφ, hφa⟩ := hAI a ha
  refine ⟨MulAut.congr e φ, hI φ hφ, fun l => ?_⟩
  change e (φ (e.symm (e (ψ l)))) = e (ψ (a l))
  rw [MulEquiv.symm_apply_apply, hφa]

theorem ggBstarBound_of_mulEquiv (e : R ≃* R') (hI : ∀ φ ∈ I, MulAut.congr e φ ∈ I')
    (h : GGBstarBound p r R' I') : GGBstarBound p r R I := by
  intro Eb Eh hEbI hEb hr h3 hle hEh hcard
  set c := MulAut.congr e with hc
  have hcEb : Nat.card (Eb.map c.toMonoidHom) = Nat.card Eb :=
    Subgroup.card_map_of_injective c.injective
  have hcEh : Nat.card (Eh.map c.toMonoidHom) = Nat.card Eh :=
    Subgroup.card_map_of_injective c.injective
  obtain ⟨E', hlt, hE'h, U, hU, hU2, hEU⟩ := h (Eb.map c.toMonoidHom) (Eh.map c.toMonoidHom)
    (by
      rintro _ ⟨φ, hφ, rfl⟩
      exact hI φ (hEbI hφ))
    (TableB.isElemAbelian_map hEb _) (hcEb ▸ hr) (hcEb ▸ h3) (Subgroup.map_mono hle)
    (TableB.isElemAbelian_map hEh _) (by rw [hcEb, hcEh]; exact hcard)
  refine ⟨E'.comap c.toMonoidHom, ?_, ?_, U.comap e.toMonoidHom, ?_,
    hU2.comap_of_injective _ e.injective, ?_⟩
  · refine lt_of_le_of_ne (Subgroup.map_le_iff_le_comap.mp hlt.le) ?_
    intro heq
    apply hlt.ne
    rw [heq, Subgroup.map_comap_eq_self_of_surjective (f := c.toMonoidHom) c.surjective]
  · calc E'.comap c.toMonoidHom ≤ (Eh.map c.toMonoidHom).comap c.toMonoidHom :=
          Subgroup.comap_mono hE'h
      _ = Eh := Subgroup.comap_map_eq_self_of_injective (f := c.toMonoidHom) c.injective Eh
  · intro hbot
    apply hU
    rw [← Subgroup.map_comap_eq_self_of_surjective (f := e.toMonoidHom) e.surjective U, hbot,
      Subgroup.map_bot]
  · intro φ hφ u hu
    have h1 := hEU (c φ) hφ (e u) hu
    change e (φ u) ∈ U
    have h2 : c φ (e u) = e (φ u) := by
      rw [hc, MulAut.congr_apply]
      change e (φ (e.symm (e u))) = e (φ u)
      rw [MulEquiv.symm_apply_apply]
    rw [← h2]
    exact h1

end Transport

end CFSG.StandardType.TypeA

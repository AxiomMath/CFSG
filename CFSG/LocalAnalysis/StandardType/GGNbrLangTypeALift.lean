module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveTypeALift
public import CFSG.LocalAnalysis.StandardType.GGNbrGraphFieldLinear
public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherOuterQuotients
public import CFSG.LinearAlgebra.LinearGroups.Perfect

public section

namespace CFSG.StandardType

namespace NbrLangTypeA

open Matrix CFSG.Assembly CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag CFSG.LieType.Steinberg.CentralExt.SLClosed
open CFSG.ComponentClassification
open scoped commutatorElement

theorem eq_of_mul_mem_center {H X : Type*} [Group H] [Group X] (hH : commutator H = ⊤)
    {f₁ f₂ : H →* X} (h : ∀ g, (f₁ g)⁻¹ * f₂ g ∈ Subgroup.center X) : f₁ = f₂ := by
  have hle : commutator H ≤ MonoidHom.eqLocus f₁ f₂ := by
    rw [commutator_def, Subgroup.commutator_le]
    intro a _ b _
    change f₁ ⁅a, b⁆ = f₂ ⁅a, b⁆
    have ea : f₂ a = f₁ a * ((f₁ a)⁻¹ * f₂ a) := by group
    have eb : f₂ b = f₁ b * ((f₁ b)⁻¹ * f₂ b) := by group
    rw [map_commutatorElement, map_commutatorElement, ea, eb,
      commutatorElement_mul_mem_center (h a) (h b)]
  ext g
  exact hle (hH ▸ Subgroup.mem_top g)

variable {G : Type*} [Group G] {K : Subgroup G} {d : ℕ} {F : Type} [Field F]

theorem exists_lift [Finite F] (hd : 3 ≤ d) (h2 : Nat.card F ≠ 2)
    (h4 : ¬(d = 3 ∧ Nat.card F = 4)) (h3 : Nat.card F ≠ 3) (hK : commutator K = ⊤)
    (θ₁ : K ⧸ Subgroup.center K ≃* projectiveSL d F) :
    ∃ φ₀ : Matrix.SpecialLinearGroup (Fin d) F →* K, Function.Surjective φ₀ ∧
      φ₀.ker ≤ Subgroup.center (Matrix.SpecialLinearGroup (Fin d) F) ∧
      ∀ g, θ₁ (QuotientGroup.mk (φ₀ g)) = proj d F g := by
  obtain ⟨n, rfl⟩ : ∃ n, d = n + 1 := ⟨d - 1, by omega⟩
  let θ₂ := θ₁.trans (QuotientGroup.quotientMulEquivOfEq (scalars_eq_center (n + 1) F))
  have hsep : Separating n F :=
    separating_of_card (by omega) h2 (fun h => h4 ⟨by omega, h.2⟩) (fun h => h3 h.2)
  obtain ⟨φ₀, hsurj, hker, hlift⟩ :=
    exists_slLift_of_mulEquiv (n := n) (by omega) hsep hK θ₂
  refine ⟨φ₀, hsurj, hker, fun g => ?_⟩
  apply (QuotientGroup.quotientMulEquivOfEq (scalars_eq_center (n + 1) F)).injective
  exact hlift g

theorem conj_lift_eq (hSL : commutator (Matrix.SpecialLinearGroup (Fin d) F) = ⊤)
    (θ₁ : K ⧸ Subgroup.center K ≃* projectiveSL d F)
    (φ₀ : Matrix.SpecialLinearGroup (Fin d) F →* K)
    (hlift : ∀ g, θ₁ (QuotientGroup.mk (φ₀ g)) = proj d F g) {g : G}
    (hg : g ∈ Subgroup.normalizer (K : Set G))
    (ψ : MulAut (Matrix.SpecialLinearGroup (Fin d) F))
    (hψ : ggLAut K θ₁ ⟨g, hg⟩ = descendAut d F ψ) (h : Matrix.SpecialLinearGroup (Fin d) F) :
    g * (φ₀ h : G) * g⁻¹ = (φ₀ (ψ h) : G) := by
  set f₁ := (K.normalizerMonoidHom ⟨g, hg⟩).toMonoidHom.comp φ₀ with hf₁
  set f₂ := φ₀.comp ψ.toMonoidHom with hf₂
  have hcen : ∀ h, (f₁ h)⁻¹ * f₂ h ∈ Subgroup.center K := by
    intro h
    apply QuotientGroup.eq.mp
    apply θ₁.injective
    have e1 : θ₁ (QuotientGroup.mk (f₁ h)) = ggLAut K θ₁ ⟨g, hg⟩ (θ₁ (QuotientGroup.mk (φ₀ h))) :=
      (ggLAut_apply K θ₁ ⟨g, hg⟩ (φ₀ h)).symm
    rw [e1, hlift, hψ, descendAut_proj, ← hlift]
    rfl
  have heq := eq_of_mul_mem_center hSL hcen
  have h1 := congrArg (fun f => ((f h : K) : G)) heq
  exact h1

theorem ggLAut_trans {R R' : Type} [Group R] [Group R'] (θ : K ⧸ Subgroup.center K ≃* R)
    (e : R ≃* R') (g : Subgroup.normalizer (K : Set G)) :
    ggLAut K (θ.trans e) g = MulAut.congr e (ggLAut K θ g) := by
  ext r
  obtain ⟨q, rfl⟩ := (θ.trans e).surjective r
  induction q using QuotientGroup.induction_on with
  | H l =>
    rw [ggLAut_apply, MulAut.congr_apply]
    simp only [MulEquiv.trans_apply, MulEquiv.symm_apply_apply]
    rw [ggLAut_apply]

theorem congr_recipeEquiv_field_mem {φ : MulAut (LargeEvenProj (LargeEvenSLGroup (Fin d) F))}
    (hφ : φ ∈ LargeEvenMatFieldImage (LargeEvenProjMk (LargeEvenSLGroup (Fin d) F))) :
    MulAut.congr (TypeA.recipeEquiv d F) φ ∈ Set.range (fieldAut d F) := by
  obtain ⟨σ, hσ⟩ := hφ
  refine ⟨σ, ?_⟩
  ext x
  obtain ⟨g, rfl⟩ := proj_surjective d F x
  set h : LargeEvenSLGroup (Fin d) F := (TypeA.slKerEquiv d F).symm g with hh
  have hg : proj d F g =
      TypeA.recipeEquiv d F (LargeEvenProjMk (LargeEvenSLGroup (Fin d) F) h) := by
    rw [TypeA.recipeEquiv_mk, hh, MulEquiv.apply_symm_apply]
  set h' : LargeEvenSLGroup (Fin d) F :=
    (TypeA.slKerEquiv d F).symm (Matrix.SpecialLinearGroup.map σ.toRingHom g) with hh'
  have h1 := hσ h h' rfl
  rw [MulAut.congr_apply, hg]
  simp only [MulEquiv.trans_apply, MulEquiv.symm_apply_apply]
  rw [h1, ← hg, fieldAut_proj, hh', TypeA.recipeEquiv_mk, MulEquiv.apply_symm_apply]

theorem conj_frame_eq (hSL : commutator (Matrix.SpecialLinearGroup (Fin d) F) = ⊤)
    (θ₁ : K ⧸ Subgroup.center K ≃* projectiveSL d F)
    (φ₀ : Matrix.SpecialLinearGroup (Fin d) F →* K)
    (hlift : ∀ g, θ₁ (QuotientGroup.mk (φ₀ g)) = proj d F g) {g : G}
    (hg : g ∈ Subgroup.normalizer (K : Set G)) (M D₁ : GL (Fin d) F) (τ : F ≃+* F)
    (hψ : ggLAut K θ₁ ⟨g, hg⟩ =
      conjAut d F M * conjAut d F D₁ * fieldAut d F τ * (conjAut d F M)⁻¹)
    (h : Matrix.SpecialLinearGroup (Fin d) F) :
    g * (φ₀ (CatalogueBHigherLinearAction.slConjugation d F M h) : G) * g⁻¹ =
      (φ₀ (CatalogueBHigherLinearAction.slConjugation d F M
        (CatalogueBHigherLinearAction.slConjugation d F D₁
          (Matrix.SpecialLinearGroup.map τ.toRingHom h))) : G) := by
  set ψ : MulAut (Matrix.SpecialLinearGroup (Fin d) F) :=
    CatalogueBHigherLinearAction.slConjugation d F M *
      CatalogueBHigherLinearAction.slConjugation d F D₁ *
      CatalogueBHigherLinearField.slFieldAut (Fin d) F τ *
      (CatalogueBHigherLinearAction.slConjugation d F M)⁻¹ with hψdef
  have hdesc : ggLAut K θ₁ ⟨g, hg⟩ = descendAut d F ψ := by
    rw [hψ, hψdef, map_mul, map_mul, map_mul, map_inv]
    rfl
  rw [conj_lift_eq hSL θ₁ φ₀ hlift hg ψ hdesc]
  congr 2
  rw [hψdef, MulAut.mul_apply, MulAut.mul_apply, MulAut.mul_apply, MulAut.inv_apply,
    MulEquiv.symm_apply_apply]
  rfl

theorem ker_comp_slConjugation_le {X : Type*} [Group X]
    (φ : Matrix.SpecialLinearGroup (Fin d) F →* X)
    (hφ : φ.ker ≤ Subgroup.center (Matrix.SpecialLinearGroup (Fin d) F)) (M : GL (Fin d) F) :
    (φ.comp (CatalogueBHigherLinearAction.slConjugation d F M).toMonoidHom).ker ≤
      Subgroup.center (Matrix.SpecialLinearGroup (Fin d) F) := by
  intro h hh
  have h1 : CatalogueBHigherLinearAction.slConjugation d F M h ∈
      Subgroup.center (Matrix.SpecialLinearGroup (Fin d) F) := hφ hh
  rw [Subgroup.mem_center_iff] at h1 ⊢
  intro z
  apply (CatalogueBHigherLinearAction.slConjugation d F M).injective
  rw [map_mul, map_mul]
  exact h1 _

theorem ggLAut_mem_conjImage_of_mem
    (θ : K ⧸ Subgroup.center K ≃* LargeEvenProj (LargeEvenSLGroup (Fin d) F)) {k : G}
    (hk : k ∈ K) (hkN : k ∈ Subgroup.normalizer (K : Set G)) :
    ggLAut K θ ⟨k, hkN⟩ ∈
      LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSLGroup (Fin d) F)) Set.univ := by
  obtain ⟨h₀, hh₀⟩ := QuotientGroup.mk'_surjective _
    (θ (QuotientGroup.mk (⟨k, hk⟩ : K)))
  refine ⟨(h₀ : GL (Fin d) F), Set.mem_univ _, fun h h' hh' => ?_⟩
  have hconj : ggLAut K θ ⟨k, hkN⟩ = MulAut.conj (θ (QuotientGroup.mk (⟨k, hk⟩ : K))) := by
    ext r
    obtain ⟨q, rfl⟩ := θ.surjective r
    induction q using QuotientGroup.induction_on with
    | H l =>
      rw [ggLAut_apply, MulAut.conj_apply, ← map_mul, ← map_inv, ← map_mul]
      congr 1
  have hh'' : h' = h₀ * h * h₀⁻¹ := Subtype.ext hh'
  rw [hconj, ← hh₀, MulAut.conj_apply, hh'', map_mul, map_mul, map_inv]

end NbrLangTypeA

end CFSG.StandardType

end

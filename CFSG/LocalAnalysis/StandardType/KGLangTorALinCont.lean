module

public import CFSG.LocalAnalysis.StandardType.GGNbrLangTorARankKG
import CFSG.LocalAnalysis.StandardType.KGLangTorAGeneric
import CFSG.LocalAnalysis.StandardType.KGLangTorALinLift
import CFSG.LocalAnalysis.StandardType.KGLangTorALinCore
import CFSG.LocalAnalysis.StandardType.KGLangTorAFields
import CFSG.LocalAnalysis.StandardType.GGNbrFieldFixKnownLinearProj
import CFSG.LocalAnalysis.StandardType.GGRecipeFieldLinear
import CFSG.LocalAnalysis.StandardType.GGRecipeFieldCyclicLabels
import CFSG.LocalAnalysis.StandardType.GGRecipeFieldLinearLang
import CFSG.LinearAlgebra.LinearGroups.Perfect

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.LocalAnalysis.ComponentInitial

theorem kgLangTorA_lin_cont {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {lab : LargeEvenLabel}
    (htag : lab.tag = .A) (hd : 3 ≤ lab.rank + 1) (hn : 1 ≤ lab.n) (F : Type) [Field F]
    [Finite F] (hF : Nat.card F = 2 ^ lab.n) :
    KGLangAxisTorACont p lab (LargeEvenProj (LargeEvenSLGroup (Fin (lab.rank + 1)) F))
      (LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSLGroup (Fin (lab.rank + 1)) F))
        Set.univ)
      (LargeEvenMatFieldImage (LargeEvenProjMk (LargeEvenSLGroup (Fin (lab.rank + 1)) F))) := by
  classical
  let d : ℕ := lab.rank + 1
  let R : Type := LargeEvenProj (LargeEvenSLGroup (Fin d) F)
  let I : Set (MulAut R) :=
    LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSLGroup (Fin d) F)) Set.univ
  let Fd : Set (MulAut R) :=
    LargeEvenMatFieldImage (LargeEvenProjMk (LargeEvenSLGroup (Fin d) F))
  have hd : 3 ≤ d := by omega
  change KGLangAxisTorACont p lab R I Fd
  rw [KGLangAxisTorACont]
  intro K _ _ θ hK A hA hAIF α₀ hα₀ hα₀I hcard2 hcardSplit
  have hd2 : 2 ≤ d := by omega
  have hsimple : IsSimpleGroup R := LinearFieldFix.isSimpleGroup_proj hd F
  have hna : ∃ a b : R, a * b ≠ b * a := LinearFieldFix.exists_noncomm_proj hd F
  have hinn : GGRawInnField p R I Fd :=
    RecipeFieldLinear.ggRawInnField_linear (d := d) (K := F) hd2 (Or.inl hd) hp.ne_one
  have hPC : GGRawPCyclic p R I Fd :=
    RecipeFieldLinear.ggRawPCyclic_linear (d := d) (K := F) hd2 (hp.odd_of_ne_two hp2)
  have hFC : GGRawFieldConj p R I Fd :=
    RecipeFieldLang.ggRawFieldConj_linear (d := d) (K := F) hd2 (Or.inl hd) hp
  obtain ⟨B₀, X, u₀, f₀, hmem, hdec, hXcard, hu₀, hf₀, hf₀ord, hα₀eq, hXab, hXI, hXf, hXβ⟩ :=
    kgLangTorA_setup hp hsimple hna hinn hPC hFC θ hK hA hAIF hα₀ hα₀I
  have hXgt1 : 1 < Nat.card X := by
    rw [hXcard]
    exact lt_of_lt_of_le (by norm_num : 1 < 2 ^ 2)
      (le_trans (Nat.pow_le_pow_left hp.two_le 2) hcard2)
  have hp3 : 3 ≤ p := by
    have hodd := hp.odd_of_ne_two hp2
    have h2 := hp.two_le
    omega
  let E : MulAut R ≃* MulAut (LinearFlag.projectiveSL d F) :=
    MulAut.congr (TypeA.recipeEquiv d F)
  obtain ⟨σ, hσord, hσE, hX'ab, hX'c, hX'σ, hX'card⟩ :=
    kgLangTorA_lin_transport (d := d) (p := p) hp hd hXab hXI hf₀ hf₀ord hXf
  obtain ⟨hpn, -⟩ := kgLangTorA_card_fixed_linear (F := F) (n := lab.n) (p := p) hn hF hσord
  have hn3 : 3 ≤ lab.n := by
    obtain ⟨m, hm⟩ := hpn
    have hm1 : 1 ≤ m := Nat.pos_of_ne_zero (by rintro rfl; omega)
    calc 3 ≤ p := hp3
      _ = p * 1 := by simp
      _ ≤ p * m := Nat.mul_le_mul_left p hm1
      _ = lab.n := hm.symm
  have hF8 : 8 ≤ Nat.card F := by
    rw [hF]
    calc 8 = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ lab.n := Nat.pow_le_pow_right (by norm_num) hn3
  have hF2 : Nat.card F ≠ 2 := by omega
  have hF3 : Nat.card F ≠ 3 := by omega
  have hF4 : ¬(d = 3 ∧ Nat.card F = 4) := by
    rintro ⟨-, h⟩
    omega
  let θ' : K ⧸ Subgroup.center K ≃* LinearFlag.projectiveSL d F :=
    θ.trans (TypeA.recipeEquiv d F)
  obtain ⟨κ, hκ⟩ := kgLangTorA_lin_lift (d := d) (F := F) hd hF2 hF4 hF3 hK θ'
  have hEu : E u₀ = LinearFlag.conjAut d F (Classical.choose (TypeA.congr_recipeEquiv_mem hu₀)) :=
    (Classical.choose_spec (TypeA.congr_recipeEquiv_mem hu₀)).symm
  let g₀ : GL (Fin d) F := Classical.choose (TypeA.congr_recipeEquiv_mem hu₀)
  have hEu' : E u₀ = LinearFlag.conjAut d F g₀ := by
    simpa [g₀] using hEu
  let κ' : Matrix.SpecialLinearGroup (Fin d) F →* K :=
    κ.comp (CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation d F g₀).toMonoidHom
  have hκ' : ∀ h, θ' (QuotientGroup.mk (κ' h)) =
      LinearFlag.conjAut d F g₀ (LinearFlag.proj d F h) := by
    intro h
    change θ' (QuotientGroup.mk (κ (CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation d F g₀ h))) =
      LinearFlag.conjAut d F g₀ (LinearFlag.proj d F h)
    rw [hκ]
    exact LinearFlag.conjAut_proj g₀ h
  have hα₀eq' : E (kgInducedAut θ α₀) =
      LinearFlag.conjAut d F g₀ * LinearFlag.fieldAut d F σ *
        (LinearFlag.conjAut d F g₀)⁻¹ := by
    rw [hα₀eq, map_mul, map_mul, map_inv, hσE, hEu']
  have hX'gt1 : 1 < Nat.card (Subgroup.map E.toMonoidHom X) := by
    rw [hX'card]
    exact hXgt1
  have hsplitX' : p ∣ 2 ^ lab.n - 1 →
      p ^ (d / p + 2) ≤ Nat.card (Subgroup.map E.toMonoidHom X) := by
    intro hpdvd
    have hs : GGTypeASplitPrime p lab := Or.inl ⟨htag, hpdvd⟩
    have hc := hcardSplit hs
    calc p ^ (d / p + 2) = p ^ ((lab.rank + 1) / p + 2) := by simp [d]
      _ ≤ Nat.card {α : MulAut K // α ∈ A ∧ kgInducedAut θ α ∈ I} := hc
      _ = Nat.card X := hXcard.symm
      _ = Nat.card (Subgroup.map E.toMonoidHom X) := hX'card.symm
  obtain ⟨e, s, he_fixed, hep, he_notcenter, hs_fixed, hcomm⟩ :=
    kgLangTorA_lin_core (d := d) (n := lab.n) (p := p) hp hp2 hn hF hd hσord
      hX'ab hX'c hX'σ hX'gt1 hsplitX'
  have heKne : κ' e ≠ 1 := by
    intro h
    have h1 : θ' (QuotientGroup.mk (κ' e)) = 1 := by
      rw [h, QuotientGroup.mk_one, map_one]
    rw [hκ' e] at h1
    have hproj : LinearFlag.proj d F e = 1 := by
      apply (LinearFlag.conjAut d F g₀).injective
      simpa using h1
    exact he_notcenter (by
      rw [← LinearFlag.scalars_eq_center]
      exact (LinearFlag.proj_eq_one_iff).mp hproj)
  have hα₀ψ : ∀ h, kgInducedAut θ' α₀ (θ' (QuotientGroup.mk (κ' h))) =
      θ' (QuotientGroup.mk (κ' (Matrix.SpecialLinearGroup.map σ.toRingHom h))) := by
    intro h
    rw [kgLangTorA_inducedAut_trans θ (TypeA.recipeEquiv d F) α₀]
    rw [hκ' h, hα₀eq', hκ' (Matrix.SpecialLinearGroup.map σ.toRingHom h)]
    change ((LinearFlag.conjAut d F g₀ * LinearFlag.fieldAut d F σ *
        (LinearFlag.conjAut d F g₀)⁻¹) * LinearFlag.conjAut d F g₀)
        (LinearFlag.proj d F h) =
      LinearFlag.conjAut d F g₀
        (LinearFlag.proj d F (Matrix.SpecialLinearGroup.map σ.toRingHom h))
    rw [← LinearFlag.fieldAut_proj]
    change ((LinearFlag.conjAut d F g₀ * LinearFlag.fieldAut d F σ *
        (LinearFlag.conjAut d F g₀)⁻¹) * LinearFlag.conjAut d F g₀)
        (LinearFlag.proj d F h) =
      (LinearFlag.conjAut d F g₀ * LinearFlag.fieldAut d F σ) (LinearFlag.proj d F h)
    rw [show LinearFlag.conjAut d F g₀ * LinearFlag.fieldAut d F σ *
        (LinearFlag.conjAut d F g₀)⁻¹ * LinearFlag.conjAut d F g₀ =
        LinearFlag.conjAut d F g₀ * LinearFlag.fieldAut d F σ by group]
  have hβψ : ∀ β ∈ B₀, ∃ ψ : Matrix.SpecialLinearGroup (Fin d) F →*
      Matrix.SpecialLinearGroup (Fin d) F, ψ e = e ∧ ψ s = s ∧
      ∀ h, kgInducedAut θ' β (θ' (QuotientGroup.mk (κ' h))) =
        θ' (QuotientGroup.mk (κ' (ψ h))) := by
    intro β hβ
    have hxX : u₀⁻¹ * kgInducedAut θ β * u₀ ∈ X := hXβ β hβ
    have hxX' : E (u₀⁻¹ * kgInducedAut θ β * u₀) ∈ Subgroup.map E.toMonoidHom X :=
      Subgroup.mem_map.mpr ⟨_, hxX, rfl⟩
    have hxI : u₀⁻¹ * kgInducedAut θ β * u₀ ∈ I := hXI _ hxX
    obtain ⟨C, hC⟩ := TypeA.congr_recipeEquiv_mem hxI
    have hCX' : LinearFlag.conjAut d F C ∈ Subgroup.map E.toMonoidHom X := by
      rw [hC]
      exact hxX'
    have hcommC := hcomm C hCX'
    have hxE : E (u₀⁻¹ * kgInducedAut θ β * u₀) =
        (LinearFlag.conjAut d F g₀)⁻¹ * E (kgInducedAut θ β) *
          LinearFlag.conjAut d F g₀ := by
      rw [map_mul, map_mul, map_inv, hEu']
    have hEimage : E (kgInducedAut θ β) =
        LinearFlag.conjAut d F g₀ * LinearFlag.conjAut d F C *
          (LinearFlag.conjAut d F g₀)⁻¹ := by
      calc E (kgInducedAut θ β)
          = LinearFlag.conjAut d F g₀ *
              ((LinearFlag.conjAut d F g₀)⁻¹ * E (kgInducedAut θ β) *
                LinearFlag.conjAut d F g₀) *
              (LinearFlag.conjAut d F g₀)⁻¹ := by group
        _ = LinearFlag.conjAut d F g₀ * LinearFlag.conjAut d F C *
              (LinearFlag.conjAut d F g₀)⁻¹ := by rw [← hxE, hC]
    let ψ : Matrix.SpecialLinearGroup (Fin d) F →*
        Matrix.SpecialLinearGroup (Fin d) F :=
      (CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation d F C).toMonoidHom
    refine ⟨ψ, ?_, ?_, ?_⟩
    · apply Matrix.SpecialLinearGroup.toGL_injective
      change Matrix.SpecialLinearGroup.toGL
        (CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation d F C e) =
        Matrix.SpecialLinearGroup.toGL e
      rw [CFSG.ComponentClassification.CatalogueBHigherLinearAction.toGL_slConjugation, hcommC.1]
      group
    · apply Matrix.SpecialLinearGroup.toGL_injective
      change Matrix.SpecialLinearGroup.toGL
        (CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation d F C s) =
        Matrix.SpecialLinearGroup.toGL s
      rw [CFSG.ComponentClassification.CatalogueBHigherLinearAction.toGL_slConjugation, hcommC.2]
      group
    · intro h
      rw [kgLangTorA_inducedAut_trans θ (TypeA.recipeEquiv d F) β, hκ' h, hEimage]
      rw [hκ']
      change ((LinearFlag.conjAut d F g₀ * LinearFlag.conjAut d F C *
          (LinearFlag.conjAut d F g₀)⁻¹) * LinearFlag.conjAut d F g₀)
          (LinearFlag.proj d F h) =
        LinearFlag.conjAut d F g₀
          (LinearFlag.proj d F
            (CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation d F C h))
      rw [← LinearFlag.conjAut_proj]
      change ((LinearFlag.conjAut d F g₀ * LinearFlag.conjAut d F C *
          (LinearFlag.conjAut d F g₀)⁻¹) * LinearFlag.conjAut d F g₀)
          (LinearFlag.proj d F h) =
        (LinearFlag.conjAut d F g₀ * LinearFlag.conjAut d F C)
          (LinearFlag.proj d F h)
      rw [show LinearFlag.conjAut d F g₀ * LinearFlag.conjAut d F C *
          (LinearFlag.conjAut d F g₀)⁻¹ * LinearFlag.conjAut d F g₀ =
          LinearFlag.conjAut d F g₀ * LinearFlag.conjAut d F C by group]
  haveI hSLperf : Group.IsPerfect (Matrix.SpecialLinearGroup (Fin d) F) :=
    CFSG.LinearGroups.special_linear_dimension_at_least_three_perfect hd
  have hSL : commutator (Matrix.SpecialLinearGroup (Fin d) F) = ⊤ :=
    Group.IsPerfect.commutator_eq_top
  obtain ⟨k, eK, heKne, heKp, hAe, hBk, hke⟩ :=
    kgLangTorA_concl_of_lift (H := Matrix.SpecialLinearGroup (Fin d) F) (K := K)
      (R := LinearFlag.projectiveSL d F) hSL θ' A B₀ hdec κ'
      (Matrix.SpecialLinearGroup.map σ.toRingHom) hα₀ψ heKne hep he_fixed hs_fixed hβψ
  refine ⟨k, eK, heKne, heKp, hAe, ?_, hke⟩
  intro α hα hαI
  exact hBk α (hmem α hα hαI)

end CFSG.StandardType

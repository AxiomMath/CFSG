module

public import CFSG.LocalAnalysis.StandardType.KGLangTorAFields
public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherAutomorphismData
public import CFSG.LocalAnalysis.StandardType.GGTableBTypeATransport
public import CFSG.LocalAnalysis.StandardType.GGPGLToralityBasic
import CFSG.LocalAnalysis.StandardType.GGSecFiveTypeALift
import CFSG.LieType.Steinberg.CentralExt.SLCentrallyClosed
import CFSG.LocalAnalysis.ComponentInitial.LinearFlagElation
import CFSG.LocalAnalysis.ComponentInitial.LinearHigherAutomorphismTransport
import CFSG.LocalAnalysis.StandardType.GGTableBTypeALift
import CFSG.LocalAnalysis.ComponentInitial.LinearHigherFieldInvolution
import CFSG.LocalAnalysis.StandardType.GGPGLTorality
import CFSG.LocalAnalysis.StandardType.GGRecipeFieldLinear
import CFSG.LocalAnalysis.StandardType.GGNbrLangTypeALift
import CFSG.LocalAnalysis.StandardType.GGNbrFieldFixKnownLinearDescent

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.LocalAnalysis.ComponentInitial
open CFSG.GroupTheory.SteinbergBK (semilinearFixedSubfield)

theorem kgLangTorA_lin_lift {d : ℕ} {F : Type} [Field F] [Finite F] (hd : 3 ≤ d)
    (h2 : Nat.card F ≠ 2) (h4 : ¬(d = 3 ∧ Nat.card F = 4)) (h3 : Nat.card F ≠ 3)
    {K : Type} [Group K] (hK : commutator K = ⊤)
    (θ : K ⧸ Subgroup.center K ≃* LinearFlag.projectiveSL d F) :
    ∃ κ : Matrix.SpecialLinearGroup (Fin d) F →* K,
      ∀ g, θ (QuotientGroup.mk (κ g)) = LinearFlag.proj d F g := by
  obtain ⟨m, rfl⟩ : ∃ m, d = m + 1 := ⟨d - 1, by omega⟩
  let θ₂ := θ.trans (QuotientGroup.quotientMulEquivOfEq (LinearFlag.scalars_eq_center (m + 1) F))
  have hsep : CFSG.LieType.Steinberg.CentralExt.SLClosed.Separating m F :=
    CFSG.LieType.Steinberg.CentralExt.SLClosed.separating_of_card (by omega) h2
      (fun h => h4 ⟨by omega, h.2⟩) (fun h => h3 h.2)
  obtain ⟨κ, -, -, hlift⟩ := exists_slLift_of_mulEquiv (n := m) (by omega) hsep hK θ₂
  refine ⟨κ, fun g => ?_⟩
  apply (QuotientGroup.quotientMulEquivOfEq (LinearFlag.scalars_eq_center (m + 1) F)).injective
  exact hlift g

theorem kgLangTorA_lin_semifixed {d : ℕ} {F : Type} [Field F] [Finite F] (hd : 0 < d)
    (σ : F ≃+* F) (B : GL (Fin d) F)
    (h : LinearFlag.fieldAut d F σ * LinearFlag.conjAut d F B =
      LinearFlag.conjAut d F B * LinearFlag.fieldAut d F σ) :
    ∃ c : Fˣ, Matrix.GeneralLinearGroup.map (σ : F →+* F) B =
      Matrix.GeneralLinearGroup.scalar (Fin d) c * B := by
  have htrans := (LinearFlag.standard_automorphism_transport (n := d) (K := F)).2.2.1 σ B
  have hconj : LinearFlag.conjAut d F (Matrix.GeneralLinearGroup.map (σ : F →+* F) B) =
      LinearFlag.conjAut d F B := by
    rw [← htrans, h, mul_assoc, mul_inv_cancel, mul_one]
  have h1 : LinearFlag.conjAut d F
      (Matrix.GeneralLinearGroup.map (σ : F →+* F) B * B⁻¹) = 1 := by
    rw [map_mul, map_inv, hconj, mul_inv_cancel]
  obtain ⟨c, hc⟩ := TypeA.exists_scalar_of_conjAut_eq_one h1
  obtain ⟨u, hu⟩ := TypeA.exists_unit_of_scalar hd hc
  refine ⟨u, ?_⟩
  rw [← hu]
  group

theorem kgLangTorA_lin_descend_lift {d p : ℕ} {F : Type} [Field F] [Finite F] (hp : p.Prime)
    (hd : 0 < d) {σ : F ≃+* F} (hσ : orderOf σ = p) (B : GL (Fin d) F)
    (h : LinearFlag.fieldAut d F σ * LinearFlag.conjAut d F B =
      LinearFlag.conjAut d F B * LinearFlag.fieldAut d F σ) :
    ∃ (c : Fˣ) (M : GL (Fin d) (semilinearFixedSubfield σ)),
      B = Matrix.GeneralLinearGroup.scalar (Fin d) c *
        Matrix.GeneralLinearGroup.map (semilinearFixedSubfield σ).subtype M := by
  obtain ⟨c, hc⟩ := kgLangTorA_lin_semifixed hd σ B h
  haveI : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  obtain ⟨μ, M, hM⟩ : ∃ (μ : Fˣ) (M : GL (Fin d) (semilinearFixedSubfield σ)),
      ((Matrix.GeneralLinearGroup.map (semilinearFixedSubfield σ).subtype M : GL (Fin d) F) :
        Matrix (Fin d) (Fin d) F) = (μ : F) • (B : Matrix (Fin d) (Fin d) F) :=
    LinearFieldFix.exists_descend_of_map_eq_smul σ B c (by
      have := congrArg (fun A : GL (Fin d) F => (A : Matrix (Fin d) (Fin d) F)) hc
      simpa [Matrix.GeneralLinearGroup.coe_scalar, Matrix.smul_eq_diagonal_mul] using this)
  refine ⟨μ⁻¹, M, ?_⟩
  apply Units.ext
  rw [Matrix.GeneralLinearGroup.coe_mul, Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
    ← Matrix.smul_eq_diagonal_mul, hM, smul_smul, Units.inv_mul, one_smul]

private theorem kgLangTorALinAux_scalar_descent {d : ℕ} {F : Type} [Field F] [Finite F]
    {σ : F ≃+* F} (hd : 0 < d) {M : GL (Fin d) (semilinearFixedSubfield σ)}
    (h : LinearFlag.conjAut d F
      (Matrix.GeneralLinearGroup.map (semilinearFixedSubfield σ).subtype M) = 1) :
    ∃ c₀ : (semilinearFixedSubfield σ)ˣ,
      M = Matrix.GeneralLinearGroup.scalar (Fin d) c₀ := by
  obtain ⟨c, hc⟩ := TypeA.exists_scalar_of_conjAut_eq_one (K := F) h
  obtain ⟨u, hu⟩ := TypeA.exists_unit_of_scalar hd hc
  have hentry : ∀ i j : Fin d,
      (semilinearFixedSubfield σ).subtype
        ((M : Matrix (Fin d) (Fin d) (semilinearFixedSubfield σ)) i j) =
        (if i = j then (u : F) else 0) := by
    intro i j
    have h1 := congrArg (fun A : GL (Fin d) F =>
      (A : Matrix (Fin d) (Fin d) F) i j) hu
    rw [Matrix.GeneralLinearGroup.map_apply, Matrix.GeneralLinearGroup.coe_scalar,
      Matrix.scalar_apply, Matrix.diagonal_apply] at h1
    exact h1
  let a : semilinearFixedSubfield σ :=
    (M : Matrix (Fin d) (Fin d) (semilinearFixedSubfield σ)) ⟨0, hd⟩ ⟨0, hd⟩
  have hdiag : (semilinearFixedSubfield σ).subtype a = (u : F) := by
    have h1 := hentry ⟨0, hd⟩ ⟨0, hd⟩
    simpa [a] using h1
  have ha0 : a ≠ 0 := by
    intro h0
    have h2 : (u : F) = 0 := by rw [← hdiag, h0]; rfl
    exact u.ne_zero h2
  refine ⟨Units.mk0 a ha0, ?_⟩
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  by_cases hij : i = j
  · subst hij
    rw [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.diagonal_apply_eq,
      Units.val_mk0]
    exact (semilinearFixedSubfield σ).subtype_injective (by
      rw [hentry i i, if_pos rfl, hdiag])
  · rw [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
      Matrix.diagonal_apply_ne _ hij]
    exact (semilinearFixedSubfield σ).subtype_injective (by
      rw [hentry i j, if_neg hij, map_zero])

theorem kgLangTorA_lin_fixed_group {d p : ℕ} {F : Type} [Field F] [Finite F] (hp : p.Prime)
    (hd : 0 < d) {σ : F ≃+* F} (hσ : orderOf σ = p)
    {X : Subgroup (MulAut (LinearFlag.projectiveSL d F))} (hX : IsElemAbelian p X)
    (hXc : ∀ x ∈ X, x ∈ Set.range (LinearFlag.conjAut d F))
    (hXσ : ∀ x ∈ X, LinearFlag.fieldAut d F σ * x = x * LinearFlag.fieldAut d F σ) :
    TypeA.PGLTor.IsProjElem p (X.comap ((LinearFlag.conjAut d F).comp
        (Matrix.GeneralLinearGroup.map (semilinearFixedSubfield σ).subtype))) ∧
      Nat.card (X.comap ((LinearFlag.conjAut d F).comp
        (Matrix.GeneralLinearGroup.map (semilinearFixedSubfield σ).subtype))) =
        Nat.card X * (Nat.card (semilinearFixedSubfield σ) - 1) := by
  haveI : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  let χ : GL (Fin d) (semilinearFixedSubfield σ) →* MulAut (LinearFlag.projectiveSL d F) :=
    (LinearFlag.conjAut d F).comp
      (Matrix.GeneralLinearGroup.map (semilinearFixedSubfield σ).subtype)
  change TypeA.PGLTor.IsProjElem p (X.comap χ) ∧
    Nat.card (X.comap χ) = Nat.card X * (Nat.card (semilinearFixedSubfield σ) - 1)
  set Ĝ : Subgroup (GL (Fin d) (semilinearFixedSubfield σ)) := X.comap χ with hĜ
  have hmem : ∀ M : GL (Fin d) (semilinearFixedSubfield σ), M ∈ Ĝ ↔ χ M ∈ X := by
    intro M
    rw [hĜ, Subgroup.mem_comap]
  have hscalar : ∀ u : (semilinearFixedSubfield σ)ˣ,
      Matrix.GeneralLinearGroup.scalar (Fin d) u ∈ Ĝ := by
    intro u
    rw [hmem]
    show LinearFlag.conjAut d F (Matrix.GeneralLinearGroup.map
      (semilinearFixedSubfield σ).subtype
      (Matrix.GeneralLinearGroup.scalar (Fin d) u)) ∈ X
    rw [Matrix.GeneralLinearGroup.map_scalar, LinearFlag.conjAut_scalar]
    exact X.one_mem
  have hpow : ∀ M ∈ Ĝ, ∃ u : (semilinearFixedSubfield σ)ˣ,
      M ^ p = Matrix.GeneralLinearGroup.scalar (Fin d) u := by
    intro M hM
    have hχp : χ M ^ p = 1 := hX.2 (χ M) ((hmem M).mp hM)
    have hconj : LinearFlag.conjAut d F (Matrix.GeneralLinearGroup.map
        (semilinearFixedSubfield σ).subtype (M ^ p)) = 1 := by
      rw [map_pow, map_pow]
      exact hχp
    exact kgLangTorALinAux_scalar_descent hd hconj
  have hcomm : ∀ M ∈ Ĝ, ∀ N ∈ Ĝ, ∃ u : (semilinearFixedSubfield σ)ˣ,
      M * N = Matrix.GeneralLinearGroup.scalar (Fin d) u * (N * M) := by
    intro M hM N hN
    have hMN : χ M * χ N = χ N * χ M :=
      congrArg Subtype.val (hX.1.is_comm.comm ⟨χ M, (hmem M).mp hM⟩ ⟨χ N, (hmem N).mp hN⟩)
    have hconj : LinearFlag.conjAut d F (Matrix.GeneralLinearGroup.map
        (semilinearFixedSubfield σ).subtype (M * N * (N * M)⁻¹)) = 1 := by
      simp only [map_mul, map_inv]
      show χ M * χ N * (χ N * χ M)⁻¹ = 1
      rw [hMN, mul_inv_cancel]
    obtain ⟨u, hu⟩ := kgLangTorALinAux_scalar_descent hd hconj
    refine ⟨u, ?_⟩
    rw [← hu]
    group
  have hproj : TypeA.PGLTor.IsProjElem p Ĝ := ⟨hscalar, hpow, hcomm⟩
  let f : Ĝ →* MulAut (LinearFlag.projectiveSL d F) := χ.comp Ĝ.subtype
  have hrange : f.range = X := by
    ext x
    constructor
    · rintro ⟨M, rfl⟩
      exact (hmem M).mp M.2
    · intro hx
      obtain ⟨B, rfl⟩ := hXc x hx
      obtain ⟨c, M, hM⟩ := kgLangTorA_lin_descend_lift hp hd hσ B (hXσ _ hx)
      have hχM : χ M = LinearFlag.conjAut d F B := by
        simp only [χ, MonoidHom.comp_apply, hM, map_mul, LinearFlag.conjAut_scalar, one_mul]
      refine ⟨⟨M, ?_⟩, ?_⟩
      · rw [hmem, hχM]; exact hx
      · exact hχM
  have hker : Nat.card f.ker = Nat.card (semilinearFixedSubfield σ) - 1 := by
    rw [← Nat.card_units (semilinearFixedSubfield σ)]
    symm
    let g : (semilinearFixedSubfield σ)ˣ → f.ker := fun u =>
      ⟨⟨Matrix.GeneralLinearGroup.scalar (Fin d) u, hscalar u⟩, by
        rw [MonoidHom.mem_ker]
        show LinearFlag.conjAut d F (Matrix.GeneralLinearGroup.map
          (semilinearFixedSubfield σ).subtype
          (Matrix.GeneralLinearGroup.scalar (Fin d) u)) = 1
        rw [Matrix.GeneralLinearGroup.map_scalar, LinearFlag.conjAut_scalar]⟩
    refine Nat.card_eq_of_bijective g ⟨?_, ?_⟩
    · intro u v huv
      have h1 : Matrix.GeneralLinearGroup.scalar (Fin d) u =
          Matrix.GeneralLinearGroup.scalar (Fin d) v :=
        congrArg (fun z : f.ker => ((z : Ĝ) : GL (Fin d) (semilinearFixedSubfield σ))) huv
      exact TypeA.PGLTor.scalar_injective h1
    · rintro ⟨⟨M, hMĜ⟩, hMker⟩
      have hχM : χ M = 1 := MonoidHom.mem_ker.mp hMker
      obtain ⟨u, hu⟩ := kgLangTorALinAux_scalar_descent hd hχM
      refine ⟨u, ?_⟩
      apply Subtype.ext
      apply Subtype.ext
      exact hu.symm
  refine ⟨hproj, ?_⟩
  rw [← Subgroup.card_ker_mul_card_range f, hrange, hker, mul_comm]

theorem kgLangTorA_lin_transport {d p : ℕ} {F : Type} [Field F] [Finite F] (hp : p.Prime)
    (hd : 3 ≤ d)
    {X : Subgroup (MulAut (LargeEvenProj (LargeEvenSLGroup (Fin d) F)))}
    (hX : IsElemAbelian p X)
    (hXI : ∀ x ∈ X,
      x ∈ LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSLGroup (Fin d) F)) Set.univ)
    {f₀ : MulAut (LargeEvenProj (LargeEvenSLGroup (Fin d) F))}
    (hf₀ : f₀ ∈ LargeEvenMatFieldImage (LargeEvenProjMk (LargeEvenSLGroup (Fin d) F)))
    (hf₀p : orderOf f₀ = p) (hXf : ∀ x ∈ X, f₀ * x = x * f₀) :
    ∃ σ : F ≃+* F, orderOf σ = p ∧
      MulAut.congr (TypeA.recipeEquiv d F) f₀ = LinearFlag.fieldAut d F σ ∧
      IsElemAbelian p (X.map (MulAut.congr (TypeA.recipeEquiv d F)).toMonoidHom) ∧
      (∀ x ∈ X.map (MulAut.congr (TypeA.recipeEquiv d F)).toMonoidHom,
        x ∈ Set.range (LinearFlag.conjAut d F)) ∧
      (∀ x ∈ X.map (MulAut.congr (TypeA.recipeEquiv d F)).toMonoidHom,
        LinearFlag.fieldAut d F σ * x = x * LinearFlag.fieldAut d F σ) ∧
      Nat.card (X.map (MulAut.congr (TypeA.recipeEquiv d F)).toMonoidHom) = Nat.card X := by
  let E : MulAut (LargeEvenProj (LargeEvenSLGroup (Fin d) F)) ≃*
      MulAut (LinearFlag.projectiveSL d F) := MulAut.congr (TypeA.recipeEquiv d F)
  obtain ⟨σ, hσE⟩ := RecipeFieldLinear.congr_field_eq hf₀
  have hfield_inj : Function.Injective (LinearFlag.fieldAut d F) := by
    intro a b hab
    have hab' : LinearFlag.fieldAut d F (a * b⁻¹) = 1 := by
      rw [map_mul, map_inv, hab, mul_inv_cancel]
    have h1 : LinearFlag.conjAut d F (1 : GL (Fin d) F) *
        LinearFlag.fieldAut d F (a * b⁻¹) = 1 := by
      rw [hab', mul_one, map_one]
    obtain ⟨h, -⟩ := RecipeFieldLinear.eq_one_of_conjAut_mul_fieldAut_eq_one' (n := d)
      (by omega) (Or.inl hd) 1 (a * b⁻¹) h1
    exact mul_inv_eq_one.mp h
  have horderσ : orderOf σ = p := by
    have h1 : orderOf σ = orderOf f₀ := by
      rw [← orderOf_injective (LinearFlag.fieldAut d F) hfield_inj σ, ← hσE]
      exact orderOf_injective E.toMonoidHom (MulEquiv.injective E) f₀
    rw [h1, hf₀p]
  have hXmap : IsElemAbelian p (X.map E.toMonoidHom) := by
    refine ⟨⟨⟨fun a b => ?_⟩⟩, fun y hy => ?_⟩
    · apply Subtype.ext
      obtain ⟨x, hx, hxE⟩ := Subgroup.mem_map.mp a.2
      obtain ⟨x', hx', hx'E⟩ := Subgroup.mem_map.mp b.2
      rw [Subgroup.coe_mul, Subgroup.coe_mul, hxE.symm, hx'E.symm]
      have hxx' : x * x' = x' * x := congrArg Subtype.val (hX.1.is_comm.comm ⟨x, hx⟩ ⟨x', hx'⟩)
      simpa only [map_mul] using congrArg E.toMonoidHom hxx'
    · obtain ⟨x, hx, hxE⟩ := Subgroup.mem_map.mp hy
      rw [hxE.symm, ← map_pow, hX.2 x hx, map_one]
  have hrange_conj : ∀ y ∈ X.map E.toMonoidHom,
      y ∈ Set.range (LinearFlag.conjAut d F) := by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hy
    exact TypeA.congr_recipeEquiv_mem (hXI x hx)
  have hcommf : ∀ y ∈ X.map E.toMonoidHom,
      LinearFlag.fieldAut d F σ * y = y * LinearFlag.fieldAut d F σ := by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hy
    have hσE' : LinearFlag.fieldAut d F σ = E.toMonoidHom f₀ := hσE.symm
    rw [hσE', ← map_mul, ← map_mul, hXf x hx]
  exact ⟨σ, horderσ, hσE, hXmap, hrange_conj, hcommf,
    Subgroup.card_map_of_injective (MulEquiv.injective E)⟩

end CFSG.StandardType

module

public import CFSG.LocalAnalysis.StandardType.GGTwE6E4bOriginalField
public import CFSG.LocalAnalysis.StandardType.GGTwE6E4bOriginalActorLift
public import CFSG.LocalAnalysis.StandardType.GGTwE6E4bActorSeed
public import CFSG.LocalAnalysis.StandardType.GGOneFiveDefs
public import CFSG.LocalAnalysis.StandardType.GGTableBStdSub
public import CFSG.Mathlib.GroupTheory.EquivariantNormalizer

public noncomputable section


namespace CFSG.StandardType.E4bOriginalSC

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.LieType.Steinberg CFSG.LieType.Steinberg.Isogeny CFSG.LieType.Steinberg.Minuscule
open CFSG.StandardType.E4bLift CFSG.StandardType.E4bOriginalLift
open CFSG.LieType.AlgebraicGroups CFSG.StandardType.TwE6E4bTorus
open CFSG.StandardType.TwE6FixedA2SL3
open CFSG.StandardType.SCFourCover CFSG.StandardType.GGFinModel
open scoped MatrixGroups

variable {n : ℕ} {K : Type} [Field K] [Finite K]
  {σ : K ≃+* K} {J : Type} [Group J]

@[expose] noncomputable def originalEFrame
    (hn : 1 ≤ n) (hK : Nat.card K = (2 ^ n) ^ 2)
    (hσ : ∀ c, σ c = c ^ 2 ^ n)
    [Algebra K GGL] [IsAlgClosure K GGL]
    (Fr : GGL →+* GGL) (hFr : ∀ c, Fr c = c ^ 2 ^ n)
    (ε : ↥(graphFixedRootGroup TwistTag.E6 K σ.toRingHom) ≃* TwE6Delta.RecipeR K n)
    (ψ : J →* TwE6Delta.RecipeR K n) (A : Subgroup (MulAut J))
    (y0 : ModGL Tag.E6 GGL) :
    Subgroup (ModGL Tag.E6 GGL) :=
  (rgrpModel hn hK σ hσ Fr hFr ε (TypeA.inducedSub ψ A)).map
    (MulAut.conj y0).toMonoidHom

@[expose] noncomputable def originalScalarPoint (ω : GGLˣ) : ModGL Tag.E6 GGL :=
  fixedA2Rho GGL (fixedA2Scalar (F := GGL) ω)


theorem originalM_mem_adjointGroup {F : Type} [Field F] [Finite F] [Finite J]
    (ι : K →+* F) (t : ↥(e6Data_valid.minGroup F))
    (ε : ↥(graphFixedRootGroup TwistTag.E6 K σ.toRingHom) ≃* TwE6Delta.RecipeR K n)
    (ψ : J →* TwE6Delta.RecipeR K n) (g : J) :
    originalM (K := K) (F := F) (σ := σ) (ε := ε) (ψ := ψ) ι t g ∈
      adjointGroup Tag.E6 F := by
  rw [originalM_apply, MulAut.conj_apply]
  have hx : baseChangeGL (τ := Tag.E6) ι ((ε.symm (ψ g)).1) ∈ adjointGroup Tag.E6 F :=
    baseChangeGL_mem_adjointGroup ι
      ((graphFixedRootGroup_le (TwistTag.E6) K σ.toRingHom).trans
        (twistedFixedGroup_le_adjointGroup (TwistTag.E6) K σ.toRingHom)
        (ε.symm (ψ g)).2)
  exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (e6Isogeny F t).2 hx)
    (Subgroup.inv_mem _ (e6Isogeny F t).2)

theorem baseChange_originalScalarPoint {F : Type} [Field F] [Finite F] [CharP F 2]
    (κ : F →+* GGL) {ωF : Fˣ} {ωΩ : GGLˣ} (hω : Units.map κ ωF = ωΩ) :
    baseChangeGL (τ := Tag.E6) κ
        (fixedA2Rho F (fixedA2Scalar (F := F) ωF)) = originalScalarPoint ωΩ := by
  have hωval : κ (ωF : F) = (ωΩ : GGL) := congrArg Units.val hω
  have hmap : Matrix.SpecialLinearGroup.map κ (fixedA2Scalar (F := F) ωF) =
      fixedA2Scalar (F := GGL) ωΩ := by
    rw [fixedA2Scalar_eq_diagSL3 (F := F) ωF,
      fixedA2Scalar_eq_diagSL3 (F := GGL) ωΩ]
    ext i j
    rw [Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply]
    fin_cases i <;> fin_cases j <;>
      simp [diagSL3, Matrix.map_apply, Units.coe_map, hωval, pow_two, mul_assoc]
  change baseChangeGL (τ := Tag.E6) κ
      (fixedA2Rho F (fixedA2Scalar (F := F) ωF)) = originalScalarPoint ωΩ
  rw [baseChangeGL_fixedA2Rho, hmap]
  rfl

theorem framed_recipeActorModelEquiv_conj
    (hn : 1 ≤ n) (hK : Nat.card K = (2 ^ n) ^ 2)
    (hσ : ∀ c, σ c = c ^ 2 ^ n)
    [Algebra K GGL] [IsAlgClosure K GGL]
    (Fr : GGL →+* GGL) (hFr : ∀ c, Fr c = c ^ 2 ^ n)
    (ε : ↥(graphFixedRootGroup TwistTag.E6 K σ.toRingHom) ≃* TwE6Delta.RecipeR K n)
    (hε : ∀ x : MulAut ↥(graphFixedRootGroup TwistTag.E6 K σ.toRingHom),
      MulAut.congr ε x ∈ TwE6Delta.RecipeI K n ↔ x ∈ (RecipeExcLang.twConj K σ).range)
    {ψ : J →* TwE6Delta.RecipeR K n}
    (hψ : Function.Surjective ψ) (hker : ψ.ker ≤ Subgroup.center J)
    (hperf : commutator J = ⊤)
    {A : Subgroup (MulAut J)}
    (hAI : ∀ a ∈ A, ∃ φ ∈ TwE6Delta.RecipeI K n, ∀ l : J, φ (ψ l) = ψ (a l))
    {g : J} (hgN : MulAut.conj g ∈ Subgroup.normalizer (A : Set (MulAut J)))
    (a : A) {y0 : ModGL Tag.E6 GGL} :
    y0 * (recipeActorModelEquiv (A := A) hn hK σ hσ Fr hFr ε hε hψ hker hperf hAI
      (ggConjAut A hgN a) : ModGL Tag.E6 GGL) * y0⁻¹ =
      (y0 * recipeMatrixHom (Ω := GGL) σ ε (ψ := ψ) g * y0⁻¹) *
        (y0 * (recipeActorModelEquiv (A := A) hn hK σ hσ Fr hFr ε hε
          hψ hker hperf hAI a : ModGL Tag.E6 GGL) * y0⁻¹) *
        (y0 * recipeMatrixHom (Ω := GGL) σ ε (ψ := ψ) g * y0⁻¹)⁻¹ := by
  let f : A →* ModGL Tag.E6 GGL :=
    (rgrpModel hn hK σ hσ Fr hFr ε (TypeA.inducedSub ψ A)).subtype.comp
      (recipeActorModelEquiv (A := A) hn hK σ hσ Fr hFr ε hε hψ hker hperf hAI).toMonoidHom
  have hact : ∀ a : A, f (ggConjAut A hgN a) =
      recipeMatrixHom (Ω := GGL) σ ε (ψ := ψ) g * f a *
        (recipeMatrixHom (Ω := GGL) σ ε (ψ := ψ) g)⁻¹ := by
    intro a
    simpa [f] using
      (SCFourCover.recipeActorModelEquiv_conj (A := A) (g := g) (Ω := GGL)
        hn hK σ hσ Fr hFr ε hε hψ hker hperf hAI hgN a)
  have h := CFSG.GroupTheory.equivariant_comp_conj f (ggConjAut A hgN)
    (recipeMatrixHom (Ω := GGL) σ ε (ψ := ψ) g) y0 hact
  simpa [f, MulAut.conj_apply] using h a

theorem framed_recipe_normalizes_originalEFrame
    (hn : 1 ≤ n) (hK : Nat.card K = (2 ^ n) ^ 2)
    (hσ : ∀ c, σ c = c ^ 2 ^ n)
    [Algebra K GGL] [IsAlgClosure K GGL]
    (Fr : GGL →+* GGL) (hFr : ∀ c, Fr c = c ^ 2 ^ n)
    (ε : ↥(graphFixedRootGroup TwistTag.E6 K σ.toRingHom) ≃* TwE6Delta.RecipeR K n)
    (hε : ∀ x : MulAut ↥(graphFixedRootGroup TwistTag.E6 K σ.toRingHom),
      MulAut.congr ε x ∈ TwE6Delta.RecipeI K n ↔ x ∈ (RecipeExcLang.twConj K σ).range)
    {ψ : J →* TwE6Delta.RecipeR K n}
    (hψ : Function.Surjective ψ) (hker : ψ.ker ≤ Subgroup.center J)
    (hperf : commutator J = ⊤)
    {A : Subgroup (MulAut J)}
    (hAI : ∀ a ∈ A, ∃ φ ∈ TwE6Delta.RecipeI K n, ∀ l : J, φ (ψ l) = ψ (a l))
    {g : J} (hgN : MulAut.conj g ∈ Subgroup.normalizer (A : Set (MulAut J)))
    {y0 : ModGL Tag.E6 GGL} :
    y0 * recipeMatrixHom (Ω := GGL) σ ε (ψ := ψ) g * y0⁻¹ ∈
      Subgroup.normalizer
        (originalEFrame (J := J) hn hK hσ Fr hFr ε ψ A y0 :
          Set (ModGL Tag.E6 GGL)) := by
  let ρ : Subgroup (ModGL Tag.E6 GGL) :=
    rgrpModel hn hK σ hσ Fr hFr ε (TypeA.inducedSub ψ A)
  let γ := recipeActorModelEquiv (A := A) hn hK σ hσ Fr hFr ε hε hψ hker hperf hAI
  let base : A →* ModGL Tag.E6 GGL := ρ.subtype.comp γ.toMonoidHom
  let f : A →* ModGL Tag.E6 GGL := (MulAut.conj y0).toMonoidHom.comp base
  have hbase_act : ∀ a : A, base (ggConjAut A hgN a) =
      recipeMatrixHom (Ω := GGL) σ ε (ψ := ψ) g * base a *
        (recipeMatrixHom (Ω := GGL) σ ε (ψ := ψ) g)⁻¹ := by
    intro a
    simpa [base, ρ, γ] using
      (SCFourCover.recipeActorModelEquiv_conj (A := A) (g := g) (Ω := GGL)
        hn hK σ hσ Fr hFr ε hε hψ hker hperf hAI hgN a)
  have hact : ∀ a : A, f (ggConjAut A hgN a) =
      (y0 * recipeMatrixHom (Ω := GGL) σ ε (ψ := ψ) g * y0⁻¹) * f a *
        (y0 * recipeMatrixHom (Ω := GGL) σ ε (ψ := ψ) g * y0⁻¹)⁻¹ :=
    CFSG.GroupTheory.equivariant_comp_conj base (ggConjAut A hgN)
      (recipeMatrixHom (Ω := GGL) σ ε (ψ := ψ) g) y0 hbase_act
  have hN := CFSG.GroupTheory.mem_normalizer_range_of_equivariant f (ggConjAut A hgN)
    (y0 * recipeMatrixHom (Ω := GGL) σ ε (ψ := ψ) g * y0⁻¹) hact
  have hbase_range : base.range = ρ := by
    change (ρ.subtype.comp γ.toMonoidHom).range = ρ
    rw [MonoidHom.range_comp]
    rw [MonoidHom.range_eq_top_of_surjective γ.toMonoidHom γ.surjective]
    rw [Subgroup.map_top]
    exact Subgroup.range_subtype ρ
  have hfrange : f.range = originalEFrame (J := J) hn hK hσ Fr hFr ε ψ A y0 := by
    change ((MulAut.conj y0).toMonoidHom.comp base).range = _
    rw [MonoidHom.range_comp, hbase_range]
    rfl
  simpa [hfrange] using hN

theorem framed_recipe_mem_adjointGroup
    (hn : 1 ≤ n) (hK : Nat.card K = (2 ^ n) ^ 2)
    (hσ : ∀ c, σ c = c ^ 2 ^ n)
    [Algebra K GGL] [IsAlgClosure K GGL]
    (Fr : GGL →+* GGL) (hFr : ∀ c, Fr c = c ^ 2 ^ n)
    (ε : ↥(graphFixedRootGroup TwistTag.E6 K σ.toRingHom) ≃* TwE6Delta.RecipeR K n)
    {ψ : J →* TwE6Delta.RecipeR K n}
    {y0 : ModGL Tag.E6 GGL} (hy0 : y0 ∈ adjointGroup Tag.E6 GGL) (g : J) :
    y0 * recipeMatrixHom (Ω := GGL) σ ε (ψ := ψ) g * y0⁻¹ ∈
      adjointGroup Tag.E6 GGL := by
  have hg : recipeMatrixHom (Ω := GGL) σ ε (ψ := ψ) g ∈
      adjointGroup Tag.E6 GGL :=
    (recipeMatrixHom_mem_Rgrp (Ω := GGL) hn hK σ hσ Fr hFr ε (ψ := ψ) g).1
  exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hy0 hg) (Subgroup.inv_mem _ hy0)

theorem framed_recipe_normalizes_fixedA2Torus
    (hn : 1 ≤ n) (hK : Nat.card K = (2 ^ n) ^ 2)
    (hσ : ∀ c, σ c = c ^ 2 ^ n)
    [Algebra K GGL] [IsAlgClosure K GGL]
    (Fr : GGL →+* GGL) (hFr : ∀ c, Fr c = c ^ 2 ^ n)
    (ε : ↥(graphFixedRootGroup TwistTag.E6 K σ.toRingHom) ≃* TwE6Delta.RecipeR K n)
    (hε : ∀ x : MulAut ↥(graphFixedRootGroup TwistTag.E6 K σ.toRingHom),
      MulAut.congr ε x ∈ TwE6Delta.RecipeI K n ↔ x ∈ (RecipeExcLang.twConj K σ).range)
    {ψ : J →* TwE6Delta.RecipeR K n}
    (hψ : Function.Surjective ψ) (hker : ψ.ker ≤ Subgroup.center J)
    (hperf : commutator J = ⊤)
    {A : Subgroup (MulAut J)}
    (hAI : ∀ a ∈ A, ∃ φ ∈ TwE6Delta.RecipeI K n, ∀ l : J, φ (ψ l) = ψ (a l))
    {g : J} (hgN : MulAut.conj g ∈ Subgroup.normalizer (A : Set (MulAut J)))
    {y0 : ModGL Tag.E6 GGL} (hy0 : y0 ∈ adjointGroup Tag.E6 GGL)
    (hS : (closedIdentityComponent (adjointGroup Tag.E6 GGL ⊓
      Subgroup.centralizer
        (originalEFrame (J := J) hn hK hσ Fr hFr ε ψ A y0 :
          Set (ModGL Tag.E6 GGL))) : Set (ModGL Tag.E6 GGL)) = fixedA2Torus GGL) :
    y0 * recipeMatrixHom (Ω := GGL) σ ε (ψ := ψ) g * y0⁻¹ ∈
      Subgroup.normalizer (fixedA2Torus GGL) := by
  have hRE := framed_recipe_normalizes_originalEFrame (J := J)
    hn hK hσ Fr hFr ε hε hψ hker hperf hAI hgN (y0 := y0)
  have hRA := framed_recipe_mem_adjointGroup (J := J)
    hn hK hσ Fr hFr ε (ψ := ψ) hy0 g
  have h := mem_normalizer_connected_adjoint_centralizer
    (originalEFrame (J := J) hn hK hσ Fr hFr ε ψ A y0) hRA hRE
  rwa [hS] at h

theorem exists_originalSC_return
    {G : Type} [Group G] [Finite G] {B Bs J : Subgroup G}
    (hBs : GGBstar 3 B Bs)
    (hN : Bs ≤ Subgroup.normalizer (J : Set G))
    {n : ℕ} (hn : 1 ≤ n) {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = (2 ^ n) ^ 2) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ 2 ^ n)
    (h3 : 3 ∣ 2 ^ n + 1)
    [Algebra K GGL] [IsAlgClosure K GGL]
    (Fr : GGL →+* GGL) (hFr : ∀ c, Fr c = c ^ 2 ^ n)
    (ε : ↥(graphFixedRootGroup TwistTag.E6 K σ.toRingHom) ≃* TwE6Delta.RecipeR K n)
    (hε : ∀ x : MulAut ↥(graphFixedRootGroup TwistTag.E6 K σ.toRingHom),
      MulAut.congr ε x ∈ TwE6Delta.RecipeI K n ↔ x ∈ (RecipeExcLang.twConj K σ).range)
    {ψ : ↥J →* TwE6Delta.RecipeR K n}
    (hψ : Function.Surjective ψ) (hker : ψ.ker ≤ Subgroup.center ↥J)
    (hperf : commutator ↥J = ⊤)
    (hAI : ∀ a ∈ actualRecipeActorGroup hN,
      ∃ φ ∈ TwE6Delta.RecipeI K n, ∀ l : ↥J, φ (ψ l) = ψ (a l))
    {y0 : ModGL Tag.E6 GGL} (hy0 : y0 ∈ adjointGroup Tag.E6 GGL)
    {ωΩ : GGLˣ} (hω3 : ωΩ ^ 3 = 1) (hω1 : ωΩ ≠ 1)
    (haΩ : originalScalarPoint ωΩ ∈
      originalEFrame (J := ↥J) hn hK hσ Fr hFr ε ψ (actualRecipeActorGroup hN) y0)
    (hS : (closedIdentityComponent (adjointGroup Tag.E6 GGL ⊓
        Subgroup.centralizer
          (originalEFrame (J := ↥J) hn hK hσ Fr hFr ε ψ
            (actualRecipeActorGroup hN) y0 : Set (ModGL Tag.E6 GGL))) :
        Set (ModGL Tag.E6 GGL)) = fixedA2Torus GGL)
    {g0 : ↥J}
    (hg0N : MulAut.conj g0 ∈
      Subgroup.normalizer (actualRecipeActorGroup hN : Set (MulAut ↥J)))
    (hR0 : (y0 * recipeMatrixHom (Ω := GGL) σ ε (ψ := ψ) g0 * y0⁻¹) *
        originalScalarPoint ωΩ *
        (y0 * recipeMatrixHom (Ω := GGL) σ ε (ψ := ψ) g0 * y0⁻¹)⁻¹ =
      (originalScalarPoint ωΩ)⁻¹) :
    ∃ c : ↥J, c ^ 3 = 1 ∧ c ≠ 1 ∧ ((c : G) ∈ Bs) ∧
      y0 * recipeMatrixHom (Ω := GGL) σ ε (ψ := ψ) c * y0⁻¹ =
        originalScalarPoint ωΩ ∧
      ∀ (g : ↥J) (hgN : MulAut.conj g ∈
          Subgroup.normalizer (actualRecipeActorGroup hN : Set (MulAut ↥J))) (m : ℤ),
        (y0 * recipeMatrixHom (Ω := GGL) σ ε (ψ := ψ) g * y0⁻¹) *
            originalScalarPoint ωΩ *
            (y0 * recipeMatrixHom (Ω := GGL) σ ε (ψ := ψ) g * y0⁻¹)⁻¹ =
          (originalScalarPoint ωΩ) ^ m →
        MulAut.conj g c = c ^ m := by
  classical
  let A : Subgroup (MulAut ↥J) := actualRecipeActorGroup hN
  let aΩ : ModGL Tag.E6 GGL := originalScalarPoint ωΩ
  let E' : Subgroup (ModGL Tag.E6 GGL) :=
    originalEFrame (J := ↥J) hn hK hσ Fr hFr ε ψ A y0
  have haΩE' : aΩ ∈ E' := by simpa [E', aΩ] using haΩ
  have hS' : (closedIdentityComponent (adjointGroup Tag.E6 GGL ⊓
      Subgroup.centralizer (E' : Set (ModGL Tag.E6 GGL))) :
      Set (ModGL Tag.E6 GGL)) = fixedA2Torus GGL := by
    simpa [E'] using hS
  obtain ⟨F, hFfield, hFfin, hFchar, ιK, κ, ζF, ωF, y0F, eF, t, σF,
    hιK, hωFmap, hζFmap3, hζF3, hωF3, hωF1, hcard4, hσF, hy0F, ht, hπt,
    hmodelJ, heF, hmodel⟩ :=
    E4bOriginalField.exists_common_field_original_actor_model
      (G := G) hN hn hK σ hσ Fr hFr ε hε hψ hker hperf hAI hy0 hω3 hω1
  letI : Field F := hFfield
  letI : Finite F := hFfin
  letI : CharP F 2 := hFchar
  let aF : adjointGroup Tag.E6 F := fixedA2AdjRho (F := F) (fixedA2Scalar (F := F) ωF)
  have haFbase : baseChangeGL (τ := Tag.E6) κ (aF : ModGL Tag.E6 F) = aΩ := by
    change baseChangeGL (τ := Tag.E6) κ
        (fixedA2Rho F (fixedA2Scalar (F := F) ωF)) = originalScalarPoint ωΩ
    exact baseChange_originalScalarPoint κ hωFmap
  obtain ⟨r, hrE', hrconj⟩ := Subgroup.mem_map.mp haΩE'
  have hrE : r ∈ rgrpModel hn hK σ hσ Fr hFr ε (TypeA.inducedSub ψ A) := hrE'
  obtain ⟨τ, hτ⟩ := (recipeActorModelEquiv (A := A) hn hK σ hσ Fr hFr ε hε
    hψ hker hperf hAI).surjective ⟨r, hrE⟩
  have hγτ : (recipeActorModelEquiv (A := A) hn hK σ hσ Fr hFr ε hε hψ hker hperf hAI
      τ : ModGL Tag.E6 GGL) = r := congrArg Subtype.val hτ
  have hτframe : y0 * (recipeActorModelEquiv (A := A) hn hK σ hσ Fr hFr ε hε
      hψ hker hperf hAI τ : ModGL Tag.E6 GGL) * y0⁻¹ = aΩ := by
    rw [hγτ]
    simpa [MulAut.conj_apply, aΩ] using hrconj
  have hA3 : ∀ a : A, a ^ 3 = 1 := by
    rintro ⟨_, b, rfl⟩
    apply Subtype.ext
    change (ggGamma J hN b) ^ 3 = 1
    have hb3 : b ^ 3 = 1 := Subtype.ext (by simpa using hBs.2.1.2 (b : G) b.2)
    rw [← map_pow, hb3, map_one]
  have hAcomm : ∀ a b : A, a * b = b * a := by
    rintro ⟨_, x, rfl⟩ ⟨_, y, rfl⟩
    apply Subtype.ext
    change ggGamma J hN x * ggGamma J hN y = ggGamma J hN y * ggGamma J hN x
    rw [← map_mul, ← map_mul, hBs.2.1.1.is_comm.comm x y]
  have hτ3A : τ ^ 3 = 1 := hA3 τ
  have hτ3 : (τ : MulAut ↥J) ^ 3 = 1 := by
    simpa using congrArg (fun x : A => (x : MulAut ↥J)) hτ3A
  have heFτbase : baseChangeGL (τ := Tag.E6) κ ((eF τ : ModGL Tag.E6 F)) = aΩ := by
    rw [heF τ, hτframe]
  have heFτ : eF τ = aF := by
    apply Subtype.ext
    apply baseChangeGL_injective (τ := Tag.E6) κ
    rw [heFτbase, haFbase]
  have hτg : originalM (K := K) (F := F) (σ := σ) (ε := ε) (ψ := ψ) ιK t
      ((τ : MulAut ↥J) g0) =
        (aF : ModGL Tag.E6 F) * originalM (K := K) (F := F) (σ := σ)
          (ε := ε) (ψ := ψ) ιK t g0 * (aF : ModGL Tag.E6 F)⁻¹ := by
    have h := hmodel τ g0
    rw [heFτ] at h
    exact h
  let R0 : ModGL Tag.E6 GGL := y0 * recipeMatrixHom (Ω := GGL) σ ε (ψ := ψ) g0 * y0⁻¹
  have hR0' : R0 * aΩ * R0⁻¹ = aΩ⁻¹ := by
    simpa [R0, aΩ] using hR0
  have hMg0base : baseChangeGL (τ := Tag.E6) κ
      (originalM (K := K) (F := F) (σ := σ) (ε := ε) (ψ := ψ) ιK t g0) = R0 := by
    rw [hmodelJ g0]
  have hg : originalM (K := K) (F := F) (σ := σ) (ε := ε) (ψ := ψ) ιK t g0 *
      (aF : ModGL Tag.E6 F) *
      (originalM (K := K) (F := F) (σ := σ) (ε := ε) (ψ := ψ) ιK t g0)⁻¹ =
        (aF : ModGL Tag.E6 F)⁻¹ := by
    apply baseChangeGL_injective (τ := Tag.E6) κ
    rw [map_mul, map_mul, map_inv, hMg0base]
    simpa [haFbase] using hR0'
  have hconjγ := SCFourCover.recipeActorModelEquiv_conj
    (A := A) (g := g0) (Ω := GGL)
    hn hK σ hσ Fr hFr ε hε hψ hker hperf hAI hg0N τ
  have hconjγ_frame : y0 * (recipeActorModelEquiv (A := A) hn hK σ hσ Fr hFr ε hε
      hψ hker hperf hAI (ggConjAut A hg0N τ) : ModGL Tag.E6 GGL) * y0⁻¹ =
        R0 * aΩ * R0⁻¹ := by
    rw [hconjγ]
    rw [← hτframe]
    simp [R0, MulAut.conj_apply]
    group
  have hτinv_frame : y0 * (recipeActorModelEquiv (A := A) hn hK σ hσ Fr hFr ε hε
      hψ hker hperf hAI (τ⁻¹) : ModGL Tag.E6 GGL) * y0⁻¹ = aΩ⁻¹ := by
    have hγinv : (recipeActorModelEquiv (A := A) hn hK σ hσ Fr hFr ε hε
        hψ hker hperf hAI (τ⁻¹) : ModGL Tag.E6 GGL) =
          ((recipeActorModelEquiv (A := A) hn hK σ hσ Fr hFr ε hε
            hψ hker hperf hAI τ : ModGL Tag.E6 GGL))⁻¹ := by
      simpa using map_inv (recipeActorModelEquiv (A := A) hn hK σ hσ Fr hFr ε hε
        hψ hker hperf hAI).toMonoidHom τ
    rw [hγinv, ← hτframe]
    group
  have hγconj_eq : (recipeActorModelEquiv (A := A) hn hK σ hσ Fr hFr ε hε
      hψ hker hperf hAI (ggConjAut A hg0N τ) : ModGL Tag.E6 GGL) =
        (recipeActorModelEquiv (A := A) hn hK σ hσ Fr hFr ε hε
          hψ hker hperf hAI (τ⁻¹) : ModGL Tag.E6 GGL) := by
    apply (MulAut.conj y0).injective
    rw [MulAut.conj_apply, MulAut.conj_apply]
    calc
      y0 * (recipeActorModelEquiv (A := A) hn hK σ hσ Fr hFr ε hε
          hψ hker hperf hAI (ggConjAut A hg0N τ) : ModGL Tag.E6 GGL) * y0⁻¹ =
          R0 * aΩ * R0⁻¹ := hconjγ_frame
      _ = aΩ⁻¹ := hR0'
      _ = y0 * (recipeActorModelEquiv (A := A) hn hK σ hσ Fr hFr ε hε
          hψ hker hperf hAI (τ⁻¹) : ModGL Tag.E6 GGL) * y0⁻¹ := hτinv_frame.symm
  have hconjEqA : ggConjAut A hg0N τ = τ⁻¹ :=
    (recipeActorModelEquiv (A := A) hn hK σ hσ Fr hFr ε hε hψ hker hperf hAI).injective
      (Subtype.ext hγconj_eq)
  have hinv : MulAut.conj g0 * (τ : MulAut ↥J) * (MulAut.conj g0)⁻¹ =
      (τ : MulAut ↥J)⁻¹ := by
    calc
      MulAut.conj g0 * (τ : MulAut ↥J) * (MulAut.conj g0)⁻¹ =
          ((ggConjAut A hg0N τ : A) : MulAut ↥J) := (ggConjAut_apply A hg0N τ).symm
      _ = ((τ⁻¹ : A) : MulAut ↥J) := by rw [hconjEqA]
      _ = (τ : MulAut ↥J)⁻¹ := rfl
  obtain ⟨c, hc3, hcne, hconjc, hMc, hcov⟩ :=
    E4bOriginalLift.exists_originalCube_inducing_inverted_actor
      (K := K) (F := F) (σ := σ) (ε := ε) (ψ := ψ) (ι := ιK) (t := t)
      hn hK hσ hψ hker hperf hcard4 h3 hζF3 hωF3 hωF1
      (τ : MulAut ↥J) hτ3 g0 hinv hτg hg (Ω := GGL) κ σF hσF
  have hMcbase : baseChangeGL (τ := Tag.E6) κ
      (originalM (K := K) (F := F) (σ := σ) (ε := ε) (ψ := ψ) ιK t c) = aΩ := by
    rw [hMc]
    exact haFbase
  have hcRecipe : y0 * recipeMatrixHom (Ω := GGL) σ ε (ψ := ψ) c * y0⁻¹ = aΩ := by
    have h := hmodelJ c
    rw [hMcbase] at h
    exact h.symm
  have hfix_b : ∀ b : Bs, ggGamma J hN b c = c := by
    intro b
    let ab : A := ⟨ggGamma J hN b, ⟨b, rfl⟩⟩
    obtain ⟨φ, hφI, hφ⟩ := hAI ab.1 ab.2
    have hψv : ∀ j : ↥J, ψ (ab.1 j) = φ (ψ j) := fun j => (hφ j).symm
    have hXmodel : ∀ j : ↥J,
        originalM (K := K) (F := F) (σ := σ) (ε := ε) (ψ := ψ) ιK t (ab.1 j) =
          (eF ab : ModGL Tag.E6 F) *
            originalM (K := K) (F := F) (σ := σ) (ε := ε) (ψ := ψ) ιK t j *
            (eF ab : ModGL Tag.E6 F)⁻¹ := fun j => hmodel ab j
    have hX_E' : baseChangeGL (τ := Tag.E6) κ ((eF ab : ModGL Tag.E6 F)) ∈ E' := by
      rw [heF ab]
      refine Subgroup.mem_map.mpr ⟨(recipeActorModelEquiv (A := A) hn hK σ hσ Fr hFr ε
        hε hψ hker hperf hAI ab : ModGL Tag.E6 GGL), ?_, ?_⟩
      · exact (recipeActorModelEquiv (A := A) hn hK σ hσ Fr hFr ε hε hψ hker hperf hAI ab).2
      · simp [MulAut.conj_apply]
    have hXnorm : baseChangeGL (τ := Tag.E6) κ ((eF ab : ModGL Tag.E6 F)) ∈
        Subgroup.normalizer (fixedA2Torus GGL) := by
      have hE'N : E' ≤ Subgroup.normalizer (fixedA2Torus GGL) := by
        have hSleCent : E' ≤ Subgroup.centralizer
            (closedIdentityComponent (adjointGroup Tag.E6 GGL ⊓
              Subgroup.centralizer (E' : Set (ModGL Tag.E6 GGL))) : Set (ModGL Tag.E6 GGL)) := by
          intro x hx
          rw [Subgroup.mem_centralizer_iff]
          intro s hs
          have hsC : s ∈ Subgroup.centralizer (E' : Set (ModGL Tag.E6 GGL)) :=
            ((closedIdentityComponent_le (adjointGroup Tag.E6 GGL ⊓
              Subgroup.centralizer (E' : Set (ModGL Tag.E6 GGL)))).trans inf_le_right) hs
          exact (Subgroup.mem_centralizer_iff.mp hsC x hx).symm
        intro x hx
        have hxN : x ∈ Subgroup.normalizer
            (closedIdentityComponent (adjointGroup Tag.E6 GGL ⊓
              Subgroup.centralizer (E' : Set (ModGL Tag.E6 GGL))) : Set (ModGL Tag.E6 GGL)) :=
          Subgroup.centralizer_le_normalizer _ (hSleCent hx)
        rwa [hS'] at hxN
      exact hE'N hX_E'
    have hcomm : (eF ab : ModGL Tag.E6 F) * (aF : ModGL Tag.E6 F) =
        (aF : ModGL Tag.E6 F) * (eF ab : ModGL Tag.E6 F) := by
      have hAab : ab * τ = τ * ab := hAcomm ab τ
      have h := congrArg (fun x : A => (eF x : ModGL Tag.E6 F)) hAab
      simpa [map_mul, heFτ] using h
    have hXaF : (eF ab : ModGL Tag.E6 F) * (aF : ModGL Tag.E6 F) *
        (eF ab : ModGL Tag.E6 F)⁻¹ = (aF : ModGL Tag.E6 F) ^ (1 : ℤ) := by
      rw [zpow_one]
      calc
        (eF ab : ModGL Tag.E6 F) * (aF : ModGL Tag.E6 F) * (eF ab : ModGL Tag.E6 F)⁻¹ =
            (aF : ModGL Tag.E6 F) * (eF ab : ModGL Tag.E6 F) * (eF ab : ModGL Tag.E6 F)⁻¹ := by
          rw [hcomm]
        _ = (aF : ModGL Tag.E6 F) := by group
    have hXaF_adj : eF ab * aF * (eF ab)⁻¹ = aF ^ (1 : ℤ) := by
      apply Subtype.ext
      change (eF ab : ModGL Tag.E6 F) * (aF : ModGL Tag.E6 F) *
        (eF ab : ModGL Tag.E6 F)⁻¹ = (aF : ModGL Tag.E6 F) ^ (1 : ℤ)
      exact hXaF
    have h := hcov ab.1 φ hψv (eF ab) hXmodel hXnorm 1 hXaF_adj
    simpa [ab] using h
  have hcCent : ((c : G) ∈ Subgroup.centralizer (Bs : Set G)) := by
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    have hfix := hfix_b ⟨b, hb⟩
    have hcoe := congrArg (fun x : ↥J => (x : G)) hfix
    have hgg := ggGamma_coe (L := J) (hBN := hN) (b := ⟨b, hb⟩) c
    rw [hgg] at hcoe
    have hbc : (b : G) * (c : G) = (c : G) * (b : G) := by
      calc (b : G) * (c : G) = ((b : G) * (c : G) * (b : G)⁻¹) * (b : G) := by group
        _ = (c : G) * (b : G) := by rw [hcoe]
    exact hbc
  have hc3G : (c : G) ^ 3 = 1 := by
    simpa using congrArg (fun x : ↥J => (x : G)) hc3
  have hcBs : (c : G) ∈ Bs := hBs.2.2.2 (c : G) hcCent hc3G
  refine ⟨c, hc3, hcne, hcBs, hcRecipe, ?_⟩
  intro g hgN m hscalar
  have hMgGad : originalM (K := K) (F := F) (σ := σ) (ε := ε) (ψ := ψ) ιK t g ∈
      adjointGroup Tag.E6 F :=
    originalM_mem_adjointGroup (K := K) (F := F) (σ := σ) (ε := ε) (ψ := ψ) ιK t g
  let X : adjointGroup Tag.E6 F :=
    ⟨originalM (K := K) (F := F) (σ := σ) (ε := ε) (ψ := ψ) ιK t g, hMgGad⟩
  have hXbase : baseChangeGL (τ := Tag.E6) κ (X : ModGL Tag.E6 F) =
      y0 * recipeMatrixHom (Ω := GGL) σ ε (ψ := ψ) g * y0⁻¹ := by
    change baseChangeGL (τ := Tag.E6) κ
      (originalM (K := K) (F := F) (σ := σ) (ε := ε) (ψ := ψ) ιK t g) = _
    exact hmodelJ g
  have hψv : ∀ j : ↥J, ψ (MulAut.conj g j) = MulAut.conj (ψ g) (ψ j) := by
    intro j
    simp [MulAut.conj_apply]
  have hXmodel : ∀ j : ↥J,
      originalM (K := K) (F := F) (σ := σ) (ε := ε) (ψ := ψ) ιK t (MulAut.conj g j) =
        (X : ModGL Tag.E6 F) *
          originalM (K := K) (F := F) (σ := σ) (ε := ε) (ψ := ψ) ιK t j *
          (X : ModGL Tag.E6 F)⁻¹ := by
    intro j
    change originalM (K := K) (F := F) (σ := σ) (ε := ε) (ψ := ψ) ιK t (g * j * g⁻¹) =
      originalM (K := K) (F := F) (σ := σ) (ε := ε) (ψ := ψ) ιK t g *
        originalM (K := K) (F := F) (σ := σ) (ε := ε) (ψ := ψ) ιK t j *
        (originalM (K := K) (F := F) (σ := σ) (ε := ε) (ψ := ψ) ιK t g)⁻¹
    simp only [map_mul, map_inv]
  have hXaF : (X : ModGL Tag.E6 F) * (aF : ModGL Tag.E6 F) * (X : ModGL Tag.E6 F)⁻¹ =
      (aF : ModGL Tag.E6 F) ^ m := by
    apply baseChangeGL_injective (τ := Tag.E6) κ
    rw [map_mul, map_mul, map_inv, hXbase, map_zpow, haFbase]
    exact hscalar
  have hXaF_adj : X * aF * X⁻¹ = aF ^ m := by
    apply Subtype.ext
    change (X : ModGL Tag.E6 F) * (aF : ModGL Tag.E6 F) * (X : ModGL Tag.E6 F)⁻¹ =
      (aF : ModGL Tag.E6 F) ^ m
    exact hXaF
  have hXnorm : baseChangeGL (τ := Tag.E6) κ (X : ModGL Tag.E6 F) ∈
      Subgroup.normalizer (fixedA2Torus GGL) := by
    have hRgNE' : (y0 * recipeMatrixHom (Ω := GGL) σ ε (ψ := ψ) g * y0⁻¹) ∈
        Subgroup.normalizer (E' : Set (ModGL Tag.E6 GGL)) := by
      simpa [E'] using
        framed_recipe_normalizes_originalEFrame (J := ↥J)
          hn hK hσ Fr hFr ε hε hψ hker hperf hAI hgN (y0 := y0)
    have hRgN_S : (y0 * recipeMatrixHom (Ω := GGL) σ ε (ψ := ψ) g * y0⁻¹) ∈
        Subgroup.normalizer (fixedA2Torus GGL) :=
      framed_recipe_normalizes_fixedA2Torus (J := ↥J)
        hn hK hσ Fr hFr ε hε hψ hker hperf hAI hgN hy0
        (by simpa [E'] using hS')
    simpa [hXbase] using hRgN_S
  have h := hcov (MulAut.conj g) (MulAut.conj (ψ g)) hψv X hXmodel hXnorm m hXaF_adj
  exact h

end CFSG.StandardType.E4bOriginalSC

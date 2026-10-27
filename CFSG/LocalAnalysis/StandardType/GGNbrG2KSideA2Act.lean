module

public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67A2Hom
public import CFSG.RankThree.PartTwo.KFacts.AutG2
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ParabCommGTwoChev
public import CFSG.LocalAnalysis.AGLEmbedding.D1GlobalU
public import CFSG.LocalAnalysis.AGLEmbedding.LeviBlockGTwoData
public import CFSG.LocalAnalysis.AGLEmbedding.LeviBlockGTwoNode
public import CFSG.LocalAnalysis.AGLEmbedding.Reduction
public import CFSG.LocalAnalysis.AGLEmbedding.TwoCoreObstruction
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore

public section

namespace CFSG.StandardType

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.PartTwo.KFacts

local notation "RA2" => CFSG.LieType.RootSystem.roots
  (CFSG.LieType.Universal.SpecialLinear.isFiniteType_A 2) (∅ : Set (Fin 2))

private def rootClosure (F : Type) [Field F] :
    Subgroup (Matrix.SpecialLinearGroup (Fin 3) F) :=
  Subgroup.closure (⋃ γ ∈ RA2, Set.range (CFSG.LieType.Steinberg.SL.x 2 F γ))

private lemma x_mem_rootClosure {F : Type} [Field F] {γ : Fin 2 → ℤ} (hγ : γ ∈ RA2) (c : F) :
    CFSG.LieType.Steinberg.SL.x 2 F γ c ∈ rootClosure F := by
  refine Subgroup.subset_closure ?_
  simp only [Set.mem_iUnion, Set.mem_range]
  exact ⟨γ, hγ, c, rfl⟩

private lemma transvection_mem_rootClosure {F : Type} [Field F] {i j : Fin 3}
    (hij : i ≠ j) (c : F) :
    Matrix.SpecialLinearGroup.transvection hij c ∈ rootClosure F := by
  fin_cases i <;> fin_cases j
  · exact absurd rfl hij
  · have hγ : (![1, 0] : Fin 2 → ℤ) ∈ RA2 := by
      rw [CFSG.GH74.GLS.Stage2.Bender.Thm1.mem_RA2_iff]; decide
    rw [← CFSG.LieType.Steinberg.SL.x_eq (m := 2) (F := F)
      (γ := (![1, 0] : Fin 2 → ℤ)) hij (by decide) c]
    exact x_mem_rootClosure hγ c
  · have hγ : (![1, 1] : Fin 2 → ℤ) ∈ RA2 := by
      rw [CFSG.GH74.GLS.Stage2.Bender.Thm1.mem_RA2_iff]; decide
    rw [← CFSG.LieType.Steinberg.SL.x_eq (m := 2) (F := F)
      (γ := (![1, 1] : Fin 2 → ℤ)) hij (by decide) c]
    exact x_mem_rootClosure hγ c
  · have hγ : (![-1, 0] : Fin 2 → ℤ) ∈ RA2 := by
      rw [CFSG.GH74.GLS.Stage2.Bender.Thm1.mem_RA2_iff]; decide
    rw [← CFSG.LieType.Steinberg.SL.x_eq (m := 2) (F := F)
      (γ := (![-1, 0] : Fin 2 → ℤ)) hij (by decide) c]
    exact x_mem_rootClosure hγ c
  · exact absurd rfl hij
  · have hγ : (![0, 1] : Fin 2 → ℤ) ∈ RA2 := by
      rw [CFSG.GH74.GLS.Stage2.Bender.Thm1.mem_RA2_iff]; decide
    rw [← CFSG.LieType.Steinberg.SL.x_eq (m := 2) (F := F)
      (γ := (![0, 1] : Fin 2 → ℤ)) hij (by decide) c]
    exact x_mem_rootClosure hγ c
  · have hγ : (![-1, -1] : Fin 2 → ℤ) ∈ RA2 := by
      rw [CFSG.GH74.GLS.Stage2.Bender.Thm1.mem_RA2_iff]; decide
    rw [← CFSG.LieType.Steinberg.SL.x_eq (m := 2) (F := F)
      (γ := (![-1, -1] : Fin 2 → ℤ)) hij (by decide) c]
    exact x_mem_rootClosure hγ c
  · have hγ : (![0, -1] : Fin 2 → ℤ) ∈ RA2 := by
      rw [CFSG.GH74.GLS.Stage2.Bender.Thm1.mem_RA2_iff]; decide
    rw [← CFSG.LieType.Steinberg.SL.x_eq (m := 2) (F := F)
      (γ := (![0, -1] : Fin 2 → ℤ)) hij (by decide) c]
    exact x_mem_rootClosure hγ c
  · exact absurd rfl hij

private lemma rootClosure_eq_top (F : Type) [Field F] : rootClosure F = ⊤ := by
  rw [eq_top_iff, ← Matrix.SpecialLinearGroup.closure_range_toSpecialLinearGroup_eq_top_of_field
    (ι := Fin 3) (K := F), Subgroup.closure_le]
  rintro _ ⟨⟨i, j, hij, c⟩, rfl⟩
  show Matrix.SpecialLinearGroup.transvection hij c ∈ rootClosure F
  exact transvection_mem_rootClosure hij c

private lemma map_x (F : Type) [Field F] (σ : F ≃+* F) {γ : Fin 2 → ℤ} (hγ : γ ∈ RA2) (c : F) :
    Matrix.SpecialLinearGroup.map σ.toRingHom (CFSG.LieType.Steinberg.SL.x 2 F γ c) =
      CFSG.LieType.Steinberg.SL.x 2 F γ (σ c) := by
  obtain ⟨hij, hst⟩ := CFSG.LieType.Steinberg.SL.pairOf_spec hγ
  rw [CFSG.LieType.Steinberg.SL.x_eq hij hst c,
    CFSG.LieType.Steinberg.SL.x_eq hij hst (σ c)]
  exact Matrix.SpecialLinearGroup.map_transvection σ.toRingHom hij c

private lemma fieldHom_a2y
    (F : Type) [Field F] (σ : F ≃+* F) (γ : Fin 2 → ℤ) (c : F) :
    g2FieldHom F σ (CFSG.GH74.GLS.Stage2.Bender.Thm1.a2y γ c) =
      CFSG.GH74.GLS.Stage2.Bender.Thm1.a2y γ (σ c) := by
  unfold CFSG.GH74.GLS.Stage2.Bender.Thm1.a2y
  exact CFSG.LocalAnalysis.RankThreeTheoremC.TenThreeThree.ParabComm.GTwo.g2FieldHom_xPar
    (K := F) σ (CFSG.LieType.Steinberg.RankTwo.g2CommRoot
      (CFSG.GH74.GLS.Stage2.Bender.Thm1.a2pos (γ 0, γ 1))) c

theorem ggNbrG2K_a2_fieldHom
    {F : Type} [Field F]
    (φ : Matrix.SpecialLinearGroup (Fin 3) F →* adjointGroup Tag.G2 F)
    (hφ : ∀ γ ∈ RA2, ∀ c : F, φ (CFSG.LieType.Steinberg.SL.x 2 F γ c) =
      CFSG.GH74.GLS.Stage2.Bender.Thm1.a2y γ c)
    (σ : F ≃+* F) (g : Matrix.SpecialLinearGroup (Fin 3) F) :
    g2FieldHom F σ (φ g) = φ (Matrix.SpecialLinearGroup.map σ.toRingHom g) := by
  let ψ₁ : Matrix.SpecialLinearGroup (Fin 3) F →* adjointGroup Tag.G2 F :=
    (g2FieldHom F σ).toMonoidHom.comp φ
  let ψ₂ : Matrix.SpecialLinearGroup (Fin 3) F →* adjointGroup Tag.G2 F :=
    φ.comp (Matrix.SpecialLinearGroup.map σ.toRingHom)
  change ψ₁ g = ψ₂ g
  have hgen : rootClosure F = ⊤ := rootClosure_eq_top F
  have hle : rootClosure F ≤ MonoidHom.eqLocus ψ₁ ψ₂ := by
    change Subgroup.closure (⋃ γ ∈ RA2, Set.range (CFSG.LieType.Steinberg.SL.x 2 F γ)) ≤
      MonoidHom.eqLocus ψ₁ ψ₂
    rw [Subgroup.closure_le]
    rintro x hx
    simp only [Set.mem_iUnion, Set.mem_range] at hx
    obtain ⟨γ, hγ, c, rfl⟩ := hx
    change ψ₁ (CFSG.LieType.Steinberg.SL.x 2 F γ c) =
      ψ₂ (CFSG.LieType.Steinberg.SL.x 2 F γ c)
    have h1 : ψ₁ (CFSG.LieType.Steinberg.SL.x 2 F γ c) =
        CFSG.GH74.GLS.Stage2.Bender.Thm1.a2y γ (σ c) := by
      simp only [ψ₁, MonoidHom.comp_apply]
      rw [hφ γ hγ c]
      change g2FieldHom F σ (CFSG.GH74.GLS.Stage2.Bender.Thm1.a2y γ c) =
        CFSG.GH74.GLS.Stage2.Bender.Thm1.a2y γ (σ c)
      rw [fieldHom_a2y F σ γ c]
    have h2 : ψ₂ (CFSG.LieType.Steinberg.SL.x 2 F γ c) =
        CFSG.GH74.GLS.Stage2.Bender.Thm1.a2y γ (σ c) := by
      simp only [ψ₂, MonoidHom.comp_apply]
      rw [map_x F σ hγ c, hφ γ hγ (σ c)]
    rw [h1, h2]
  have hx : g ∈ MonoidHom.eqLocus ψ₁ ψ₂ := by
    rw [hgen] at hle
    exact hle (Subgroup.mem_top g)
  exact hx

end CFSG.StandardType

end

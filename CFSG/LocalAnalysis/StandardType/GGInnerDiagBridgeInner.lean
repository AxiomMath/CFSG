module

public import CFSG.LocalAnalysis.StandardType.GGInnerDiagBridgeTypeA

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank

@[expose] def GGInnerTag (t : StatedLieTag) : Prop :=
  t = .PSp ∨ t = .POmegaPlus ∨ t = .POmegaMinus ∨ t = .F4 ∨ t = .E7 ∨ t = .E8

section Recipes

theorem spForm_of_mem_spGroup {K : Type} [Field K] {m : ℕ} {g : GL (Fin m ⊕ Fin m) K}
    (hg : g ∈ LargeEvenSpGroup K m) :
    Matrix.transpose (g : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) * LargeEvenSpForm K m *
      (g : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) = LargeEvenSpForm K m := by
  induction hg using Subgroup.closure_induction with
  | mem x hx => exact hx
  | one => simp
  | mul x y _ _ hx hy =>
    calc Matrix.transpose ((x * y : GL (Fin m ⊕ Fin m) K) : Matrix _ _ K) * LargeEvenSpForm K m *
          ((x * y : GL (Fin m ⊕ Fin m) K) : Matrix _ _ K)
        = Matrix.transpose (y : Matrix _ _ K) *
            (Matrix.transpose (x : Matrix _ _ K) * LargeEvenSpForm K m * (x : Matrix _ _ K)) *
              (y : Matrix _ _ K) := by
          rw [Units.val_mul, Matrix.transpose_mul]
          simp only [Matrix.mul_assoc]
      _ = LargeEvenSpForm K m := by rw [hx, hy]
  | inv x _ hx =>
    have h1 : (x : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *
        ((x⁻¹ : GL (Fin m ⊕ Fin m) K) : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) = 1 := by
      rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
    calc Matrix.transpose ((x⁻¹ : GL (Fin m ⊕ Fin m) K) : Matrix _ _ K) * LargeEvenSpForm K m *
          ((x⁻¹ : GL (Fin m ⊕ Fin m) K) : Matrix _ _ K)
        = Matrix.transpose ((x⁻¹ : GL (Fin m ⊕ Fin m) K) : Matrix _ _ K) *
            (Matrix.transpose (x : Matrix _ _ K) * LargeEvenSpForm K m * (x : Matrix _ _ K)) *
              ((x⁻¹ : GL (Fin m ⊕ Fin m) K) : Matrix _ _ K) := by rw [hx]
      _ = Matrix.transpose ((x : Matrix _ _ K) * ((x⁻¹ : GL (Fin m ⊕ Fin m) K) : Matrix _ _ K)) *
            LargeEvenSpForm K m *
              ((x : Matrix _ _ K) * ((x⁻¹ : GL (Fin m ⊕ Fin m) K) : Matrix _ _ K)) := by
          rw [Matrix.transpose_mul]
          simp only [Matrix.mul_assoc]
      _ = LargeEvenSpForm K m := by rw [h1, Matrix.transpose_one, Matrix.one_mul, Matrix.mul_one]

theorem innSet_subset_symplectic {K : Type} [Field K] (m : ℕ) :
    LargeEvenInnSet (LargeEvenProj (LargeEvenSpGroup K m)) ⊆
      LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSpGroup K m)) (LargeEvenGSpSet K m) := by
  rintro _ ⟨r, rfl⟩
  obtain ⟨h₀, rfl⟩ := QuotientGroup.mk_surjective r
  refine ⟨h₀, ⟨1, one_ne_zero, by rw [one_smul]; exact spForm_of_mem_spGroup h₀.2⟩,
    fun h h' hh' => ?_⟩
  show (h₀ : LargeEvenProj (LargeEvenSpGroup K m)) * (h : LargeEvenProj (LargeEvenSpGroup K m)) *
      (h₀ : LargeEvenProj (LargeEvenSpGroup K m))⁻¹ = (h' : LargeEvenProj (LargeEvenSpGroup K m))
  rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul]
  congr 1
  exact Subtype.ext (by rw [hh']; rfl)

theorem recipeSymplectic_inn {m q : ℕ} {Q : LargeEvenRawCont}
    (h : LargeEvenRecipeSymplectic m q false Q) :
    LargeEvenRecipeSymplectic m q false fun R _ I F => Q R I F ∧ LargeEvenInnSet R ⊆ I := by
  obtain ⟨K, _, _, hK, hQ⟩ := h
  exact ⟨K, inferInstance, inferInstance, hK, hQ, innSet_subset_symplectic m⟩

theorem recipeOmegaPlus_inn {m q : ℕ} {Q : LargeEvenRawCont}
    (h : LargeEvenRecipeOmegaPlus m q Q) :
    LargeEvenRecipeOmegaPlus m q fun R _ I F => Q R I F ∧ LargeEvenInnSet R ⊆ I := by
  obtain ⟨K, _, _, hK, hQ⟩ := h
  exact ⟨K, inferInstance, inferInstance, hK, hQ, subset_rfl⟩

theorem recipeOmegaMinus_inn {m q : ℕ} {Q : LargeEvenRawCont}
    (h : LargeEvenRecipeOmegaMinus m q Q) :
    LargeEvenRecipeOmegaMinus m q fun R _ I F => Q R I F ∧ LargeEvenInnSet R ⊆ I := by
  obtain ⟨K, _, _, hK, b, c, hbc, hQ⟩ := h
  exact ⟨K, inferInstance, inferInstance, hK, b, c, hbc, hQ, subset_rfl⟩

theorem recipeChevalley_inn {r : ℕ} {A : Matrix (Fin r) (Fin r) ℤ} {q : ℕ} {derived : Bool}
    {Q : LargeEvenRawCont} (h : LargeEvenRecipeChevalley A q derived Q) :
    LargeEvenRecipeChevalley A q derived fun R _ I F => Q R I F ∧ LargeEvenInnSet R ⊆ I := by
  obtain ⟨K, _, _, hK, hQ⟩ := h
  exact ⟨K, inferInstance, inferInstance, hK, hQ,
    fun φ hφ => Subgroup.subset_closure (Set.mem_union_left _ hφ)⟩

theorem largeEvenRawDatum_inn {lab : LargeEvenLabel} {Q : LargeEvenRawCont}
    (ht : GGInnerTag (markTag lab)) (h : LargeEvenRawDatum lab Q) :
    LargeEvenRawDatum lab fun R _ I F => Q R I F ∧ LargeEvenInnSet R ⊆ I := by
  obtain ⟨tg, l, n⟩ := lab
  have hf : ¬ GGInnerTag .PSL ∧ ¬ GGInnerTag .PSU ∧ ¬ GGInnerTag .E6 ∧
      ¬ GGInnerTag .twistedE6 ∧ ¬ GGInnerTag .trialityD4 ∧ ¬ GGInnerTag .G2 ∧
      ¬ GGInnerTag .twistedB2 ∧ ¬ GGInnerTag .twistedF4 ∧ ¬ GGInnerTag .Tits := by
    simp [GGInnerTag]
  cases tg with
  | A => exact absurd ht hf.1
  | twA => exact absurd ht hf.2.1
  | B => exact recipeSymplectic_inn h
  | C => exact recipeSymplectic_inn h
  | D =>
    by_cases hl : l = 3
    · exact absurd (by simpa [markTag, hl] using ht) hf.1
    · have h' : LargeEvenRecipeOmegaPlus l (2 ^ n) Q := by
        simpa only [LargeEvenRawDatum, hl, ↓reduceIte] using h
      show if l = 3 then _ else _
      simp only [hl, ↓reduceIte]
      exact recipeOmegaPlus_inn h'
  | twD =>
    by_cases hl2 : l = 2
    · exact absurd (by simpa [markTag, hl2] using ht) hf.1
    by_cases hl3 : l = 3
    · exact absurd (by simpa [markTag, hl3] using ht) hf.2.1
    · have h' : LargeEvenRecipeOmegaMinus (l - 1) (2 ^ n) Q := by
        simpa only [LargeEvenRawDatum, hl2, hl3, ↓reduceIte] using h
      show if l = 2 then _ else if l = 3 then _ else _
      simp only [hl2, hl3, ↓reduceIte]
      exact recipeOmegaMinus_inn h'
  | E6 => exact absurd ht hf.2.2.1
  | E7 => exact recipeChevalley_inn h
  | E8 => exact recipeChevalley_inn h
  | F4 => exact recipeChevalley_inn h
  | twE6 => exact absurd ht hf.2.2.2.1
  | triD4 => exact absurd ht hf.2.2.2.2.1
  | G2 => exact absurd ht hf.2.2.2.2.2.1
  | twB2 => exact absurd ht hf.2.2.2.2.2.2.1
  | twF4 => exact absurd ht hf.2.2.2.2.2.2.2.1
  | B2der => exact absurd ht hf.1
  | G2der => exact absurd ht hf.2.1
  | twF4der => exact absurd ht hf.2.2.2.2.2.2.2.2

end Recipes

section Genuine

@[expose] def GGPsiDiagInnerAt (t : StatedLieTag) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (n f : ℕ) (ψ : (ggU t n f).K →* G) (G₀ : Subgroup G),
    GGPresentsG0 G₀ (ggU t n f).D t n f ψ → ∀ c ∈ Subgroup.normalizer (G₀ : Set G),
      GGPsiInnerDiag (ggU t n f).D ψ c → ∃ g ∈ G₀, c * g ∈ Subgroup.centralizer (G₀ : Set G)

end Genuine

section Reduction

theorem ggInnerDiagMarkingAt_of_diagInner {t : StatedLieTag} (ht : GGInnerTag t)
    (hD : GGPsiDiagInnerAt t) : GGInnerDiagMarkingAt t := by
  intro G _ _ n f ψ G₀ hpres
  obtain ⟨hperf, lab, hlab, hraw⟩ :=
    largeEvenMarking_of_lieModel_centerQuot hpres.2.2.1 hpres.2.2.2
  obtain ⟨-, -, -, -, -, -, -, hmt, -⟩ := largeEvenRawDatum_exists hraw
  refine ⟨hperf, lab, hlab, largeEvenRawDatum_mono ?_ (largeEvenRawDatum_inn (hmt ▸ ht) hraw)⟩
  rintro R _ I F ⟨⟨hs, hna, θ, -⟩, hInn⟩
  refine ⟨hs, hna, θ, fun c hc hdiag => ?_⟩
  obtain ⟨g, hg, hcg⟩ := hD G n f ψ G₀ hpres c hc hdiag
  refine ⟨MulAut.conj (θ (QuotientGroup.mk ⟨g, hg⟩)), hInn ⟨_, rfl⟩, fun l l' hl => ?_⟩
  have hl' : l' = ⟨g, hg⟩ * l * (⟨g, hg⟩ : ↥G₀)⁻¹ := by
    apply Subtype.ext
    rw [hl]
    have hcomm := Subgroup.mem_centralizer_iff.mp hcg l l.2
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    calc c⁻¹ * (l : G) * c = c⁻¹ * ((l : G) * (c * g)) * g⁻¹ := by group
      _ = c⁻¹ * ((c * g) * l) * g⁻¹ := by rw [hcomm]
      _ = g * l * g⁻¹ := by group
  rw [hl', MulAut.conj_apply, QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv,
    map_mul, map_mul, map_inv]

end Reduction

section Assembly

theorem lc_gl_std_of_v2_steps_inner
    (hHolt : CFSG.RankThree.PartTwo.Sec21.HoltUniqueFixedPointSimple)
    (ha : GGBstarInput) (ha₀ : GGLNoncyclicInput) (hb : GGStdSubPreInput)
    (hc₀ : GGFieldNbrCanonicalInput) (hc₁ : GGProp41Input) (hc₂ : GGCor42Input)
    (hc₃ : GGNoTransvectionInput) (hd : GGCoxeterLabelInput) (he : GGPropFiveTwentyOneV2Input)
    (hf : GGHypSixV2Input) (hg₁ : GGCorFiveTwentyInput) (hg₂ : GGOmegaOneInput)
    (hD : ∀ t, GGInnerTag t → GGPsiDiagInnerAt t)
    (hR : ∀ t, (t = .PSU ∨ t = .E6 ∨ t = .twistedE6) → GGInnerDiagMarkingAt t)
    (h1 : GGSixStepOneV2Input) (h2 : GGSixStepTwoV2Input) (h3a : GGSixStepThreeAInput)
    (h3b : GGSixStepThreeBInput) (h3c : GGSixStepThreeCInput) (h3d : GGSixStepThreeDInput)
    (hKG : GGRootInvolutionCentralInput)
    (G : Type) [Group G] [Finite G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a) (hK : KProper InCatalog G) (hchar : IsCharTwoType G)
    (he4 : 4 ≤ evenRank G) (p : ℕ) (hp : p ∈ LargeEvenBeta 4 G) (B : Subgroup G) (x : G)
    (L : Subgroup G) (hS : LargeEvenSStar p B x L) (hst : LargeEvenStandardType p B x L) :
    InCatalog G := by
  have hI : ∀ t, GGInnerTag t → GGInnerDiagMarkingAt t := fun t ht =>
    ggInnerDiagMarkingAt_of_diagInner ht (hD t ht)
  refine lc_gl_std_of_v2_steps_typeA hHolt ha ha₀ hb hc₀ hc₁ hc₂ hc₃ hd he hf hg₁ hg₂
    (fun t ht => ?_) h1 h2 h3a h3b h3c h3d hKG G hnonab hK hchar he4 p hp B x L hS hst
  rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact hR _ (.inl rfl)
  · exact hI _ (.inl rfl)
  · exact hI _ (.inr (.inl rfl))
  · exact hI _ (.inr (.inr (.inl rfl)))
  · exact hI _ (.inr (.inr (.inr (.inl rfl))))
  · exact hR _ (.inr (.inl rfl))
  · exact hI _ (.inr (.inr (.inr (.inr (.inl rfl)))))
  · exact hI _ (.inr (.inr (.inr (.inr (.inr rfl)))))
  · exact hR _ (.inr (.inr rfl))

end Assembly

end CFSG.StandardType

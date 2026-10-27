module

public import CFSG.LocalAnalysis.StandardType.GGNbrLangRestRank
public import CFSG.LocalAnalysis.StandardType.GGCorFourTwoOpenVac
public import CFSG.LocalAnalysis.StandardType.GGRecipeFieldLinearLang
public import CFSG.LocalAnalysis.StandardType.GGRecipeFieldLinear
public import CFSG.LocalAnalysis.StandardType.GGRecipeFieldExc
public import CFSG.LocalAnalysis.StandardType.GGRecipeFieldSymplectic
public import CFSG.LocalAnalysis.StandardType.GGRecipeFieldSpUSpLabels
public import CFSG.LocalAnalysis.StandardType.GGRecipeFieldOmegaConjLabels

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

@[expose] def GGNbrLangFieldTwoLabel (lab : LargeEvenLabel) : Prop :=
  lab.n = 1 ∧ (lab.tag = .B ∨ lab.tag = .C ∨ (lab.tag = .D ∧ 4 ≤ lab.rank) ∨ lab.tag = .F4 ∨
    lab.tag = .E6 ∨ lab.tag = .E7 ∨ lab.tag = .E8 ∨ lab.tag = .B2der ∨ lab.tag = .G2der ∨
    lab.tag = .twF4der)

@[expose] def GGLinearCoprimeDegLabel (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  (lab.tag = .A ∨ (lab.tag = .D ∧ lab.rank = 3)) ∧ ¬ p ∣ lab.n

@[expose] def GGSpOmegaCoprimeDegLabel (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  (lab.tag = .B ∨ lab.tag = .C ∨ (lab.tag = .D ∧ 4 ≤ lab.rank)) ∧ ¬ p ∣ lab.n

namespace NbrLangRest

section Config

variable {G : Type} [Group G] [Finite G]

theorem ggLAut_pow_eq_one {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hC : GGConfig p B Bs x L D J) {K : Subgroup G} (hN : Bs ≤ Subgroup.normalizer (K : Set G))
    {R : Type} [Group R] (θ : K ⧸ Subgroup.center K ≃* R) {b₀ : G} (hb₀ : b₀ ∈ Bs) :
    ggLAut K θ ⟨b₀, hN hb₀⟩ ^ p = 1 := by
  have h1 : (⟨b₀, hN hb₀⟩ : Subgroup.normalizer (K : Set G)) ^ p = 1 :=
    Subtype.ext (by rw [Subgroup.coe_pow]; exact hC.2.1.2.1.2 b₀ hb₀)
  rw [← map_pow, h1, map_one]

end Config

theorem pow_eq_one_of_mem_field_linear {d m : ℕ} {K : Type} [Field K] [Finite K] (hm : 1 ≤ m)
    (hK : Nat.card K = 2 ^ m) {f : MulAut (LargeEvenProj (LargeEvenSLGroup (Fin d) K))}
    (hf : f ∈ LargeEvenMatFieldImage (LargeEvenProjMk (LargeEvenSLGroup (Fin d) K))) :
    f ^ m = 1 := by
  obtain ⟨σ, hσ⟩ := RecipeFieldLinear.congr_field_eq hf
  obtain ⟨-, -, -, -, hcard, -⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_automorphism_fixed_field_cardinality
      Nat.prime_two hm hK
  have hσm : σ ^ m = 1 := hcard ▸ pow_card_eq_one'
  apply (MulAut.congr (TypeA.recipeEquiv d K)).injective
  rw [map_pow, hσ, ← map_pow, hσm, map_one, map_one]

theorem recipeSymplectic_field_eq_one {m N : ℕ} (hN : N = 2) {derived : Bool}
    {Q : LargeEvenRawCont} (h : LargeEvenRecipeSymplectic m N derived Q) :
    LargeEvenRecipeSymplectic m N derived fun R _ I F => Q R I F ∧ ∀ f ∈ F, f = 1 := by
  obtain ⟨K, _, _, hK, hQ⟩ := h
  exact ⟨K, inferInstance, inferInstance, hK, hQ, fun f hf =>
    matFieldImage_eq_one_of_card_two (hK.trans hN) _ hf⟩

theorem recipeOmegaPlus_field_eq_one {m N : ℕ} (hN : N = 2) {Q : LargeEvenRawCont}
    (h : LargeEvenRecipeOmegaPlus m N Q) :
    LargeEvenRecipeOmegaPlus m N fun R _ I F => Q R I F ∧ ∀ f ∈ F, f = 1 := by
  obtain ⟨K, _, _, hK, hQ⟩ := h
  exact ⟨K, inferInstance, inferInstance, hK, hQ, fun f hf =>
    matFieldImage_eq_one_of_card_two (hK.trans hN) _ hf⟩

theorem recipeChevalley_field_eq_one {r : ℕ} {A : Matrix (Fin r) (Fin r) ℤ} {N : ℕ} (hN : N = 2)
    {derived : Bool} {Q : LargeEvenRawCont} (h : LargeEvenRecipeChevalley A N derived Q) :
    LargeEvenRecipeChevalley A N derived fun R _ I F => Q R I F ∧ ∀ f ∈ F, f = 1 := by
  obtain ⟨K, _, _, hK, hQ⟩ := h
  exact ⟨K, inferInstance, inferInstance, hK, hQ, fun f hf =>
    chevFieldImage_eq_one_of_card_two (hK.trans hN) _ hf⟩

theorem recipeTwF4_zero_field_eq_one {a : ℕ} (ha : a = 0) {Q : LargeEvenRawCont}
    (h : LargeEvenRecipeTwF4 a Q) :
    LargeEvenRecipeTwF4 a fun R _ I F => Q R I F ∧ ∀ f ∈ F, f = 1 := by
  subst ha
  obtain ⟨K, _, _, hK, hQ⟩ := h
  exact ⟨K, inferInstance, inferInstance, hK, hQ, fun f hf =>
    chevFieldImage_eq_one_of_card_two (by rw [hK]; norm_num) _ hf⟩

theorem largeEvenLabelAll_field_eq_one_two {lab : LargeEvenLabel}
    (h : GGNbrLangFieldTwoLabel lab) :
    LargeEvenLabelAll lab fun _ _ _ F => ∀ f ∈ F, f = 1 := by
  obtain ⟨t, l, n⟩ := lab
  obtain ⟨hn, ht⟩ := h
  dsimp only at hn ht
  subst hn
  intro Q hQ
  have h2 : 2 ^ 1 = 2 := pow_one 2
  rcases ht with rfl | rfl | ⟨rfl, hl⟩ | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recipeSymplectic_field_eq_one h2 hQ
  · exact recipeSymplectic_field_eq_one h2 hQ
  · dsimp only [LargeEvenRawDatum] at hQ ⊢
    split_ifs at hQ ⊢ with h3
    · omega
    · exact recipeOmegaPlus_field_eq_one h2 hQ
  · exact recipeChevalley_field_eq_one h2 hQ
  · exact recipeChevalley_field_eq_one h2 hQ
  · exact recipeChevalley_field_eq_one h2 hQ
  · exact recipeChevalley_field_eq_one h2 hQ
  · exact recipeSymplectic_field_eq_one rfl hQ
  · exact recipeChevalley_field_eq_one rfl hQ
  · exact recipeTwF4_zero_field_eq_one (by norm_num) hQ

theorem largeEvenLabelAll_field_pow_linear {lab : LargeEvenLabel} (hlab : LargeEvenInLambda2 lab)
    (h : lab.tag = .A ∨ (lab.tag = .D ∧ lab.rank = 3)) :
    LargeEvenLabelAll lab fun _ _ _ F => ∀ f ∈ F, f ^ lab.n = 1 := by
  obtain ⟨t, l, n⟩ := lab
  have hn : 1 ≤ n := hlab.1
  intro Q hQ
  rcases h with ht | ⟨ht, hl⟩ <;> dsimp only at ht <;> subst ht
  · dsimp only [LargeEvenRawDatum] at hQ ⊢
    exact NbrGraphLinear.recipeLinear_all (fun _ _ _ hK _ hf =>
      pow_eq_one_of_mem_field_linear hn hK hf) hQ
  · dsimp only at hl
    subst hl
    simp only [LargeEvenRawDatum, ↓reduceIte] at hQ ⊢
    exact NbrGraphLinear.recipeLinear_all (fun _ _ _ hK _ hf =>
      pow_eq_one_of_mem_field_linear hn hK hf) hQ

theorem pow_eq_one_of_mem_field_symplectic {m n : ℕ} {K : Type} [Field K] [Finite K] (hn : 1 ≤ n)
    (hK : Nat.card K = 2 ^ n) {f : MulAut (LargeEvenProj (LargeEvenSpGroup K m))}
    (hf : f ∈ LargeEvenMatFieldImage (LargeEvenProjMk (LargeEvenSpGroup K m))) : f ^ n = 1 := by
  obtain ⟨σ, rfl⟩ := RecipeFieldSp.exists_fieldAut_of_mem hf
  obtain ⟨-, -, -, -, hcard, -⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_automorphism_fixed_field_cardinality
      Nat.prime_two hn hK
  have hσn : σ ^ n = 1 := hcard ▸ pow_card_eq_one'
  have h1 : (CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher.fieldAut m K σ) ^ n = 1 := by
    rw [← map_pow, hσn, map_one]
  exact h1

theorem pow_eq_one_of_mem_field_omegaPlus {m n : ℕ} {K : Type} [Field K] [Finite K] (hm : 1 ≤ m)
    (hn : 1 ≤ n) (hK : Nat.card K = 2 ^ n)
    {f : MulAut (LargeEvenProj (LargeEvenOmega (LargeEvenQPlus K m)))}
    (hf : f ∈ LargeEvenMatFieldImage (LargeEvenProjMk (LargeEvenOmega (LargeEvenQPlus K m)))) :
    f ^ n = 1 := by
  have := charP_two_of_card hK
  obtain ⟨σ, hσ⟩ := RecipeFieldOmega.congr_plusEquiv_of_mem_field hm hf
  obtain ⟨-, -, -, -, hcard, -⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_automorphism_fixed_field_cardinality
      Nat.prime_two hn hK
  have hσn : σ ^ n = 1 := hcard ▸ pow_card_eq_one'
  apply (MulAut.congr (RecipeFieldOmega.plusEquiv (K := K) hm)).injective
  rw [map_pow, hσ, ← map_pow, hσn, map_one, map_one]

theorem largeEvenLabelAll_field_pow_spOmega {lab : LargeEvenLabel} (hlab : LargeEvenInLambda2 lab)
    (h : lab.tag = .B ∨ lab.tag = .C ∨ (lab.tag = .D ∧ 4 ≤ lab.rank)) :
    LargeEvenLabelAll lab fun _ _ _ F => ∀ f ∈ F, f ^ lab.n = 1 := by
  obtain ⟨t, l, n⟩ := lab
  have hn : 1 ≤ n := hlab.1
  intro Q hQ
  rcases h with ht | ht | ⟨ht, hl⟩ <;> dsimp only at ht <;> subst ht
  · dsimp only [LargeEvenRawDatum] at hQ ⊢
    exact NbrGraphSymplectic.recipeSymplectic_all (fun _ _ _ hK _ hf =>
      pow_eq_one_of_mem_field_symplectic hn hK hf) hQ
  · dsimp only [LargeEvenRawDatum] at hQ ⊢
    exact NbrGraphSymplectic.recipeSymplectic_all (fun _ _ _ hK _ hf =>
      pow_eq_one_of_mem_field_symplectic hn hK hf) hQ
  · dsimp only at hl
    dsimp only [LargeEvenRawDatum] at hQ ⊢
    split_ifs at hQ ⊢ with h3
    · omega
    · obtain ⟨K, _, _, hK, hQ⟩ := hQ
      exact ⟨K, inferInstance, inferInstance, hK, hQ, fun f hf =>
        pow_eq_one_of_mem_field_omegaPlus (by omega) hn hK hf⟩

end NbrLangRest

open NbrLangRest

theorem ggNbrLangTorusAxisOn_of_pow_mem {S : ℕ → LargeEvenLabel → Prop}
    (h : ∀ (p : ℕ) (lab : LargeEvenLabel), p.Prime → p ≠ 2 → LargeEvenInLambda2 lab → S p lab →
      LargeEvenLabelAll lab fun R _ I _ => ∀ φ : MulAut R, φ ^ p = 1 → φ ∈ I) :
    GGNbrLangTorusAxisOn S := by
  intro G _ _ p B Bs x L D J hC y K hK hN P hP
  obtain ⟨hperf, lab, hlab, hraw⟩ := hP
  refine ⟨hperf, lab, hlab, ?_⟩
  by_cases hS : S p lab
  · refine largeEvenRawDatum_mono ?_
      (h p lab hC.1.2.2.2.2.2.1.1 hC.1.2.2.2.2.2.1.2.1 hlab hS _ hraw)
    rintro R _ I F ⟨⟨hs, hna, θ, hPθ⟩, hpow⟩
    exact ⟨hs, hna, θ, hPθ, fun _ _ b₀ hb₀ hb₀I =>
      absurd (hpow _ (ggLAut_pow_eq_one hC hN θ hb₀)) hb₀I⟩
  · exact largeEvenRawDatum_mono
      (fun R _ I F ⟨hs, hna, θ, hθ⟩ => ⟨hs, hna, θ, hθ, fun h' => absurd h' hS⟩) hraw

theorem ggNbrLangTorusAxisOn_of_field_eq_one {S : ℕ → LargeEvenLabel → Prop}
    (h : ∀ (p : ℕ) (lab : LargeEvenLabel), p.Prime → p ≠ 2 → LargeEvenInLambda2 lab → S p lab →
      LargeEvenLabelAll lab fun _ _ _ F => ∀ f ∈ F, f = 1) :
    GGNbrLangTorusAxisOn S := by
  intro G _ _ p B Bs x L D J hC y K hK hN P hP
  obtain ⟨hperf, lab, hlab, hraw⟩ := hP
  refine ⟨hperf, lab, hlab, ?_⟩
  by_cases hS : S p lab
  · refine largeEvenRawDatum_mono ?_
      (h p lab hC.1.2.2.2.2.2.1.1 hC.1.2.2.2.2.2.1.2.1 hlab hS _ hraw)
    rintro R _ I F ⟨⟨hs, hna, θ, hPθ⟩, hF⟩
    refine ⟨hs, hna, θ, hPθ, fun _ hgr b₀ hb₀ hb₀I => ?_⟩
    obtain ⟨u, hu, f, hf, heq⟩ := hgr b₀ hb₀
    rw [eq_one_of_mem_closure_of_forall hF hf, mul_one] at heq
    exact absurd (heq ▸ hu) hb₀I
  · exact largeEvenRawDatum_mono
      (fun R _ I F ⟨hs, hna, θ, hθ⟩ => ⟨hs, hna, θ, hθ, fun h' => absurd h' hS⟩) hraw

theorem ggNbrLangTorusAxisOn_of_conj_fieldPow {S : ℕ → LargeEvenLabel → Prop}
    (N : LargeEvenLabel → ℕ)
    (h : ∀ (p : ℕ) (lab : LargeEvenLabel), p.Prime → p ≠ 2 → LargeEvenInLambda2 lab → S p lab →
      ¬ p ∣ N lab ∧ LargeEvenLabelAll lab (GGRawFieldConj p) ∧
        LargeEvenLabelAll lab fun _ _ _ F => ∀ f ∈ F, f ^ N lab = 1) :
    GGNbrLangTorusAxisOn S := by
  intro G _ _ p B Bs x L D J hC y K hK hN P hP
  obtain ⟨hperf, lab, hlab, hraw⟩ := hP
  refine ⟨hperf, lab, hlab, ?_⟩
  by_cases hS : S p lab
  · obtain ⟨hpN, hconj, hpow⟩ :=
      h p lab hC.1.2.2.2.2.2.1.1 hC.1.2.2.2.2.2.1.2.1 hlab hS
    refine largeEvenRawDatum_mono ?_ (largeEvenLabelAll_and hconj hpow _ hraw)
    rintro R _ I F ⟨⟨hs, hna, θ, hPθ⟩, hcj, hfp⟩
    refine ⟨hs, hna, θ, hPθ, fun _ hgr b₀ hb₀ hb₀I => ?_⟩
    obtain ⟨u, hu, f, hf, heq⟩ := hgr b₀ hb₀
    have hp1 : (u * f) ^ p = 1 := heq ▸ ggLAut_pow_eq_one hC hN θ hb₀
    obtain ⟨f', hf', u', -, hord, -⟩ := hcj hs hna u hu f hf (heq ▸ hb₀I) hp1
    exact absurd (hord ▸ orderOf_dvd_of_pow_eq_one (hfp f' hf')) hpN
  · exact largeEvenRawDatum_mono
      (fun R _ I F ⟨hs, hna, θ, hθ⟩ => ⟨hs, hna, θ, hθ, fun h' => absurd h' hS⟩) hraw

theorem ggNbrLangTorusAxisOn_openVac : GGNbrLangTorusAxisOn GGCorFourTwoOpenVacLabel :=
  ggNbrLangTorusAxisOn_of_pow_mem fun _ _ hp _ hlab h => largeEvenLabelAll_pow_mem_vac hp hlab h

theorem ggNbrLangTorusAxisOn_fieldTwo :
    GGNbrLangTorusAxisOn fun _ lab => GGNbrLangFieldTwoLabel lab :=
  ggNbrLangTorusAxisOn_of_field_eq_one fun _ _ _ _ _ h => largeEvenLabelAll_field_eq_one_two h

theorem ggNbrLangTorusAxisOn_linearCoprimeDeg : GGNbrLangTorusAxisOn GGLinearCoprimeDegLabel :=
  ggNbrLangTorusAxisOn_of_conj_fieldPow (fun lab => lab.n) fun p lab hp hp2 hlab h =>
    ⟨h.2, ggRawFieldConjOn_linear p hp hp2 lab hlab
      (h.1.elim Or.inl fun h' => Or.inr (Or.inl h')),
      largeEvenLabelAll_field_pow_linear hlab h.1⟩

theorem ggNbrLangTorusAxisOn_spOmegaCoprimeDeg : GGNbrLangTorusAxisOn GGSpOmegaCoprimeDegLabel :=
  ggNbrLangTorusAxisOn_of_conj_fieldPow (fun lab => lab.n) fun p lab hp hp2 hlab h =>
    ⟨h.2, h.1.elim (fun hB => ggRawFieldConjOn_symplectic p hp hp2 lab hlab (Or.inl hB))
      fun h' => h'.elim (fun hC => ggRawFieldConjOn_symplectic p hp hp2 lab hlab (Or.inr hC))
        fun hD => ggRawFieldConjOn_omegaPlus p hp hp2 lab hlab hD,
      largeEvenLabelAll_field_pow_spOmega hlab h.1⟩

end CFSG.StandardType

end

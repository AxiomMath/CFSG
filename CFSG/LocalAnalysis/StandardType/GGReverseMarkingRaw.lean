module

public import CFSG.LocalAnalysis.StandardType.MarkingClassical
public import CFSG.LocalAnalysis.StandardType.MarkingChevalley

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.Blueprint CFSG.Blueprint.Chevalley
open CFSG.ComponentClassification.ClassicalModelStatedBridge

variable {S : Type} [Group S]

theorem recipeLinear_of_statedClassicalModel {d f : ℕ} (h : StatedClassicalModel S .PSL d 2 f) :
    LargeEvenRecipeLinear d (2 ^ f) fun R _ _ _ => Nonempty (S ≃* R) := by
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := h
  obtain ⟨e'⟩ := nonempty_proj_congr (K := K) (statedSL_eq_ker_det K (n := d)).symm
  exact ⟨K, inferInstance, inferInstance, hK, ⟨e.trans e'.symm⟩⟩

theorem recipeUnitary_of_statedClassicalModel {d f : ℕ} (h : StatedClassicalModel S .PSU d 2 f) :
    LargeEvenRecipeUnitary d (2 ^ f) fun R _ _ _ => Nonempty (S ≃* R) := by
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := h
  exact ⟨K, inferInstance, inferInstance, hK, ⟨e⟩⟩

theorem recipeSymplectic_of_statedClassicalModel {m f : ℕ}
    (h : StatedClassicalModel S .PSp m 2 f) :
    LargeEvenRecipeSymplectic m (2 ^ f) false fun R _ _ _ => Nonempty (S ≃* R) := by
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := h
  exact ⟨K, inferInstance, inferInstance, hK, ⟨e⟩⟩

theorem recipeOmegaPlus_of_statedClassicalModel {m f : ℕ}
    (h : StatedClassicalModel S .POmegaPlus m 2 f) :
    LargeEvenRecipeOmegaPlus m (2 ^ f) fun R _ _ _ => Nonempty (S ≃* R) := by
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := h
  exact ⟨K, inferInstance, inferInstance, hK, ⟨e⟩⟩

theorem recipeOmegaMinus_of_statedClassicalModel {l f : ℕ}
    (h : StatedClassicalModel S .POmegaMinus l 2 f) :
    LargeEvenRecipeOmegaMinus (l - 1) (2 ^ f) fun R _ _ _ => Nonempty (S ≃* R) := by
  obtain ⟨-, K, _, _, hK, b, c, hbc, ⟨e⟩⟩ := h
  exact ⟨K, inferInstance, inferInstance, hK, b, c, hbc,
    ⟨e.trans (omegaMinusProjEquiv l b c).symm⟩⟩

theorem recipeChevalley_of_untwistedChevalleyModel (τ : Tag) {q : ℕ}
    (h : UntwistedChevalleyModel S τ q) :
    LargeEvenRecipeChevalley τ.cartan q false fun R _ _ _ => Nonempty (S ≃* R) := by
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ := h
  obtain ⟨e'⟩ := centerQuot_chevGroup_equiv K τ
  exact ⟨K, inferInstance, inferInstance, hK, ⟨e.trans e'.symm⟩⟩

theorem recipeTwisted_of_twistedChevalleyModel (t : TwistTag) {f : ℕ}
    (h : TwistedChevalleyModel S t (2 ^ f)) :
    LargeEvenRecipeTwisted t.tag.cartan t.perm t.order f fun R _ _ _ => Nonempty (S ≃* R) := by
  obtain ⟨K, _, _, hK, σ, hσ, ⟨e⟩⟩ := h
  obtain ⟨e'⟩ := centerQuot_twistedH_equiv K t f σ hσ
  exact ⟨K, inferInstance, inferInstance, hK, ⟨e.trans e'.symm⟩⟩

theorem recipeTwF4_of_reeTitsRelationModel {a : ℕ}
    (h : ReeTitsRelationModel S .F4 reeF4Perm reeF4Long 2 (2 * a + 1) a) :
    LargeEvenRecipeTwF4 a fun R _ _ _ => Nonempty (S ≃* R) := by
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ := h
  obtain ⟨e'⟩ := centerQuot_twF4H_equiv K a
  exact ⟨K, inferInstance, inferInstance, hK, ⟨e.trans e'.symm⟩⟩

theorem center_eq_bot_of_mulEquiv_of_center_eq_bot {S T : Type*} [Group S] [Group T]
    (e : S ≃* T) (hZ : Subgroup.center S = ⊥) : Subgroup.center T = ⊥ := by
  rw [eq_bot_iff]
  intro z hz
  have hz' : e.symm z ∈ Subgroup.center S := by
    rw [Subgroup.mem_center_iff]
    intro g
    apply e.injective
    rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
    exact Subgroup.mem_center_iff.mp hz (e g)
  rw [hZ, Subgroup.mem_bot] at hz'
  rw [Subgroup.mem_bot, ← e.apply_symm_apply z, hz', map_one]

theorem recipeSuzuki_of_mulEquiv {a : ℕ} {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 2 ^ (2 * a + 1)) (e : S ≃* suzukiGroup a K)
    (hZ : Subgroup.center S = ⊥) :
    LargeEvenRecipeSuzuki a fun R _ _ _ => Nonempty (S ≃* R) := by
  obtain ⟨e₁⟩ := nonempty_centerQuot_congr (largeEvenSzGroup_eq a K)
  have hZ' := center_eq_bot_of_mulEquiv_of_center_eq_bot e hZ
  let e₂ : LargeEvenCenterQuot (suzukiGroup a K) ≃* suzukiGroup a K :=
    (QuotientGroup.quotientMulEquivOfEq hZ').trans QuotientGroup.quotientBot
  exact ⟨K, inferInstance, inferInstance, hK, ⟨e.trans (e₁.trans e₂).symm⟩⟩

theorem exists_label_rawDatum_of_statedClassicalModel {t : StatedLieTag} {n f : ℕ}
    (h : StatedClassicalModel S t n 2 f) :
    ∃ lab : LargeEvenLabel, LargeEvenInLambda2 lab ∧ markTag lab = t ∧ markRank lab = n ∧
      markChar lab = 2 ∧ markDeg lab = f ∧
      LargeEvenRawDatum lab fun R _ _ _ => Nonempty (S ≃* R) := by
  obtain ⟨-, hf, hadm⟩ := h.1
  cases t with
  | PSL =>
    obtain ⟨hn, h22, -⟩ := hadm
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    have hm : m = 1 → 2 ≤ f := by
      rintro rfl
      by_contra hlt
      exact h22 (by rw [show f = 1 by omega]; rfl)
    exact ⟨⟨.A, m, f⟩, ⟨hf, (by omega : 1 ≤ m), hm⟩, rfl, rfl, rfl, rfl,
      recipeLinear_of_statedClassicalModel h⟩
  | PSU =>
    obtain ⟨hn, h32⟩ := hadm
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    have hm : m = 2 → 2 ≤ f := by
      rintro rfl
      by_contra hlt
      exact h32 (by rw [show f = 1 by omega]; rfl)
    exact ⟨⟨.twA, m, f⟩, ⟨hf, (by omega : 2 ≤ m), hm⟩, rfl, rfl, rfl, rfl,
      recipeUnitary_of_statedClassicalModel h⟩
  | PSp =>
    obtain ⟨hn, h22⟩ := hadm
    have hm : n = 2 → 2 ≤ f := by
      rintro rfl
      by_contra hlt
      exact h22 (by rw [show f = 1 by omega]; rfl)
    exact ⟨⟨.C, n, f⟩, ⟨hf, hn, hm⟩, rfl, rfl, rfl, rfl,
      recipeSymplectic_of_statedClassicalModel h⟩
  | POmegaOdd => exact absurd rfl hadm.2
  | POmegaPlus =>
    have h3 : n ≠ 3 := by omega
    refine ⟨⟨.D, n, f⟩, ⟨hf, (by omega : 3 ≤ n)⟩, ?_, ?_, rfl, rfl, ?_⟩
    · simp [markTag, h3]
    · simp [markRank, h3]
    · show if n = 3 then _ else _
      simp only [h3, ↓reduceIte]
      exact recipeOmegaPlus_of_statedClassicalModel h
  | POmegaMinus =>
    have h2 : n ≠ 2 := by omega
    have h3 : n ≠ 3 := by omega
    refine ⟨⟨.twD, n, f⟩, ⟨hf, (by omega : 2 ≤ n)⟩, ?_, ?_, rfl, ?_, ?_⟩
    · simp [markTag, h2, h3]
    · simp [markRank, h2, h3]
    · simp [markDeg, h2]
    · show if n = 2 then _ else if n = 3 then _ else _
      simp only [h2, h3, ↓reduceIte]
      exact recipeOmegaMinus_of_statedClassicalModel h
  | G2 | F4 | E6 | E7 | E8 | twistedE6 | trialityD4 | twistedB2 | twistedG2 | twistedF4 | Tits =>
    exact h.2.elim

theorem exists_label_rawDatum_of_chevalleyExceptionalModel {t : StatedLieTag} {f : ℕ}
    (h : ChevalleyExceptionalModel S t 2 f) :
    ∃ lab : LargeEvenLabel, LargeEvenInLambda2 lab ∧ markTag lab = t ∧ markRank lab = 0 ∧
      markChar lab = 2 ∧ markDeg lab = f ∧
      LargeEvenRawDatum lab fun R _ _ _ => Nonempty (S ≃* R) := by
  obtain ⟨⟨-, hf, hadm⟩, h⟩ := h
  cases t with
  | G2 =>
    obtain ⟨-, h3⟩ := hadm
    have hf2 : 2 ≤ f := by
      by_contra hlt
      obtain rfl : f = 1 := by omega
      norm_num at h3
    exact ⟨⟨.G2, 0, f⟩, ⟨hf, rfl, hf2⟩, rfl, rfl, rfl, rfl,
      recipeChevalley_of_untwistedChevalleyModel .G2 h⟩
  | F4 => exact ⟨⟨.F4, 0, f⟩, ⟨hf, rfl⟩, rfl, rfl, rfl, rfl,
      recipeChevalley_of_untwistedChevalleyModel .F4 h⟩
  | E6 => exact ⟨⟨.E6, 0, f⟩, ⟨hf, rfl⟩, rfl, rfl, rfl, rfl,
      recipeChevalley_of_untwistedChevalleyModel .E6 h⟩
  | E7 => exact ⟨⟨.E7, 0, f⟩, ⟨hf, rfl⟩, rfl, rfl, rfl, rfl,
      recipeChevalley_of_untwistedChevalleyModel .E7 h⟩
  | E8 => exact ⟨⟨.E8, 0, f⟩, ⟨hf, rfl⟩, rfl, rfl, rfl, rfl,
      recipeChevalley_of_untwistedChevalleyModel .E8 h⟩
  | twistedE6 => exact ⟨⟨.twE6, 0, f⟩, ⟨hf, rfl⟩, rfl, rfl, rfl, rfl,
      recipeTwisted_of_twistedChevalleyModel .E6 h⟩
  | trialityD4 => exact ⟨⟨.triD4, 0, f⟩, ⟨hf, rfl⟩, rfl, rfl, rfl, rfl,
      recipeTwisted_of_twistedChevalleyModel .D4 h⟩
  | PSL | PSU | PSp | POmegaOdd | POmegaPlus | POmegaMinus | twistedB2 | twistedG2 | twistedF4
    | Tits => exact h.elim

theorem exists_label_rawDatum_of_reeTitsModel {t : StatedLieTag} {f : ℕ}
    (h : ReeTitsModel S t 2 f) :
    ∃ lab : LargeEvenLabel, LargeEvenInLambda2 lab ∧ markTag lab = t ∧ markRank lab = 0 ∧
      markChar lab = 2 ∧ markDeg lab = f ∧
      LargeEvenRawDatum lab fun R _ _ _ => Nonempty (S ≃* R) := by
  obtain ⟨⟨-, hf, hadm⟩, a, hfa, h⟩ := h
  cases t with
  | twistedF4 =>
    obtain ⟨-, -, hodd, h3⟩ := hadm
    have hraw : LargeEvenRecipeTwF4 ((f - 1) / 2) fun R _ _ _ => Nonempty (S ≃* R) := by
      rw [show (f - 1) / 2 = a by omega]
      subst hfa
      exact recipeTwF4_of_reeTitsRelationModel h
    exact ⟨⟨.twF4, 0, f⟩, ⟨hf, rfl, hodd, h3⟩, rfl, rfl, rfl, rfl, hraw⟩
  | Tits =>
    obtain ⟨-, -, rfl⟩ := hadm
    obtain rfl : a = 0 := by omega
    exact ⟨⟨.twF4der, 0, 1⟩, ⟨le_rfl, rfl, rfl⟩, rfl, rfl, rfl, rfl,
      recipeTwF4_of_reeTitsRelationModel h⟩
  | twistedG2 => exact absurd hadm.2.1 (by decide)
  | PSL | PSU | PSp | POmegaOdd | POmegaPlus | POmegaMinus | G2 | F4 | E6 | E7 | E8 | twistedE6
    | trialityD4 | twistedB2 => exact h.elim

theorem exists_label_rawDatum_of_suzukiModel (hZ : Subgroup.center S = ⊥) {f : ℕ}
    (h : SuzukiModel S 2 f) :
    ∃ lab : LargeEvenLabel, LargeEvenInLambda2 lab ∧ markTag lab = .twistedB2 ∧
      markRank lab = 0 ∧ markChar lab = 2 ∧ markDeg lab = f ∧
      LargeEvenRawDatum lab fun R _ _ _ => Nonempty (S ≃* R) := by
  obtain ⟨-, a, ha, K, _, _, hfa, hK, ⟨e⟩⟩ := h
  have hraw : LargeEvenRecipeSuzuki ((f - 1) / 2) fun R _ _ _ => Nonempty (S ≃* R) := by
    rw [show (f - 1) / 2 = a by omega]
    subst hfa
    exact recipeSuzuki_of_mulEquiv hK e hZ
  exact ⟨⟨.twB2, 0, f⟩, ⟨(by omega : 1 ≤ f), rfl, (⟨a, hfa⟩ : Odd f), (by omega : 3 ≤ f)⟩,
    rfl, rfl, rfl, rfl, hraw⟩

theorem exists_label_rawDatum_of_lieModel (hZ : Subgroup.center S = ⊥) {t : StatedLieTag}
    {n f : ℕ} (h : LieModel S t n 2 f) :
    ∃ lab : LargeEvenLabel, LargeEvenInLambda2 lab ∧ markTag lab = t ∧ markRank lab = n ∧
      markChar lab = 2 ∧ markDeg lab = f ∧
      LargeEvenRawDatum lab fun R _ _ _ => Nonempty (S ≃* R) := by
  rcases h with ⟨-, h⟩ | ⟨rfl, -, h⟩ | ⟨rfl, -, h⟩ | ⟨rfl, rfl, h⟩
  · exact exists_label_rawDatum_of_statedClassicalModel h
  · exact exists_label_rawDatum_of_chevalleyExceptionalModel h
  · exact exists_label_rawDatum_of_reeTitsModel h
  · exact exists_label_rawDatum_of_suzukiModel hZ h

namespace Legacy
abbrev exists_label_rawDatum_of_lieModel := @CFSG.StandardType.exists_label_rawDatum_of_lieModel
end Legacy

namespace Canonical
theorem exists_label_rawDatum_of_lieModel (hZ : Subgroup.center S = ⊥) {t : StatedLieTag}
    {n f : ℕ} (h : LieModel S t n 2 f) :
    ∃ lab : LargeEvenLabel, LargeEvenInLambda2 lab ∧ markTag lab = t ∧ markRank lab = n ∧
      markChar lab = 2 ∧ markDeg lab = f ∧
      CFSG.Assembly.LargeEvenRawDatum lab fun R _ _ _ => Nonempty (S ≃* R) := by
  obtain ⟨lab, hlab, ht, hn, hp, hf, hraw⟩ :=
    CFSG.StandardType.exists_label_rawDatum_of_lieModel hZ h
  exact ⟨lab, hlab, ht, hn, hp, hf,
    CFSG.Assembly.largeEvenRawDatumLegacy_to_canonical_carrier hraw⟩
end Canonical

end CFSG.StandardType

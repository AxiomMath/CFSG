module

public import CFSG.LocalAnalysis.StandardType.GGTypeANbrLabels
public import CFSG.LocalAnalysis.StandardType.GGTwistedLabelModels
public import CFSG.LocalAnalysis.StandardType.GGNbrFieldOtherClassicalResL3Three
public import CFSG.HardMathSupport.Lang.UnitaryAutomorphisms.OuterFixedSubfieldPSL
public import CFSG.HardMathSupport.Lang.UnitaryAutomorphisms.OuterFixedSubfieldPSU
public import CFSG.HardMathSupport.Lang.UnitaryAutomorphisms.OuterFixedSubfieldPOmegaMinus
public import CFSG.LocalAnalysis.SectionRank.ClassicalEven.Linear
public import CFSG.LocalAnalysis.SectionRank.ClassicalEven.Orthogonal
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank.Agl418Block
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank65Plane
public import CFSG.GroupTheory.ElementaryAbelianTransport
public import CFSG.LocalAnalysis.ComponentClassification.OuterAutomorphisms
public import CFSG.HardMathSupport.Lang.UnitaryAutomorphisms.OuterFixedPOmegaEven
public import CFSG.LocalAnalysis.ComponentInitial.SteinbergBUProjectivePlaneFieldRoot
public import CFSG.LocalAnalysis.ComponentInitial.SteinbergBUProjectivePlaneHilbertNinety
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank614Defs
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank614PrimeDefs

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Assembly.LowTwoRank

private theorem exists_fixed_elemAbelian_of_injective_of_le_pRank {p k : ℕ} (hp : p.Prime)
    {M X : Type} [Group M] [Finite M] [Group X] (ι : M →* X) (hι : Function.Injective ι)
    {α : MulAut X} (hfix : ∀ y : M, α (ι y) = ι y)
    (hrank : k ≤ CFSG.Open.pRank p (⊤ : Subgroup M)) :
    ∃ A : Subgroup X, IsElemAbelian p A ∧ Nat.card A = p ^ k ∧ ∀ a ∈ A, α a = a := by
  obtain ⟨E, -, hE, hEcard⟩ :=
    CFSG.LocalAnalysis.RankThreeTheoremC.exists_isElemAbelian_of_le_pRank (G := M) (H := ⊤) hp hrank
  refine ⟨E.map ι, hE.map ι, ?_, ?_⟩
  · rw [Subgroup.card_map_of_injective hι, hEcard]
  · rintro a ⟨y, -, rfl⟩
    exact hfix y

theorem exists_fixed_elemAbelian_of_ggHasLabel_A5 {X : Type} [Group X]
    {f : ℕ} (hf : 1 ≤ f) (h3 : 3 ∣ 2 ^ f + 1) (hl : GGHasLabel ⟨.A, 5, f⟩ X)
    {α : MulAut X} (hα : α ^ 3 = 1) (hin : ∀ x : X, α ≠ MulAut.conj x) :
    ∃ A : Subgroup X, IsElemAbelian 3 A ∧ Nat.card A = 3 ^ 3 ∧ ∀ a ∈ A, α a = a := by
  have hΛ : LargeEvenInLambda2 ⟨.A, 5, f⟩ := by simp [LargeEvenInLambda2]; omega
  have hcl : StatedClassicalModel X .PSL 6 2 f :=
    statedClassicalModel_of_hasLabel_typeA hΛ hl
  have hαin : α ∉ CFSG.ComponentClassification.OuterAutomorphisms.inner X := by
    rintro ⟨x, hx⟩
    exact hin x hx.symm
  have hdiv : ¬ 3 ∣ Nat.gcd 6 (2 ^ f - 1) := by
    intro h
    have h2 : 3 ∣ 2 ^ f - 1 := h.trans (Nat.gcd_dvd_right 6 (2 ^ f - 1))
    have h2le : 2 ≤ 2 ^ f := by
      simpa using pow_le_pow_right' (show (1 : ℕ) ≤ 2 by norm_num) hf
    have hsub : (2 ^ f + 1) - (2 ^ f - 1) = 2 := by omega
    have h3dvd2 : 3 ∣ 2 := by
      rw [← hsub]
      exact Nat.dvd_sub h3 h2
    obtain ⟨c, hc⟩ := h3dvd2
    omega
  obtain ⟨-, K, hKField, hKFin, hKChar, -, ι, hι, hfix⟩ :=
    CFSG.HardMathSupport.Lang.UnitaryAutomorphisms.psl_prime_outer_fixed_subfield_embedding
      (n := 6) (ℓ := 2)
      (by omega) hcl Nat.prime_three (by norm_num) hdiv α hα hαin
  have hrank : 3 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup (StatedProj (StatedSL 6 K))) :=
    CFSG.SectionRank.ClassicalEven.psl_three_le_pRank_three (K := K) (n := 6) le_rfl
  exact exists_fixed_elemAbelian_of_injective_of_le_pRank Nat.prime_three ι hι hfix hrank

theorem exists_fixed_elemAbelian_of_ggHasLabel_twA5 {X : Type} [Group X]
    {f : ℕ} (hf : 1 ≤ f) (h3 : 3 ∣ 2 ^ f - 1) (hl : GGHasLabel ⟨.twA, 5, f⟩ X)
    {α : MulAut X} (hα : α ^ 3 = 1) (hin : ∀ x : X, α ≠ MulAut.conj x) :
    ∃ A : Subgroup X, IsElemAbelian 3 A ∧ Nat.card A = 3 ^ 3 ∧ ∀ a ∈ A, α a = a := by
  have hΛ : LargeEvenInLambda2 ⟨.twA, 5, f⟩ := by simp [LargeEvenInLambda2]; omega
  have hcl : StatedClassicalModel X .PSU 6 2 f :=
    statedClassicalModel_of_hasLabel_typeTwA hΛ hl
  have hαin : α ∉ CFSG.ComponentClassification.OuterAutomorphisms.inner X := by
    rintro ⟨x, hx⟩
    exact hin x hx.symm
  have hdiv : ¬ 3 ∣ Nat.gcd 6 (2 ^ f + 1) := by
    intro h
    have h2 : 3 ∣ 2 ^ f + 1 := h.trans (Nat.gcd_dvd_right 6 (2 ^ f + 1))
    have h2le : 2 ≤ 2 ^ f := by
      simpa using pow_le_pow_right' (show (1 : ℕ) ≤ 2 by norm_num) hf
    have hsub : (2 ^ f + 1) - (2 ^ f - 1) = 2 := by omega
    have h3dvd2 : 3 ∣ 2 := by
      rw [← hsub]
      exact Nat.dvd_sub h2 h3
    obtain ⟨c, hc⟩ := h3dvd2
    omega
  obtain ⟨h3f, K, hKField, hKFin, hKChar, hKcard, ι, hι, hfix⟩ :=
    CFSG.HardMathSupport.Lang.UnitaryAutomorphisms.psu_prime_outer_fixed_subfield_embedding
      (n := 6) (ℓ := 2)
      hcl Nat.prime_three (by norm_num) hdiv α hα hαin
  have h3mod : 3 ∣ 2 ^ (f / 3) - 1 :=
    L3Three.three_dvd_two_pow_div_three_sub_one h3f h3
  have hrank : 3 ≤ CFSG.Open.pRank 3
      (⊤ : Subgroup (StatedProj (StatedSU 6 (2 ^ (f / 3)) K))) :=
    CFSG.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank.psu_three_le_pRank_of_one_mod_three
      (K := K) (n := 6) (e := f / 3) hKcard h3mod le_rfl
  exact exists_fixed_elemAbelian_of_injective_of_le_pRank Nat.prime_three ι hι hfix hrank

theorem exists_fixed_elemAbelian_of_ggHasLabel_twD4 {X : Type} [Group X]
    {f : ℕ} (hl : GGHasLabel ⟨.twD, 4, f⟩ X)
    {α : MulAut X} (hα : α ^ 3 = 1) (hin : ∀ x : X, α ≠ MulAut.conj x) :
    ∃ A : Subgroup X, IsElemAbelian 3 A ∧ Nat.card A = 3 ^ 3 ∧ ∀ a ∈ A, α a = a := by
  have hcl : StatedClassicalModel X .POmegaMinus 4 2 f :=
    statedClassicalModel_of_hasLabel_typeTwD (by norm_num) hl
  have hαin : α ∉ CFSG.ComponentClassification.OuterAutomorphisms.inner X := by
    rintro ⟨x, hx⟩
    exact hin x hx.symm
  obtain ⟨-, K, hKField, hKFin, hKChar, b, c, -, -, ι, hι, hfix⟩ :=
    CFSG.HardMathSupport.Lang.UnitaryAutomorphisms.omegaMinus_prime_outer_fixed_subfield_embedding
      (n := 4) (ℓ := 2)
      hcl Nat.prime_three (by norm_num) α hα hαin
  have hrank : 3 ≤ CFSG.Open.pRank 3
      (⊤ : Subgroup (StatedProj (StatedOmega (StatedQuadMinus 4 K b c)))) :=
    CFSG.SectionRank.ClassicalEven.omegaMinus_three_le_pRank_three (K := K) (n := 4) le_rfl b c
  exact exists_fixed_elemAbelian_of_injective_of_le_pRank Nat.prime_three ι hι hfix hrank

end CFSG.StandardType

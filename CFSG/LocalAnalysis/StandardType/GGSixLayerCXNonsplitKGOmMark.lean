module

public import CFSG.LocalAnalysis.StandardType.GGSixLayerCXNonsplitKGOmCent
public import CFSG.LocalAnalysis.StandardType.GGSixLayerCXNonsplitKGClSpOne
public import CFSG.LocalAnalysis.StandardType.GGRecipeFieldOmega
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotCatTypeDet
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotCatTypeDet
public import CFSG.LocalAnalysis.SeitzReduction.UnitaryPilotCatTypeDet
public import CFSG.LocalAnalysis.SeitzReduction.RankOneCatSL2TypeDet
public import CFSG.RankThree.PartOne.S11d.OrthCaseN
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X7bPairs
public import CFSG.LocalAnalysis.SeitzReduction.UnitaryPilotCatAlt
public import CFSG.RankThree.PartOne.KC.OrthogonalD4WitnessEven
public import CFSG.RankThree.PartOne.KC.OrthogonalD4WitnessOdd
public import CFSG.RankThree.PartOne.KC.OrthogonalSubfieldCentralizer
public import CFSG.RankThree.PartOne.S11d.OutClassicalTwo
public import CFSG.RankThree.PartOne.S11d.OutLinear
public import CFSG.RankThree.PartOne.S11d.OutSymplectic
public import CFSG.RankThree.PartOne.S11d.OutUnitary
public import CFSG.RankThree.PartOne.S9.Sylow.ExclusionBasic
public import CFSG.RankThree.Theta.ThreeComponentOrbitCover

public section

namespace CFSG.StandardType

namespace OmNonsplit

open CFSG.Assembly CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.LieType.Universal Module
  QuadraticMap CFSG.ClassicalGroups.Orthogonal CFSG.RankThree.PartOne.KCOrthogonal
open scoped MatrixGroups

theorem halfSplit_A {p l n : ℕ} {c : Prop} (h : LargeEvenHalfSplit p ⟨.A, l, n⟩ c) :
    p ∣ 2 ^ n - 1 ∨ (n = 1 ∧ p = 3) ∨ l = 5 ∨ l = 8 := by
  rcases h with (⟨-, h⟩ | ⟨hu, -⟩ | ⟨ht, -⟩ | h) | ⟨ht, -⟩ | ⟨ht, -⟩ | h | h | h
  · exact Or.inl h
  · exact absurd trivial hu
  · simp at ht
  · exact Or.inr (Or.inl h)
  · simp at ht
  · simp at ht
  · exact Or.inr (Or.inr (Or.inl h.2.1))
  · exact Or.inr (Or.inr (Or.inr h.2.1))
  · simp at h

theorem halfSplit_twA {p l n : ℕ} {c : Prop} (h : LargeEvenHalfSplit p ⟨.twA, l, n⟩ c) :
    p ∣ 2 ^ n + 1 ∨ (n = 1 ∧ p = 3) ∨ l = 5 := by
  rcases h with (⟨hu, -⟩ | ⟨-, -, h⟩ | ⟨ht, -⟩ | h) | ⟨ht, -⟩ | ⟨ht, -⟩ | h | h | h
  · exact absurd hu id
  · exact Or.inl h
  · simp at ht
  · exact Or.inr (Or.inl h)
  · simp at ht
  · rcases ht with ⟨-, h⟩ | h
    · exact Or.inr (Or.inr h)
    · simp at h
  · simp at h
  · simp at h
  · simp at h

theorem halfSplit_D_twD {p n : ℕ} {t : LargeEvenLieTag} (ht : t = .D ∨ t = .twD) {l : ℕ}
    {c : Prop} (h : LargeEvenHalfSplit p ⟨t, l, n⟩ c) :
    p ∣ 2 ^ n - 1 ∨ p ∣ 2 ^ n + 1 ∨ (n = 1 ∧ p = 3) := by
  rcases ht with rfl | rfl
  · rcases h with (⟨-, h⟩ | ⟨hu, -⟩ | ⟨ht, -⟩ | h) | ⟨-, h⟩ | ⟨ht, -⟩ | h | h | h
    · exact Or.inl h
    · exact absurd trivial hu
    · simp at ht
    · exact Or.inr (Or.inr h)
    · exact Or.inr (Or.inl h)
    · simp at ht
    · simp at h
    · simp at h
    · simp at h
  · rcases h with (⟨hu, -⟩ | ⟨-, -, h⟩ | ⟨-, h⟩ | h) | ⟨ht, -⟩ | ⟨ht, -⟩ | h | h | h
    · exact absurd hu id
    · exact Or.inr (Or.inl h)
    · exact Or.inl h
    · exact Or.inr (Or.inr h)
    · simp at ht
    · simp at ht
    · simp at h
    · simp at h
    · simp at h

theorem not_dvd_two_pow_two_mul_sub_one {p f : ℕ} (hp : p.Prime) (hq1 : ¬ p ∣ 2 ^ f - 1)
    (hq2 : ¬ p ∣ 2 ^ f + 1) : ¬ p ∣ 2 ^ (2 * f) - 1 := by
  rw [mul_comm, pow_mul]
  exact not_dvd_sq_sub_one hp hq1 hq2

theorem markOm_label {lab : LargeEvenLabel} (hlab : LargeEvenInLambda2 lab)
    (hc : markChar lab = 2) {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hp3 : p ≠ 3)
    (hq1 : ¬ p ∣ 2 ^ f - 1) (hq2 : ¬ p ∣ 2 ^ f + 1)
    (h : ((markTag lab = .POmegaPlus ∨ markTag lab = .POmegaMinus) ∧ 4 ≤ markRank lab ∧
        markDeg lab = f) ∨
      ((markTag lab = .PSL ∨ markTag lab = .PSU) ∧ markRank lab = 4 ∧ markDeg lab = f) ∨
      (markTag lab = .PSL ∧ markRank lab = 2 ∧ markDeg lab = 2 * f)) :
    (∀ c, ¬ LargeEvenHalfSplit p lab c) ∧ LargeEvenLabelAll lab (GGRawInnField p) := by
  have hDD : ∀ {t : LargeEvenLieTag} (ht : t = .D ∨ t = .twD) {l : ℕ},
      ∀ c, ¬ LargeEvenHalfSplit p ⟨t, l, f⟩ c := by
    intro t ht l c hc'
    rcases halfSplit_D_twD ht hc' with h1 | h1 | ⟨-, h1⟩
    · exact hq1 h1
    · exact hq2 h1
    · exact hp3 h1
  obtain ⟨t, l, n⟩ := lab
  cases t
  case A =>
    simp only [markTag, markRank, markDeg] at h
    have h' : (l = 3 ∧ n = f) ∨ (l = 1 ∧ n = 2 * f) := by
      rcases h with ⟨h1 | h1, -⟩ | ⟨-, h2, h3⟩ | ⟨-, h2, h3⟩
      · simp at h1
      · simp at h1
      · exact Or.inl ⟨by omega, h3⟩
      · exact Or.inr ⟨by omega, h3⟩
    refine ⟨fun c hc' => ?_, ggRawInnFieldOn_linear p hp hp2 _ hlab (Or.inl rfl)⟩
    rcases h' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rcases halfSplit_A hc' with h1 | ⟨-, h1⟩ | h1 | h1
      · exact hq1 h1
      · exact hp3 h1
      · omega
      · omega
    · rcases halfSplit_A hc' with h1 | ⟨h1, -⟩ | h1 | h1
      · exact not_dvd_two_pow_two_mul_sub_one hp hq1 hq2 h1
      · omega
      · omega
      · omega
  case twA =>
    simp only [markTag, markRank, markDeg] at h
    have h' : l = 3 ∧ n = f := by
      rcases h with ⟨h1 | h1, -⟩ | ⟨-, h2, h3⟩ | ⟨h1, -⟩
      · simp at h1
      · simp at h1
      · exact ⟨by omega, h3⟩
      · simp at h1
    obtain ⟨rfl, rfl⟩ := h'
    refine ⟨fun c hc' => ?_, ggRawInnFieldOn_unitary p hp hp2 _ hlab (Or.inl rfl)⟩
    rcases halfSplit_twA hc' with h1 | ⟨-, h1⟩ | h1
    · exact hq2 h1
    · exact hp3 h1
    · omega
  case D =>
    by_cases hl : l = 3
    · subst hl
      simp only [markTag, markRank, markDeg, ite_true] at h
      have hn : n = f := by
        rcases h with ⟨h1 | h1, -⟩ | ⟨-, -, h3⟩ | ⟨-, h2, -⟩
        · simp at h1
        · simp at h1
        · exact h3
        · simp at h2
      subst hn
      exact ⟨hDD (Or.inl rfl),
        ggRawInnFieldOn_linear p hp hp2 _ hlab (Or.inr (Or.inl ⟨rfl, rfl⟩))⟩
    · simp only [markTag, markRank, markDeg, hl, ite_false] at h
      have h' : 4 ≤ l ∧ n = f := by
        rcases h with ⟨-, h2, h3⟩ | ⟨h1 | h1, -⟩ | ⟨h1, -⟩
        · exact ⟨h2, h3⟩
        · simp at h1
        · simp at h1
        · simp at h1
      obtain ⟨h4, rfl⟩ := h'
      exact ⟨hDD (Or.inl rfl), ggRawInnFieldOn_omega p hp hp2 _ hlab (Or.inl ⟨rfl, h4⟩)⟩
  case twD =>
    by_cases hl2 : l = 2
    · subst hl2
      simp only [markTag, markRank, markDeg, ite_true] at h
      have hn : n = f := by
        rcases h with ⟨h1 | h1, -⟩ | ⟨-, h2, -⟩ | ⟨-, -, h3⟩
        · simp at h1
        · simp at h1
        · simp at h2
        · omega
      subst hn
      exact ⟨hDD (Or.inr rfl),
        ggRawInnFieldOn_linear p hp hp2 _ hlab (Or.inr (Or.inr ⟨rfl, rfl⟩))⟩
    by_cases hl3 : l = 3
    · subst hl3
      simp only [markTag, markRank, markDeg, ite_true] at h
      have hn : n = f := by
        rcases h with ⟨h1 | h1, -⟩ | ⟨-, -, h3⟩ | ⟨h1, -⟩
        · simp at h1
        · simp at h1
        · exact h3
        · simp at h1
      subst hn
      exact ⟨hDD (Or.inr rfl), ggRawInnFieldOn_unitary p hp hp2 _ hlab (Or.inr ⟨rfl, rfl⟩)⟩
    · simp only [markTag, markRank, markDeg, hl2, hl3, ite_false] at h
      have h' : 4 ≤ l ∧ n = f := by
        rcases h with ⟨-, h2, h3⟩ | ⟨h1 | h1, -⟩ | ⟨h1, -⟩
        · exact ⟨h2, h3⟩
        · simp at h1
        · simp at h1
        · simp at h1
      obtain ⟨h4, rfl⟩ := h'
      exact ⟨hDD (Or.inr rfl), ggRawInnFieldOn_omega p hp hp2 _ hlab (Or.inr ⟨rfl, h4⟩)⟩
  all_goals simp [markTag, markRank, markDeg, markChar] at h hc

end OmNonsplit

end CFSG.StandardType

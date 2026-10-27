module

public import CFSG.LocalAnalysis.StandardType.Marking
public import CFSG.RankThree.PartOne.S12K.Rigidity
public import CFSG.RankThree.PartOne.FLM.OrdSmall
public import CFSG.Timmesfeld.Orders.ClassicalLinear
public import CFSG.Assembly.OrderReductions.InvertedSubgroup
public import CFSG.Assembly.OrderReductions.OddInversion
public import CFSG.LieType.Ree.LargeReeEightTorus
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasFive
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasSix
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalReflectionSplitting
public import CFSG.LocalAnalysis.ComponentInitial.SylowPointRecovery
public import CFSG.LocalAnalysis.SectionRank.BruhatLift
public import CFSG.LocalAnalysis.SectionRank.ClassicalOdd
public import CFSG.LocalAnalysis.SectionRank.EvenCover.LinearStep
public import CFSG.LocalAnalysis.SectionRank.LargeRee.SLTwo
public import CFSG.LocalAnalysis.SectionRank.LargeReeCover
public import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
public import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
public import CFSG.Sporadic.Schreier.TitsOther
public import CFSG.Walter.Defs

public section

namespace CFSG.StandardType

open CFSG.Open CFSG.Timmesfeld CFSG.Timmesfeld.Orders CFSG.Assembly CFSG.Assembly.LowTwoRank
  CFSG.Blueprint
open CFSG.RankThree.PartOne.S12K (charTwoOrder card_of_lieModel_two)
open CFSG.RankThree.PartOne.FLM (profile_exp_eq ten_le_tri)

theorem ggProfile_exp_of_eq {m N : ℕ} {Z : ℕ → Prop} (h : Profile m N Z) :
    (m = 5616 → N = 4) ∧ (m = 7800 → N = 3) := by
  refine ⟨fun hm => ?_, fun hm => ?_⟩
  · exact profile_exp_eq h (r := 351) (by decide) (by rw [hm]; norm_num)
  · exact profile_exp_eq h (r := 975) (by decide) (by rw [hm]; norm_num)

theorem ggCharTwoOrder_ne {t : StatedLieTag} {n f : ℕ} (hadm : StatedLieAdmissible t n 2 f) :
    charTwoOrder t n f ≠ 5616 ∧ charTwoOrder t n f ≠ 7800 := by
  obtain ⟨-, hf, hrest⟩ := hadm
  have hf' : f ≤ f * 1 := by omega
  cases t
  case PSL =>
    obtain ⟨hn, hn22, -⟩ := hrest
    have hP := ggProfile_exp_of_eq (profile_ordA (n := n - 1) (by omega) hf)
    change ordA (n - 1) (2 ^ f) ≠ 5616 ∧ ordA (n - 1) (2 ^ f) ≠ 7800
    have h10 : 5 ≤ n → 10 ≤ (n - 1) * (n - 1 + 1) / 2 := ten_le_tri
    have hmul : (n - 1) * (n - 1 + 1) / 2 ≤ f * ((n - 1) * (n - 1 + 1) / 2) :=
      Nat.le_mul_of_pos_left _ hf
    refine ⟨fun h => ?_, fun h => ?_⟩
    · have hN := hP.1 h
      rcases (show n = 2 ∨ n = 3 ∨ n = 4 ∨ 5 ≤ n by omega) with rfl | rfl | rfl | h5
      · have hf4 : f = 4 := by norm_num at hN; omega
        subst hf4
        revert h; decide
      · norm_num at hN; omega
      · norm_num at hN; omega
      · have := h10 h5; omega
    · have hN := hP.2 h
      rcases (show n = 2 ∨ n = 3 ∨ n = 4 ∨ 5 ≤ n by omega) with rfl | rfl | rfl | h5
      · have hf3 : f = 3 := by norm_num at hN; omega
        subst hf3
        revert h; decide
      · have hf1 : f = 1 := by norm_num at hN; omega
        subst hf1
        revert h; decide
      · norm_num at hN; omega
      · have := h10 h5; omega
  case PSU =>
    obtain ⟨hn, hne⟩ := hrest
    have hP := ggProfile_exp_of_eq (profile_ordTwistedA (n := n - 1) (by omega) hf)
    change ordTwistedA (n - 1) (2 ^ f) ≠ 5616 ∧ ordTwistedA (n - 1) (2 ^ f) ≠ 7800
    have h10 : 5 ≤ n → 10 ≤ (n - 1) * (n - 1 + 1) / 2 := ten_le_tri
    have hmul : (n - 1) * (n - 1 + 1) / 2 ≤ f * ((n - 1) * (n - 1 + 1) / 2) :=
      Nat.le_mul_of_pos_left _ hf
    refine ⟨fun h => ?_, fun h => ?_⟩
    · have hN := hP.1 h
      rcases (show n = 3 ∨ n = 4 ∨ 5 ≤ n by omega) with rfl | rfl | h5
      · norm_num at hN; omega
      · norm_num at hN; omega
      · have := h10 h5; omega
    · have hN := hP.2 h
      rcases (show n = 3 ∨ n = 4 ∨ 5 ≤ n by omega) with rfl | rfl | h5
      · have hf1 : f = 1 := by norm_num at hN; omega
        subst hf1
        exact hne rfl
      · norm_num at hN; omega
      · have := h10 h5; omega
  case PSp =>
    obtain ⟨hn, hne⟩ := hrest
    have hP := ggProfile_exp_of_eq (profile_ordBC (n := n) hf)
    change ordBC n (2 ^ f) ≠ 5616 ∧ ordBC n (2 ^ f) ≠ 7800
    have h4 : 4 ≤ n * n := Nat.mul_le_mul hn hn
    have hmul : n * n ≤ f * (n * n) := Nat.le_mul_of_pos_left _ hf
    refine ⟨fun h => ?_, fun h => ?_⟩
    · have hN := hP.1 h
      have hn2 : n = 2 := by
        by_contra hn2
        have h9 : 3 * 3 ≤ n * n := Nat.mul_le_mul (by omega : 3 ≤ n) (by omega : 3 ≤ n)
        omega
      subst hn2
      have hf1 : f = 1 := by omega
      subst hf1
      exact hne rfl
    · have hN := hP.2 h
      omega
  case POmegaOdd => exact absurd rfl hrest.2
  case POmegaPlus =>
    have hP := ggProfile_exp_of_eq (profile_ordD (n := n) (by omega) hf)
    change ordD n (2 ^ f) ≠ 5616 ∧ ordD n (2 ^ f) ≠ 7800
    have h12 : 4 * 3 ≤ n * (n - 1) := Nat.mul_le_mul hrest (by omega)
    have hmul : n * (n - 1) ≤ f * (n * (n - 1)) := Nat.le_mul_of_pos_left _ hf
    exact ⟨fun h => by have := hP.1 h; omega, fun h => by have := hP.2 h; omega⟩
  case POmegaMinus =>
    have hP := ggProfile_exp_of_eq (profile_ordTwistedD (n := n) (by omega) hf)
    change ordTwistedD n (2 ^ f) ≠ 5616 ∧ ordTwistedD n (2 ^ f) ≠ 7800
    have h12 : 4 * 3 ≤ n * (n - 1) := Nat.mul_le_mul hrest (by omega)
    have hmul : n * (n - 1) ≤ f * (n * (n - 1)) := Nat.le_mul_of_pos_left _ hf
    exact ⟨fun h => by have := hP.1 h; omega, fun h => by have := hP.2 h; omega⟩
  case G2 =>
    have hP := ggProfile_exp_of_eq (profile_ordG2 hf)
    exact ⟨fun h => by have := hP.1 h; omega, fun h => by have := hP.2 h; omega⟩
  case F4 =>
    have hP := ggProfile_exp_of_eq (profile_ordF4 hf)
    exact ⟨fun h => by have := hP.1 h; omega, fun h => by have := hP.2 h; omega⟩
  case E6 =>
    have hP := ggProfile_exp_of_eq (profile_ordE6 hf)
    exact ⟨fun h => by have := hP.1 h; omega, fun h => by have := hP.2 h; omega⟩
  case E7 =>
    have hP := ggProfile_exp_of_eq (profile_ordE7 hf)
    exact ⟨fun h => by have := hP.1 h; omega, fun h => by have := hP.2 h; omega⟩
  case E8 =>
    have hP := ggProfile_exp_of_eq (profile_ordE8 hf)
    exact ⟨fun h => by have := hP.1 h; omega, fun h => by have := hP.2 h; omega⟩
  case twistedE6 =>
    have hP := ggProfile_exp_of_eq (profile_ordTwistedE6 hf)
    exact ⟨fun h => by have := hP.1 h; omega, fun h => by have := hP.2 h; omega⟩
  case trialityD4 =>
    have hP := ggProfile_exp_of_eq (profile_ordTrialityD4 hf)
    exact ⟨fun h => by have := hP.1 h; omega, fun h => by have := hP.2 h; omega⟩
  case twistedB2 =>
    obtain ⟨-, -, -, hf3⟩ := hrest
    have hP := ggProfile_exp_of_eq (profile_ordSuzuki hf)
    exact ⟨fun h => by have := hP.1 h; omega, fun h => by have := hP.2 h; omega⟩
  case twistedG2 => exact absurd hrest.2.1 (by norm_num)
  case twistedF4 =>
    have hP := ggProfile_exp_of_eq (profile_ordTwistedF4 hf)
    exact ⟨fun h => by have := hP.1 h; omega, fun h => by have := hP.2 h; omega⟩
  case Tits =>
    change ordTits ≠ 5616 ∧ ordTits ≠ 7800
    rw [ordTits_eq]
    decide

section Marked


theorem ggMarkedModel_card_ne {lab : LargeEvenLabel} {R : Type} [Group R] (h : MarkedModel lab R) :
    Nat.card R ≠ 5616 ∧ Nat.card R ≠ 7800 := by
  obtain ⟨t, l, n⟩ := lab
  cases t
  case B2der =>
    obtain ⟨e⟩ := nonempty_alternatingGroup_of_markedModel_b2der rfl h
    rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup, Nat.card_fin]
    decide
  case G2der =>
    dsimp only [MarkedModel, markTag, markRank, markChar, markDeg] at h
    rcases h with ⟨-, -, K, _, _, hK, ⟨e⟩⟩ | ⟨hn, -⟩ | ⟨hn, -⟩ | ⟨hn, -⟩
    · rw [Nat.card_congr e.toEquiv,
        CFSG.Timmesfeld.ClassicalOrders.card_statedProj_statedSU Nat.prime_three le_rfl hK
          (by norm_num)]
      decide
    all_goals exact absurd hn (by norm_num)
  all_goals
    dsimp only [MarkedModel, markTag, markRank, markChar, markDeg] at h
    obtain ⟨hadm, hcard⟩ := card_of_lieModel_two h
    rw [hcard]
    exact ggCharTwoOrder_ne hadm

end Marked

end CFSG.StandardType

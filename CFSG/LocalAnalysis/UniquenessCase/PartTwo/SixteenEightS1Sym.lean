module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenDefs2
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs16a
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.R1613gCase153
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven10Norm
public import CFSG.ClassicalInvolution.Models.SymplecticPairs.Quadruple
public import CFSG.GH74.GLS.Stage2.Final.ModelOrd
public import CFSG.LieType.CurtisTits.SpecialLinear
public import CFSG.LocalAnalysis.AGLEmbedding.JStarReducedDefs
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanBlockCycSmall
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanCaseTwoCMSection
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabAutIrrHom
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabAutIrrXGen
public import CFSG.LocalAnalysis.AGLEmbedding.ResidualTools
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeMax
public import CFSG.LocalAnalysis.ComponentClassification.OutcomeLocalOddCentralizer
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotCatAlt
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotMainGraphOmegaMinusPiecesEmbed
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotLeviFactPiece
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC165ExclCard
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenDeltaBound
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSpLift
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenWitt
public import CFSG.RankThree.GroupTheory.SteinbergBMTwoPartCommutatorsOdd
public import CFSG.RankThree.PartOne.KC.LinearPrimeFieldActorSolvableCore
public import CFSG.RankThree.PartOne.KC.OrthogonalHighWittFixedSpace
public import CFSG.RankThree.PartOne.KC.OrthogonalSubfieldFixed
public import CFSG.RankThree.PartOne.S8.Statements
public import CFSG.RankThree.SteinbergR3EOrthogonalCoprimeCyclic

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup

variable {W : Type} [CommGroup W]

theorem s16e_symSum_of_deltaSym {A : Subgroup (MulAut W)} {t : MulAut W} {r m : ℕ}
    (h : DeltaSym A t (⊤ : Subgroup W) r m) : SymSumOfConj A ⊤ r m := by
  obtain ⟨Δ, hinj, hrk, hind, hsup, σ, hσsurj, hσact, -⟩ := h
  have hstab : ∀ g ∈ A, g ∈ A ⊓ stabSub (⊤ : Subgroup W) := fun g hg =>
    ⟨hg, fun u => ⟨fun _ => trivial, fun _ => trivial⟩⟩
  have hconj : conjSubs A (Δ 0) = Set.range Δ := by
    ext X
    constructor
    · rintro ⟨g, hg, rfl⟩
      exact ⟨σ ⟨g, hstab g hg⟩ 0, (hσact ⟨g, hstab g hg⟩ 0).symm⟩
    · rintro ⟨j, rfl⟩
      obtain ⟨g, hg⟩ := hσsurj (Equiv.swap 0 j)
      refine ⟨(g : MulAut W), g.2.1, ?_⟩
      have h0 := hσact g 0
      rw [hg, Equiv.swap_apply_left] at h0
      exact h0.symm
  refine ⟨Δ 0, hrk 0, ?_, ?_, ?_, ?_⟩
  · rw [hconj]
    exact hind
  · rw [hconj, sSup_range]
    exact hsup
  · rw [hconj, ← Set.image_univ, Set.ncard_image_of_injective _ hinj, Set.ncard_univ,
      Nat.card_eq_fintype_card, Fintype.card_fin]
  · intro π
    let e0 : ↥(conjSubs A (Δ 0)) ≃ ↥(Set.range Δ) :=
      Equiv.subtypeEquivRight (fun X => by rw [hconj])
    let e : ↥(conjSubs A (Δ 0)) ≃ Fin (r + 1) := e0.trans (Equiv.ofInjective Δ hinj).symm
    have hY : ∀ Y : ↥(conjSubs A (Δ 0)), Δ (e Y) = (Y : Subgroup W) := by
      intro Y
      have h1 : Equiv.ofInjective Δ hinj (e Y) = e0 Y :=
        (Equiv.ofInjective Δ hinj).apply_symm_apply (e0 Y)
      exact congrArg Subtype.val h1
    obtain ⟨g, hg⟩ := hσsurj (Equiv.permCongr e π)
    refine ⟨(g : MulAut W), g.2.1, fun Y => ?_⟩
    have h3 := hσact g (e Y)
    rw [hg] at h3
    have hpc : (Equiv.permCongr e π) (e Y) = e (π Y) := by
      simp [Equiv.permCongr_apply]
    rw [hpc, hY, hY] at h3
    exact h3

private theorem s16e_comm_of_elem {X : Type*} [Group X] {p n : ℕ}
    (h : IsElemAbelianOfRank p n X) : ∀ a b : X, a * b = b * a := by
  obtain ⟨e⟩ := h
  intro a b
  exact e.injective (by rw [map_mul, map_mul, mul_comm])

private theorem s16e_pow_eq_nine {p r : ℕ} (hp : p = 3 ∨ p = 7) (hr : 2 ≤ r) (h : p ^ r = 9) :
    p = 3 ∧ r = 2 := by
  rcases hp with rfl | rfl
  · refine ⟨rfl, ?_⟩
    have h32 : (3 : ℕ) ^ r = 3 ^ 2 := by rw [h]; norm_num
    exact Nat.pow_right_injective (by norm_num : 2 ≤ 3) h32
  · exfalso
    have h7 : 7 ^ 2 ≤ 7 ^ r := Nat.pow_le_pow_right (by norm_num) hr
    rw [h] at h7
    norm_num at h7

private theorem s16e_nine_le_pow {p r : ℕ} (hp : p = 3 ∨ p = 7) (hr : 2 ≤ r) : 9 ≤ p ^ r := by
  have hp3 : 3 ≤ p := by rcases hp with rfl | rfl <;> norm_num
  calc 9 = 3 ^ 2 := by norm_num
    _ ≤ p ^ 2 := Nat.pow_le_pow_left hp3 2
    _ ≤ p ^ r := Nat.pow_le_pow_right (by omega) hr

theorem s16e_symSum_of_conc4136W [Finite W] {A L : Subgroup (MulAut W)} {t : MulAut W} {p r : ℕ}
    (hp : p = 3 ∨ p = 7) (hr : 2 ≤ r) (hE : IsElemAbelianOfRank p r ↥L)
    (hWL : commSub ⊤ L = ⊤) (hrk : rk ↥(⊤ : Subgroup W) = (r + 1) * dParam p)
    (hW : Conc4_136W A t L)
    (hnine : p = 3 → r = 2 → (∀ x ∈ L, t * x * t⁻¹ = x⁻¹) → SymSumOfConj A ⊤ 2 2) :
    SymSumOfConj A ⊤ r (dParam p) := by
  have hpp : p.Prime := by rcases hp with rfl | rfl <;> norm_num
  have hcomm := s16e_comm_of_elem hE
  have hcard : Nat.card ↥L = p ^ r := A38.card_eq_of_isElemAbelianOfRank hpp hE
  have h9 := s16e_nine_le_pow hp hr
  obtain ⟨-, -, h⟩ := hW
  rcases h with h133 | ⟨K, hK, g, hg, hKne, hLK, htens⟩ | ⟨hcomp, -, -⟩ | ⟨-, -, hcomp, -⟩
  · obtain ⟨p', hp'p, -, -, -, halt⟩ := h133
    rcases halt with ⟨hcyc, h | h | h⟩ | ⟨hcyc, h⟩ | ⟨h1p2, h⟩ | ⟨hEA, h8, -⟩ |
      ⟨hcyc, h | h⟩ | ⟨r', m', hpm, hr2, hEAr, hrk', hDelta⟩ | ⟨hEA, h6, hinv⟩
    · exfalso; have := hcyc.2; omega
    · exfalso; have := hcyc.2; omega
    · exfalso; have := hcyc.2; omega
    · exfalso; have := hcyc.2; omega
    · exact (r1613g_not_isPOnePlusTwo_of_comm hcomm h1p2).elim
    · exfalso
      have hc9 : p ^ r = 9 := by
        have h9' := A38.card_eq_of_isElemAbelianOfRank (by norm_num : Nat.Prime 3) hEA
        rw [← hcard, h9']
        norm_num
      obtain ⟨rfl, rfl⟩ := s16e_pow_eq_nine hp hr hc9
      rw [hWL, rk_top] at h8
      rw [rk_top, s16c1610_dParam_three] at hrk
      omega
    · exfalso; have := hcyc.2; omega
    · exfalso; have := hcyc.2; omega
    · have hp'pr : p'.Prime := hp'p
      have hp'3 : p' = 3 ∨ p' = 7 := by rcases hpm with ⟨h, -⟩ | ⟨h, -⟩ <;> simp [h]
      have hcard' : Nat.card ↥L = p' ^ r' := A38.card_eq_of_isElemAbelianOfRank hp'pr hEAr
      have hpow : p ^ r = p' ^ r' := hcard.symm.trans hcard'
      obtain ⟨r₁, rfl⟩ : ∃ r₁, r = r₁ + 1 := ⟨r - 1, by omega⟩
      obtain ⟨r₂, rfl⟩ : ∃ r₂, r' = r₂ + 1 := ⟨r' - 1, by omega⟩
      obtain ⟨hpp', hrr'⟩ := Nat.Prime.pow_inj hpp hp'pr hpow
      subst hpp'
      have hrr : r₁ = r₂ := hrr'
      subst hrr
      rw [hWL] at hDelta
      have hsym := s16e_symSum_of_deltaSym hDelta
      rcases hpm with ⟨hp3, rfl⟩ | ⟨hp7, rfl⟩
      · subst hp3
        rw [s16c1610_dParam_three]
        exact hsym
      · subst hp7
        rw [s16c1610_dParam_seven]
        exact hsym
    · have hc9 : p ^ r = 9 := by
        have h9' := A38.card_eq_of_isElemAbelianOfRank (by norm_num : Nat.Prime 3) hEA
        rw [← hcard, h9']
        norm_num
      obtain ⟨rfl, rfl⟩ := s16e_pow_eq_nine hp hr hc9
      rw [s16c1610_dParam_three]
      exact hnine rfl rfl hinv
  · exfalso
    have hKL : K ≤ L := hLK ▸ le_sup_left
    exact r1613g_not_isQuasisimple_of_comm
      (fun a b => Subtype.ext (by
        have h := congrArg (fun x : ↥L => (x : MulAut W))
          (hcomm ⟨a.1, hKL a.2⟩ ⟨b.1, hKL b.2⟩)
        exact h)) hK.2.2
  · exact (r1613g_not_isQuasisimple_of_comm hcomm hcomp.2.2).elim
  · exact (r1613g_not_isQuasisimple_of_comm hcomm hcomp.2.2).elim

end CFSG.LocalAnalysis.UniquenessCase.PartTwo

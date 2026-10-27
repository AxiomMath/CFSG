module

public import CFSG.LocalAnalysis.UniquenessCase.UC1K32
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.KSeven.Reduce
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.KSeven.L2Even
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.KSeven.L2OddStep
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.KSeven.L3Final
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.KSeven.U3Final
import CFSG.RankThree.PartOne.AUTSL.Interface
import CFSG.LocalAnalysis.RankThreeTheoremC.KFacts.L28.OutThree.Reduction

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Seven

open CFSG.Open Subgroup
open CFSG.LocalAnalysis.ComponentInitial.LinearCover

set_option linter.unusedSectionVars false

private theorem kscs_sevenCore_of_sevenFree {J : Type} [Group J] (h : SevenFree J) :
    SevenCore J := by
  intro W hW hWne Z T hZ
  have htop : normalizer ((Z : Subgroup J) : Set J) ⊔ fixedBy W = ⊤ := h W hW hWne Z hZ
  exact eq_top_iff.mpr (le_trans (le_of_eq htop.symm) le_sup_left)

private theorem kscs_sevenCore_of_normalizer_sup_sylow_two {J : Type} [Group J]
    (h : ∀ (Z : Sylow 3 J) (T : Sylow 2 J),
      normalizer ((Z : Subgroup J) : Set J) ⊔ (T : Subgroup J) = ⊤) : SevenCore J := by
  intro W _ _ Z T _
  rw [eq_top_iff, ← h Z T]
  exact sup_le (le_trans le_sup_left le_sup_left) le_sup_right

section Certified


theorem sevenCore_of_isKGroup (J : Type) [Group J] [Finite J] (hK : IsKGroup J)
    (hs : IsSimpleGroup J) (h3 : 3 ∣ Nat.card J) (h9 : ¬ 9 ∣ Nat.card J)
    (h7 : ¬ 7 ∣ Nat.card J) : SevenCore J := by
  have hfac : (Nat.card J).factorization 3 = 1 := by
    have hJ0 : Nat.card J ≠ 0 := Nat.card_pos.ne'
    have hpos : 0 < Nat.factorization (Nat.card J) 3 :=
      Nat.Prime.factorization_pos_of_dvd Nat.prime_three hJ0 h3
    have hle : Nat.factorization (Nat.card J) 3 ≤ 1 := by
      by_contra h
      have h2 : 2 ≤ Nat.factorization (Nat.card J) 3 := by omega
      refine h9 ?_
      have hdvd := (Nat.prime_three.pow_dvd_iff_le_factorization hJ0).mpr h2
      simpa using hdvd
    omega
  by_cases hab : ∃ a b : J, a * b ≠ b * a
  · have hKopen : CFSG.Open.IsKGroup J := hK.kGroupNonab
    rcases CFSG.LocalAnalysis.UniquenessCase.UCK.k32_holds J hKopen hs hab
        (CFSG.LocalAnalysis.RankThreeTheoremC.L28.OutThree.pRank_three_top_eq_one hfac) with
      ⟨p, f, hL⟩ | ⟨p, f, hq, hL⟩ | ⟨p, f, hq, hU⟩ | hJ1
    ·
      obtain ⟨K, hKfield, hKfin, hcard, ⟨e⟩⟩ :=
        CFSG.RankThree.PartOne.AUTSL.exists_projectiveSL_equiv_of_lieModel hL
      letI : Field K := hKfield
      letI : Finite K := hKfin
      haveI : Fintype K := Fintype.ofFinite K
      have hf : 1 ≤ f := hL.admissible.2.1
      by_cases hp2 : p = 2
      ·
        haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
        have hFcard : Fintype.card K = 2 ^ f := by
          rw [← Nat.card_eq_fintype_card, hcard, hp2]
        haveI : CharP K 2 := charP_of_card_eq_prime_pow (p := 2) (f := f) hFcard
        have e' : J ≃* Matrix.SpecialLinearGroup (Fin 2) K :=
          e.trans (projectiveSLTwoEquivSL K)
        refine kscs_sevenCore_of_normalizer_sup_sylow_two fun Z T => ?_
        exact normalizer_sup_sylow_two_eq_top (F := K) (m := f) hFcard (by omega) e' h3 h9 Z T
      ·
        have hp : p.Prime := hL.admissible.1
        have eψ := (e.trans (projectiveSpecialLinearEquivProjectiveSL 2 K).symm).trans
            (CFSG.ComponentClassification.CatalogueSchreierLinearTwo.pslEquivCoordinateG K)
        refine kscs_sevenCore_of_sevenFree (sevenFree_of_goodL2o ?_)
        exact ⟨inferInstance, h3, h9, h7, K, inferInstance, inferInstance, p, f, hp, hp2, hf,
          hcard, ⟨eψ⟩⟩
    ·
      obtain ⟨K, hKfield, hKfin, hcard, ⟨e⟩⟩ :=
        CFSG.RankThree.PartOne.AUTSL.exists_projectiveSL_equiv_of_lieModel hL
      letI : Field K := hKfield
      letI : Finite K := hKfin
      refine kscs_sevenCore_of_sevenFree (sevenFree_of_goodL3 ?_)
      refine ⟨inferInstance, h3, h9, h7, K, inferInstance, inferInstance, ?_, ⟨e⟩⟩
      rw [hcard]
      exact hq
    ·
      have hp : p.Prime := hU.admissible.1
      have hf : 1 ≤ f := hU.admissible.2.1
      obtain ⟨-, K, hKfield, hKfin, hKcard, ⟨e₀⟩⟩ := hU.statedClassicalModel (by decide)
      letI : Field K := hKfield
      letI : Finite K := hKfin
      have hUF : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData p f K :=
        ⟨hp, hf, by rw [hKcard, ← pow_mul, mul_comm]⟩
      have e₁ : J ≃* CFSG.ClassicalGroups.UnitaryFlag.unitaryPSU hUF 3 :=
        e₀.trans (CFSG.ClassicalGroups.UnitaryFlag.unitaryPSUEquiv hUF (by omega)).symm
      have e₂ : J ≃* U3 hUF :=
        e₁.trans (CFSG.RankThree.PartTwo.KFacts.psuPrimeFormEquiv hUF)
      refine kscs_sevenCore_of_sevenFree (sevenFree_of_goodU3 ?_)
      exact ⟨inferInstance, h3, h9, h7, p, f, K, inferInstance, hUF, hq, ⟨e₂⟩⟩
    ·
      obtain ⟨e⟩ := hJ1
      have hcardJ : Nat.card J = 175560 :=
        (Nat.card_congr e.toEquiv).trans CFSG.Sporadic.J1.card_J1
      exact absurd (by rw [hcardJ]; norm_num : 7 ∣ Nat.card J) h7
  ·
    have hcomm : ∀ a b : J, a * b = b * a := by
      intro a b
      exact not_not.mp (not_exists.mp (not_exists.mp hab a) b)
    letI : CommGroup J := { (inferInstance : Group J) with mul_comm := hcomm }
    intro W _ _ Z T _
    simp [CommGroup.normalizer_eq_top, top_sup_eq]

theorem ksevenGen_holds : KSevenGen :=
  ksevenGen_of_sevenCore fun J _ _ hK hs h3 h9 h7 => sevenCore_of_isKGroup J hK hs h3 h9 h7

end Certified

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Seven

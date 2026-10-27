module

public import CFSG.LocalAnalysis.StandardType.GGSixRCKC1IIIE8ThreeComponents
public import CFSG.LocalAnalysis.StandardType.GGSixRCK1416Defs
import CFSG.LocalAnalysis.StandardType.GGSixUnitaryTwoInnerDiag
import CFSG.LocalAnalysis.StandardType.GGSixRCKC1IIIUnitaryRecognition
import CFSG.LocalAnalysis.StandardType.GGSixRCKC1IIpAction
import CFSG.LocalAnalysis.StandardType.GGSixRCKC1IIINativeMinus
import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeStepA
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeFamInBCDCharTwo

public section
namespace CFSG.StandardType.RCKC1
open CFSG CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.StandardType


theorem k2At_or_exceptional_of_e8_three_compConfig
    {X : Type} [Group X] [Finite X] {n : ℕ}
    {ψ : (ggU .E8 n 1).K →* X} {G₀ A B₁ D J L K V : Subgroup X} {e r : X}
    (hcfg : RCKRP.RCKCompConfig .E8 n 1 ψ 3 G₀ A B₁ D J L K e)
    (hrow : GGSixRCKJRow .III J) (hFour : FourAt J V r)
    (hCore : CoreCommAt J V r) (hShort : ShortAt J r) :
    K2At K V r ∨
      GGHasLabel ⟨.twE6, 0, 1⟩ (↥K ⧸ Subgroup.center ↥K) ∨
      GGHasLabel ⟨.E7, 0, 1⟩ (↥K ⧸ Subgroup.center ↥K) := by
  obtain ⟨lab, hmem, hlabel⟩ := e8_three_compConfig_has_component_label hcfg
  obtain ⟨-, -, hp, hp2, hA, hBA, hDB, hDcard, hAN, -, hBNJ, hBCJ, hBcard, -, -, -,
    -, -, hJcomp, hOddJ, -, -, -, -, -, heD, hene, hKcomp, hJK, hOddK⟩ := hcfg
  obtain ⟨hBNK, d, hdD, -, hJd⟩ := RCKRP.le_normalizer_and_exists_isComponentOf_of_plane
    hp hA hBA hDB hDcard hAN hBNJ hJcomp heD hene hKcomp hJK
  have hdB : d ∈ B₁ := hDB hdD
  have hKperf : commutator ↥K = ⊤ := hKcomp.2.2.1
  have hBab : CFSG.Open.IsElemAbelian 3 B₁ := CFSG.Open.IsElemAbelian.mono hA hBA
  have hBpow : ∀ b ∈ B₁, b ^ 3 = 1 := fun b hb => hA.2 b (hBA hb)
  haveI : IsSimpleGroup (↥K ⧸ Subgroup.center ↥K) := hKcomp.2.2.2
  have hnab : ∃ a b : ↥K ⧸ Subgroup.center ↥K, a * b ≠ b * a :=
    exists_mul_ne_mul_centerQuot_of_perfect hKperf inferInstance
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl
  · exact Or.inr (Or.inl hlabel)
  · have hM := GGK0MarkedArithmetic.markedModel_of_label
      (by simp [LargeEvenInLambda2]) hnab hlabel
    have hLM : LieModel (↥K ⧸ Subgroup.center ↥K) .PSU 9 2 1 := by
      simpa [MarkedModel, markTag, markRank, markChar, markDeg] using hM
    obtain ⟨φ, hφr, hφk, hφID⟩ :=
      exists_unitary_two_innerDiag_presentation hBNK hBpow hKperf hOddK (by decide) hLM
    exact Or.inl (k2At_of_fixedSUBlockAt
      (fixedSUBlockAt_of_native_unitary_model hp hp2 (hBpow d hdB) φ hφr hφk
        (hBNK hdB) (hφID d hdB) hJd hrow) hJK hFour hCore hShort)
  · exact Or.inr (Or.inr hlabel)
  · have hM := GGK0MarkedArithmetic.markedModel_of_label
      (by simp [LargeEvenInLambda2]) hnab hlabel
    have hLM : LieModel (↥K ⧸ Subgroup.center ↥K) .POmegaMinus 7 2 1 := by
      simpa [MarkedModel, markTag, markRank, markChar, markDeg] using hM
    have hmodel : RCKRP.RCKClassicalModelIDAt .POmegaMinus K B₁ :=
      rckClassicalModelIDAt_orthogonal_two_of_elemAbelian hp hp2 hBab hBNK hKperf hOddK
        hLM (Or.inl ⟨rfl, by decide⟩)
    have hrank : 3 ^ 2 * Nat.card ↥(B₁ ⊓ Subgroup.centralizer (J : Set X)) ≤ Nat.card B₁ := by
      rw [hBCJ, hDcard]
      calc 3 ^ 2 * 3 ^ 2 = 3 ^ 4 := by ring
        _ ≤ Nat.card B₁ := hBcard
    exact Or.inl (k2At_of_row_III_of_minus_modelID hp hp2 hBab hdB hBNK hrank hmodel hJd
      hrow hOddJ hOddK hJK hFour hCore hShort)

end CFSG.StandardType.RCKC1

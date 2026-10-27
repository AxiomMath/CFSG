module

public import CFSG.LocalAnalysis.WeakClosure81.W16LSixBFree
public import CFSG.LocalAnalysis.WeakClosure81.W16LSixBEightC
public import CFSG.LocalAnalysis.WeakClosure81.W16LSixBEightD
public import CFSG.LocalAnalysis.WeakClosure81.W16LBShape
import CFSG.CGT.Timmesfeld75.Sec4CaseIIIRel

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.UC22 CFSG.SignalizerFunctorTheorem.Quadratic
open CFSG.Quasithin.G11
open Subgroup
open scoped Pointwise

variable {G : Type} [Group G] [Finite G] {M V₀ V U S H : Subgroup G}

theorem BarConf.centralInSylow {X : Type} [Group X] [Finite X] {B P : Subgroup X}
    (hc : BarConf X B P) (hB : Nat.card B = 2) : CentralInSylow X B := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine ⟨hc.isPGroup.toSylow hc.index_odd, hc.le, ?_⟩
  intro s hs p hp
  by_cases hs1 : s = 1
  · rw [hs1, one_mul, mul_one]
  have hpP : p ∈ Subgroup.normalizer (P : Set X) := Subgroup.le_normalizer hp
  have hpB : p ∈ Subgroup.normalizer (B : Set X) := hc.normalizer_le p hpP
  have hconj : p * s * p⁻¹ ∈ B := (Subgroup.mem_normalizer_iff.mp hpB s).mp hs
  have hconj_ne : p * s * p⁻¹ ≠ 1 := by
    intro h1
    apply hs1
    calc s = p⁻¹ * (p * s * p⁻¹) * p := by group
      _ = 1 := by rw [h1]; group
  have h_eq : p * s * p⁻¹ = s :=
    CFSG.CGT.Timmesfeld75.eq_of_card_two_subgroup hB hconj hs hconj_ne hs1
  calc s * p = (p * s * p⁻¹) * p := by rw [h_eq]
    _ = p * s := by group

section Certified


theorem IsMinFam16.barConf_hat (h1 : W16One G) (h5 : W16Five G) (hS : Std15 G)
    (h : Cex16 M V₀ V U S) (hH : IsMinFam16 M U S H) (hV : ¬ V ≤ pCoreOf 2 H)
    (D : ModDataE H (iSub16 V H)) : BarConf (hatX D V) (hatS D V) (hatP D V S) :=
  { IsMinFam16.barSituation_hat h1 h5 hS h hH hV D with
    isPGroup := (IsMinFam16.hatP_sylow h1 h5 hS h hH hV D).1
    index_odd := (IsMinFam16.hatP_sylow h1 h5 hS h hH hV D).2.1
    le := (IsMinFam16.hatP_sylow h1 h5 hS h hH hV D).2.2
    normalizer_le := IsMinFam16.hatX_normalizer_le h1 h5 hS h hH hV D
    free := IsMinFam16.hatX_free h1 h5 hS h hH hV D }

theorem IsMinFam16.noHyp85_hat (h1 : W16One G) (h5 : W16Five G) (hS : Std15 G)
    (h : Cex16 M V₀ V U S) (hH : IsMinFam16 M U S H) (hV : ¬ V ≤ pCoreOf 2 H)
    (D : ModDataE H (iSub16 V H)) (hF : W3Lem85ThreeFirst' (VG (D.img H))) :
    NoHyp85 (hatX D V) (hatS D V) := by
  have hc := IsMinFam16.barConf_hat h1 h5 hS h hH hV D
  obtain ⟨φ, hd, himg⟩ := IsMinFam16.shapeData_hat h1 h5 hS h hH hV D
    (fun hB => hc.centralInSylow hB)
  have hno := hd.noHyp85 (IsMinFam16.not_hyp85Three_hat h1 h5 hS h hH hV D hF)
  rwa [himg] at hno

theorem IsMinFam16.hatShape_img (hTim : TimmesfeldTIRootInput)
    (hGen : SevenK.TwoConjugateGeneration) (hCore : OddTranspositionCoreInputSC)
    (hList : OddTranspListBundle) (hIn : OrthReflParabolic)
    (h1 : W16One G) (h5 : W16Five G) (hS : Std15 G)
    (h : Cex16 M V₀ V U S) (hH : IsMinFam16 M U S H) (hV : ¬ V ≤ pCoreOf 2 H)
    (D : ModDataE H (iSub16 V H)) (hF : W3Lem85ThreeFirst' (VG (D.img H))) :
    HatShape166 (hatX D V) (hatS D V) (E3.mQuot V (iSub16 V H)) := by
  have hcard : Nat.card (hatS D V) = 2 ^ E3.mQuot V (iSub16 V H) := by
    rw [IsMinFam16.card_hatS_img h1 h5 hS h hH hV D]
    unfold E3.mQuot
    rw [inf_comm, Subgroup.inf_relIndex_right]
  have hB : hatS D V ≠ ⊥ := by
    intro hbot
    have hn : E3.mQuot V (iSub16 V H) = 0 := by
      have h0 : Nat.card (hatS D V) = 1 := by rw [hbot]; exact Subgroup.card_bot
      rw [h0] at hcard
      exact (Nat.pow_eq_one.1 hcard.symm).resolve_left (by norm_num)
    have hVI : V ≤ iSub16 V H := by
      have hz : E3.mQuot V (V ⊓ iSub16 V H) = 0 := by
        unfold E3.mQuot at hn ⊢
        rwa [inf_comm, Subgroup.inf_relIndex_right]
      have hVeq := (E3.mQuot_eq_zero_iff (B2F.isPGroup_of_isElemAbelian h.hyp.h6.elemAbelian)
        (inf_le_left : V ⊓ iSub16 V H ≤ V)).1 hz
      calc V = V ⊓ iSub16 V H := hVeq.symm
        _ ≤ iSub16 V H := inf_le_right
    exact hV (hVI.trans (Cex16.iSub16_le_pCoreOf h hH.1))
  exact w16l_hat_shape (IsMinFam16.barConf_hat h1 h5 hS h hH hV D) hB hcard
    (IsMinFam16.sevenElevenAlt_img hTim hGen hCore hList hIn h1 h5 hS h hH hV D)
    (IsMinFam16.noHyp85_hat h1 h5 hS h hH hV D hF)

end Certified

end CFSG.LocalAnalysis.WeakClosure81

end

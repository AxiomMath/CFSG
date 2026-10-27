module

public import CFSG.LocalAnalysis.StandardType.GGSixBstarExcFramesHalfToralDescent
public import CFSG.LocalAnalysis.StandardType.GGSixBstarExcFramesHalfThreeStep
public import CFSG.LocalAnalysis.StandardType.GGTableBExcThreeE7
import CFSG.LocalAnalysis.StandardType.GGSixBstarExcFramesHalfLemmaT
import CFSG.LocalAnalysis.StandardType.GGTableBExcTwoFusionE7
import CFSG.LocalAnalysis.StandardType.GGTableBExcTwoTBHalfKey
import CFSG.HardMathSupport.Timmesfeld.CrossChar.TwCompSUE7
import CFSG.HardMathSupport.Timmesfeld.CrossChar.TwCompSU
import CFSG.HardMathSupport.Timmesfeld.LangTorus.OuterField
import Certificates.Kernel.SporSch.Th.Plane2320

public section

namespace CFSG.StandardType.ExcFramesHalf

open CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley TableBExc TableBExc.Three
  TableBExcTwoFusion TableBExcTwoTB TableBExc.E6Three
open CFSG.HardMathSupport.Timmesfeld.CrossChar (e7_base_frame e7_base_01 e7_base_12)

@[expose] def frameWordE7 : Fin 3 → List (Fin Tag.E7.rank) :=
  ![[], [3, 4, 5, 2, 3, 4, 0, 2, 3, 0], [3, 2, 1, 3, 4, 5, 0, 2, 3, 4, 1, 3]]

@[expose] def lemmaTDataE7 : Fin 3 → Fin 4 → Fin Tag.E7.rank → ℤ :=
  ![![![0, 0, 0, 1, 0, 0, 0], ![1, 0, 1, 1, 0, 0, 0], ![0, 0, -1, -1, 0, 0, 0],
      ![0, 0, 0, -1, 0, 0, 0]],
    ![![0, 0, 0, 0, 0, 0, 1], ![0, 0, 0, 0, 0, 1, 1], ![0, 0, 0, 1, 0, 0, 0],
      ![0, 0, 0, 0, 0, 0, -1]],
    ![![0, 0, 0, 1, 0, 0, 0], ![0, 1, 0, 1, 0, 0, 0], ![0, 0, 0, -1, 0, 0, 0],
      ![0, 0, 0, 0, 0, 0, -1]]]

theorem frameWordE7_spec : ∀ i : Fin 3, ∀ j : Fin Tag.E7.rank,
    wordAct .E7 (frameWordE7 i) (reflect .E7 0 (reflect .E7 2
      (wordAct .E7 (frameWordE7 i).reverse (Pi.single j 1)))) =
      wordAct .E7 (wordE7G i) (Pi.single j 1) := by
  decide +kernel

theorem lemmaTDataE7_spec : ∀ i : Fin 3,
    wordAct .E7 (wordE7G i).reverse (lemmaTDataE7 i 0) +
        wordAct .E7 (wordE7G i).reverse (wordAct .E7 (wordE7G i).reverse (lemmaTDataE7 i 0)) +
        lemmaTDataE7 i 0 + (2 • wordAct .E7 (frameWordE7 i) (Pi.single 0 1) +
          wordAct .E7 (frameWordE7 i) (Pi.single 2 1)) =
      lemmaTDataE7 i 1 + lemmaTDataE7 i 1 + lemmaTDataE7 i 1 ∧
    lemmaTDataE7 i 2 - wordAct .E7 (wordE7G i).reverse (lemmaTDataE7 i 2) =
      wordAct .E7 (frameWordE7 i) (Pi.single 0 1) ∧
    lemmaTDataE7 i 3 - wordAct .E7 (wordE7G i).reverse (lemmaTDataE7 i 3) =
      wordAct .E7 (frameWordE7 i) (Pi.single 2 1) := by
  decide +kernel


theorem lemmaT_E7 {K : Type} [Field K] {ζ : Kˣ} (hζo : orderOf ζ = 3) (i : Fin 3)
    {E : Subgroup (ModGL .E7 K)} (hE : IsElemAbelian 3 E)
    (hEX : E ≤ xHat .E7 K (Subgroup.zpowers (gE7 i))) :
    ∃ y ∈ adjointGroup .E7 K, ∀ e ∈ E, ∃ c, y * e * y⁻¹ = rootDiagUnit .E7 c := by
  have hfr := (e7_base_frame (L := K)).transport ((coxeterSystem .E7).wordProd (frameWordE7 i))
  have hg : ∀ w : Fin Tag.E7.rank → ℤ, (gE7 i)⁻¹ • w = wordAct .E7 (wordE7G i).reverse w :=
    fun w => by rw [gE7, ← CoxeterSystem.wordProd_reverse, TableBExc.wordProd_smul]
  have h01 : (coxeterSystem .E7).wordProd (frameWordE7 i) •
      CFSG.RankThree.PartOne.KE.sigmaRoot 1 0 1 =
        wordAct .E7 (frameWordE7 i) (Pi.single 0 1) := by
    rw [e7_base_01, TableBExc.wordProd_smul]
  have h12 : (coxeterSystem .E7).wordProd (frameWordE7 i) •
      CFSG.RankThree.PartOne.KE.sigmaRoot 1 1 2 =
        wordAct .E7 (frameWordE7 i) (Pi.single 2 1) := by
    rw [e7_base_12, TableBExc.wordProd_smul]
  obtain ⟨horb, hu₁, hu₂⟩ := lemmaTDataE7_spec i
  refine exists_conj_diag_of_le_xHat_frame hζo hE (gE7_pow_three i) hEX hfr ?_
    (u := lemmaTDataE7 i 0) (μ := lemmaTDataE7 i 1) (by simp only [hg, h01, h12]; exact horb)
    (u₁ := lemmaTDataE7 i 2) (by rw [hg, h01]; exact hu₁)
    (u₂ := lemmaTDataE7 i 3) (by rw [hg, h12]; exact hu₂)
  show rootReflection ((coxeterSystem .E7).wordProd (frameWordE7 i) •
      CFSG.RankThree.PartOne.KE.sigmaRoot 1 0 1) *
    rootReflection ((coxeterSystem .E7).wordProd (frameWordE7 i) •
      CFSG.RankThree.PartOne.KE.sigmaRoot 1 1 2) = gE7 i
  rw [e7_base_01, e7_base_12, rootReflection_eq_conj rfl, rootReflection_eq_conj rfl]
  refine ext_single fun j => ?_
  simp only [mul_smul, inv_smul_smul]
  simp only [simple_smul, ← CoxeterSystem.wordProd_reverse, TableBExc.wordProd_smul, gE7]
  exact frameWordE7_spec i j

theorem bigElemAbelianToralBar_E7_three : BigElemAbelianToralBar .E7 3 := by
  refine bigElemAbelianToralBar_of_finite Nat.prime_three (by norm_num) le_rfl
    fun K₁ _ _ _ hq A hA hcomm hpow hcard => ?_
  have h3 : 3 ∣ Nat.card K₁ - 1 := by simpa using hq
  refine exists_conj_torusGroup_three_of_model h3
    (isUnit_det_cartan_of_eq Nat.prime_three CFSG.LieType.Chevalley.det_cartan_E7 (by norm_num))
    (card_torusPow_E7 Nat.prime_three h3) cartan_symm_E7 modelHomE7 (not_three_dvd_index_E7 h3)
    (fun A' hAS hA' hA1 => ?_) (fun hζo i E hE hEX => ?_) hA hcomm hpow hcard
  · have hkey := card_mul_card_fix_lt_or_zpowers_of_model (torusPerm .E7 3) modelHomE7
      modelHomE7_injective (T := 3 ^ 6)
      (fun _ h3 hc h1 => card_mul_fixAllCard_lt_or_zpowers (T := 3 ^ 6) (B₁ := 3 ^ 4)
        (B₅ := 3 ^ 3) (m := 1) (torusPerm .E7 3) modelHomE7 fix_caseI_E7 card_fixShift_E7
        fix_centN_E7 caseII_E7 (by norm_num) (by norm_num) h3 hc h1) hAS hA' hA1
    simp only [torusPerm_apply] at hkey
    rcases hkey with h | ⟨i, hi, -⟩
    · exact Or.inl h
    · exact Or.inr ⟨i, hi⟩
  · have hgi : modelHomE7 (SemidirectProduct.inl (.ofAdd (Pi.single i 1))) = gE7 i := by
      rw [modelHomE7, modelHom_inl, modelN_single, ZMod.val_one, pow_one]
    rw [hgi] at hEX
    exact lemmaT_E7 hζo i hE hEX

end CFSG.StandardType.ExcFramesHalf

end

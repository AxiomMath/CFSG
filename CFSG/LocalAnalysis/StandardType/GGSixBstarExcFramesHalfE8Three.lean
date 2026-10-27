module

public import CFSG.LocalAnalysis.StandardType.GGSixBstarExcFramesHalfToralDescent
public import CFSG.LocalAnalysis.StandardType.GGSixBstarExcFramesHalfThreeStep
public import CFSG.LocalAnalysis.StandardType.GGTableBExcThreeE8
public import Certificates.Certificate1952
import CFSG.LocalAnalysis.StandardType.GGSixBstarExcFramesHalfLemmaT
import CFSG.LocalAnalysis.StandardType.GGTableBExcTwoFusionE8
import CFSG.LocalAnalysis.StandardType.GGTableBExcTwoTBHalfKey
import CFSG.HardMathSupport.Timmesfeld.CrossChar.TwCompE8
import CFSG.HardMathSupport.Timmesfeld.CrossChar.TwCompPath

public section

namespace CFSG.StandardType.ExcFramesHalf

open CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley TableBExc TableBExc.Three
  TableBExcTwoFusion TableBExcTwoTB TableBExc.E6Three
open CFSG.RankThree.PartOne.KE (sigmaRootE8 sigmaRootE8_eq_smul e8chain13 e8chainRoot13_values)
open CFSG.HardMathSupport.Timmesfeld.CrossChar (isA2Frame_rhoSigmaE8)

@[expose] def frameWordE8 : Fin 4 → List (Fin Tag.E8.rank) :=
  ![[], [3, 4, 5, 2, 3, 4, 0, 2, 3, 0], [3, 2, 1, 3, 4, 5, 0, 2, 3, 4, 1, 3],
    [6, 7, 5, 6, 4, 5, 3, 4, 2, 3, 0, 2, 1, 3, 4, 5, 6, 7, 2, 3, 0, 2, 1, 3, 4, 5, 6, 3, 2, 1, 3,
      4, 5, 0, 2, 3, 4, 1, 3, 0]]

@[expose] def lemmaTDataE8 : Fin 4 → Fin 4 → Fin Tag.E8.rank → ℤ :=
  ![![![0, 0, 0, 1, 0, 0, 0, 0], ![1, 0, 1, 1, 0, 0, 0, 0], ![0, 0, -1, -1, 0, 0, 0, 0],
      ![0, 0, 0, -1, 0, 0, 0, 0]],
    ![![0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 1, 1, 0], ![0, 0, 0, 1, 0, 0, 0, 0],
      ![0, 0, 0, 0, 0, 0, -1, 0]],
    ![![0, 0, 0, 1, 0, 0, 0, 0], ![0, 1, 0, 1, 0, 0, 0, 0], ![0, 0, 0, -1, 0, 0, 0, 0],
      ![0, 0, 0, 0, 0, 0, -1, 0]],
    ![![0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, -1, -1],
      ![0, 0, 0, 0, 0, 0, 2, 1]]]

theorem frameWordE8_spec : ∀ i : Fin 4, ∀ j : Fin Tag.E8.rank,
    wordAct .E8 (frameWordE8 i) (reflect .E8 0 (reflect .E8 2
      (wordAct .E8 (frameWordE8 i).reverse (Pi.single j 1)))) =
      wordAct .E8 (wordE8G i) (Pi.single j 1) := by
  decide +kernel

theorem lemmaTDataE8_spec : ∀ i : Fin 4,
    wordAct .E8 (wordE8G i).reverse (lemmaTDataE8 i 0) +
        wordAct .E8 (wordE8G i).reverse (wordAct .E8 (wordE8G i).reverse (lemmaTDataE8 i 0)) +
        lemmaTDataE8 i 0 + (2 • wordAct .E8 (frameWordE8 i) (Pi.single 0 1) +
          wordAct .E8 (frameWordE8 i) (Pi.single 2 1)) =
      lemmaTDataE8 i 1 + lemmaTDataE8 i 1 + lemmaTDataE8 i 1 ∧
    lemmaTDataE8 i 2 - wordAct .E8 (wordE8G i).reverse (lemmaTDataE8 i 2) =
      wordAct .E8 (frameWordE8 i) (Pi.single 0 1) ∧
    lemmaTDataE8 i 3 - wordAct .E8 (wordE8G i).reverse (lemmaTDataE8 i 3) =
      wordAct .E8 (frameWordE8 i) (Pi.single 2 1) := by
  decide +kernel


theorem lemmaT_E8 {K : Type} [Field K] {ζ : Kˣ} (hζo : orderOf ζ = 3) (i : Fin 4)
    {E : Subgroup (ModGL .E8 K)} (hE : IsElemAbelian 3 E)
    (hEX : E ≤ xHat .E8 K (Subgroup.zpowers (gE8 i))) :
    ∃ y ∈ adjointGroup .E8 K, ∀ e ∈ E, ∃ c, y * e * y⁻¹ = rootDiagUnit .E8 c := by
  have hg : ∀ w : Fin Tag.E8.rank → ℤ, (gE8 i)⁻¹ • w = wordAct .E8 (wordE8G i).reverse w :=
    fun w => by rw [gE8, ← CoxeterSystem.wordProd_reverse, TableBExc.wordProd_smul]
  have hc01 : CFSG.RankThree.E6.chainRoot e8chain13 0 1 =
      (Pi.single 0 1 : Fin Tag.E8.rank → ℤ) := e8chainRoot13_values.1
  have hc12 : CFSG.RankThree.E6.chainRoot e8chain13 1 2 =
      (Pi.single 2 1 : Fin Tag.E8.rank → ℤ) := e8chainRoot13_values.2.1
  have h01 : sigmaRootE8 ((coxeterSystem .E8).wordProd (frameWordE8 i)) 0 1 =
      wordAct .E8 (frameWordE8 i) (Pi.single 0 1) := by
    rw [sigmaRootE8_eq_smul, hc01, TableBExc.wordProd_smul]
  have h12 : sigmaRootE8 ((coxeterSystem .E8).wordProd (frameWordE8 i)) 1 2 =
      wordAct .E8 (frameWordE8 i) (Pi.single 2 1) := by
    rw [sigmaRootE8_eq_smul, hc12, TableBExc.wordProd_smul]
  obtain ⟨horb, hu₁, hu₂⟩ := lemmaTDataE8_spec i
  refine exists_conj_diag_of_le_xHat_frame hζo hE (gE8_pow_three i) hEX
    (isA2Frame_rhoSigmaE8 (L := K) ((coxeterSystem .E8).wordProd (frameWordE8 i))) ?_
    (u := lemmaTDataE8 i 0) (μ := lemmaTDataE8 i 1) (by simp only [hg, h01, h12]; exact horb)
    (u₁ := lemmaTDataE8 i 2) (by rw [hg, h01]; exact hu₁)
    (u₂ := lemmaTDataE8 i 3) (by rw [hg, h12]; exact hu₂)
  show rootReflection (sigmaRootE8 ((coxeterSystem .E8).wordProd (frameWordE8 i)) 0 1) *
    rootReflection (sigmaRootE8 ((coxeterSystem .E8).wordProd (frameWordE8 i)) 1 2) = gE8 i
  rw [sigmaRootE8_eq_smul, sigmaRootE8_eq_smul, hc01, hc12, rootReflection_eq_conj rfl,
    rootReflection_eq_conj rfl]
  refine ext_single fun j => ?_
  simp only [mul_smul, inv_smul_smul]
  simp only [simple_smul, ← CoxeterSystem.wordProd_reverse, TableBExc.wordProd_smul, gE8]
  exact frameWordE8_spec i j

theorem bigElemAbelianToralBar_E8_three : BigElemAbelianToralBar .E8 3 := by
  refine bigElemAbelianToralBar_of_finite Nat.prime_three (by norm_num) le_rfl
    fun K₁ _ _ _ hq A hA hcomm hpow hcard => ?_
  have h3 : 3 ∣ Nat.card K₁ - 1 := by simpa using hq
  refine exists_conj_torusGroup_three_of_model h3
    (isUnit_det_cartan_of_eq Nat.prime_three CFSG.LieType.Chevalley.det_cartan_E8 (by norm_num))
    (card_torusPow_E8 Nat.prime_three h3) cartan_symm_E8 modelHomE8 (not_three_dvd_index_E8 h3)
    (fun A' hAS hA' hA1 => ?_) (fun hζo i E hE hEX => ?_) hA hcomm hpow hcard
  · have hkey := card_mul_card_fix_lt_or_zpowers_of_model (torusPerm .E8 3) modelHomE8
      modelHomE8_injective (T := 3 ^ 7)
      (fun _ h3 hc h1 => card_mul_fixAllCard_lt_or_zpowers (T := 3 ^ 7) (B₁ := 3 ^ 4)
        (B₅ := 3 ^ 3) (m := 2) (torusPerm .E8 3) modelHomE8 fix_caseI_E8 card_fixShift_E8
        fix_centN_E8 caseII_E8 (by norm_num) (by norm_num) h3 hc h1) hAS hA' hA1
    simp only [torusPerm_apply] at hkey
    rcases hkey with h | ⟨i, hi, -⟩
    · exact Or.inl h
    · exact Or.inr ⟨i, hi⟩
  · have hgi : modelHomE8 (SemidirectProduct.inl (.ofAdd (Pi.single i 1))) = gE8 i := by
      rw [modelHomE8, modelHom_inl, modelN_single, ZMod.val_one, pow_one]
    rw [hgi] at hEX
    exact lemmaT_E8 hζo i hE hEX

end CFSG.StandardType.ExcFramesHalf

end

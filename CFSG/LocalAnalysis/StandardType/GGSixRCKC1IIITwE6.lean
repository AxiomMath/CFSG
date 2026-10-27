module

public import CFSG.Blueprint.Catalog
public import CFSG.LocalAnalysis.StandardType.GGNbrTableForms
public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeDefs
public import CFSG.LocalAnalysis.StandardType.GGSixRCKDefs
public import CFSG.LocalAnalysis.StandardType.GGSixRCK1416Defs
import CFSG.LocalAnalysis.StandardType.GGK0MarkedArithmetic
import CFSG.LocalAnalysis.StandardType.GGInnerDiagMpRestTypeDet
import CFSG.Timmesfeld.Orders.Exceptional
import CFSG.RankThree.PartTwo.Sec21.Item228Census2ProofExc
import CFSG.RankThree.PartTwo.Sec21.Item228Census2ProofUni
import CFSG.ClassicalGroups.UnitaryFlag.StatedBridge
import CFSG.LocalAnalysis.StandardType.GGSixRCKC1IIITwE6Components
import CFSG.LocalAnalysis.StandardType.GGSixRCKC1IIIFive
import CFSG.LocalAnalysis.StandardType.GGSixAutKFlatIVQuot
import CFSG.LocalAnalysis.StandardType.GGSixUnitaryTwoInnerDiag
import CFSG.LocalAnalysis.StandardType.GGSixRCKC1IIIUnitaryRecognition
import CFSG.LocalAnalysis.StandardType.GGSixRCKC1IIpAction
import CFSG.LocalAnalysis.StandardType.GGSixRCKC1IIINativeMinus
import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeStepA
import CFSG.LocalAnalysis.StandardType.GGSixRCKC1IIITwE6Prime
import CFSG.LocalAnalysis.StandardType.GGSixRCKC1IIINativeOrthogonalPlus
import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeF1POmegaPlus
import CFSG.LocalAnalysis.StandardType.ClassicalPosition.StepA2
import CFSG.LocalAnalysis.StandardType.ClassicalPosition.BlockDegreeOneGFTwo
import CFSG.LocalAnalysis.StandardType.ClassicalPosition.FEOmegaFourMinusPOmegaPlus
import CFSG.LocalAnalysis.StandardType.ClassicalPosition.FEPOmegaPlus
import CFSG.LocalAnalysis.StandardType.GGSixRCKC1IIpFPOmegaPlusFixed
import CFSG.LocalAnalysis.StandardType.GGSixRCKC1IIpBlockFixed
import CFSG.LocalAnalysis.StandardType.GGSixRCKC1IIIUnitaryFour
import CFSG.LocalAnalysis.StandardType.GGSixRCKC1IIIUnitaryOrthBlock
import CFSG.LocalAnalysis.StandardType.TableC.OrthGram
import CFSG.LocalAnalysis.StandardType.GGSixD4TwoFixedFive
import CFSG.LieType.Universal.Spin.Action
import CFSG.LieType.Universal.Spin.Forms
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeFamInBCDCharTwo

public section

namespace CFSG.StandardType.RCKC1

open CFSG CFSG.Assembly CFSG.Blueprint CFSG.Open CFSG.StandardType
  CFSG.StandardType.GGK0MarkedArithmetic

section Certificates


theorem twistedE6_three_component_models_of_five_dvd
    {S : Type} [Group S] [Finite S] {lab : LargeEvenLabel}
    (hlab : lab ∈ [⟨.twA, 5, 1⟩, ⟨.D, 4, 1⟩, ⟨.twD, 5, 1⟩, ⟨.triD4, 0, 1⟩, ⟨.twA, 4, 1⟩, ⟨.twA, 2, 3⟩])
    (hLabel : GGHasLabel lab S)
    (hna : ∃ a b : S, a * b ≠ b * a)
    (h5 : 5 ∣ Nat.card S) :
    LieModel S .PSU 6 2 1 ∨ LieModel S .POmegaPlus 4 2 1 ∨
      LieModel S .POmegaMinus 5 2 1 ∨ LieModel S .PSU 5 2 1 := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hlab
  rcases hlab with rfl | rfl | rfl | rfl | rfl | rfl
  ·
    have hΛ : LargeEvenInLambda2 ⟨.twA, 5, 1⟩ := by simp [LargeEvenInLambda2]
    have hc : markChar ⟨.twA, 5, 1⟩ = 2 := by decide
    have hM := markedModel_of_label hΛ hna hLabel
    have hLie := lieModel_of_markedModel hc hM
    exact Or.inl (by simpa [markTag, markRank, markDeg] using hLie)
  ·
    have hΛ : LargeEvenInLambda2 ⟨.D, 4, 1⟩ := by simp [LargeEvenInLambda2]
    have hc : markChar ⟨.D, 4, 1⟩ = 2 := by decide
    have hM := markedModel_of_label hΛ hna hLabel
    have hLie := lieModel_of_markedModel hc hM
    exact Or.inr (Or.inl (by simpa [markTag, markRank, markDeg] using hLie))
  ·
    have hΛ : LargeEvenInLambda2 ⟨.twD, 5, 1⟩ := by simp [LargeEvenInLambda2]
    have hc : markChar ⟨.twD, 5, 1⟩ = 2 := by decide
    have hM := markedModel_of_label hΛ hna hLabel
    have hLie := lieModel_of_markedModel hc hM
    exact Or.inr (Or.inr (Or.inl (by simpa [markTag, markRank, markDeg] using hLie)))
  ·
    have hΛ : LargeEvenInLambda2 ⟨.triD4, 0, 1⟩ := by simp [LargeEvenInLambda2]
    have hc : markChar ⟨.triD4, 0, 1⟩ = 2 := by decide
    have hM := markedModel_of_label hΛ hna hLabel
    have hLie := lieModel_of_markedModel hc hM
    have hCE : ChevalleyExceptionalModel S .trialityD4 2 1 :=
      LieModel.chevalleyExceptionalModel hLie (by decide)
    have hcard : Nat.card S = ordTrialityD4 2 := by
      simpa using Timmesfeld.card_chevalleyExceptionalModel_two hCE
    have hno5 : ¬ 5 ∣ ordTrialityD4 2 := by
      simpa using CFSG.RankThree.PartTwo.Sec21.Item228Census2Proof.not_five_dvd_ordTrialityD4 (f := 1) (by norm_num)
    exact False.elim (hno5 (by simpa [hcard] using h5))
  ·
    have hΛ : LargeEvenInLambda2 ⟨.twA, 4, 1⟩ := by simp [LargeEvenInLambda2]
    have hc : markChar ⟨.twA, 4, 1⟩ = 2 := by decide
    have hM := markedModel_of_label hΛ hna hLabel
    have hLie := lieModel_of_markedModel hc hM
    exact Or.inr (Or.inr (Or.inr (by simpa [markTag, markRank, markDeg] using hLie)))
  ·
    have hΛ : LargeEvenInLambda2 ⟨.twA, 2, 3⟩ := by simp [LargeEvenInLambda2]
    have hc : markChar ⟨.twA, 2, 3⟩ = 2 := by decide
    have hM := markedModel_of_label hΛ hna hLabel
    have hLie := lieModel_of_markedModel hc hM
    have hSC : StatedClassicalModel S .PSU 3 2 3 :=
      LieModel.statedClassicalModel hLie (by decide)
    obtain ⟨-, K, hField, hFinite, hKcard, ⟨e⟩⟩ := hSC
    let : Field K := hField
    let : Finite K := hFinite
    have hUnitaryNo5 :
        ¬ 5 ∣ Nat.card (CFSG.ClassicalGroups.UnitaryFlag.unitaryPSU (CFSG.ClassicalGroups.UnitaryFlag.unitaryFieldDataOfCard (n := 3) hKcard) 3) :=
      (CFSG.RankThree.PartTwo.Sec21.Item228Census2Proof.not_five_dvd_card_unitary_three
        (CFSG.ClassicalGroups.UnitaryFlag.unitaryFieldDataOfCard (n := 3) hKcard) (by norm_num : 3 ∣ 2 ^ 3 + 1)).2
    have hEq :
        Nat.card S = Nat.card (CFSG.ClassicalGroups.UnitaryFlag.unitaryPSU (CFSG.ClassicalGroups.UnitaryFlag.unitaryFieldDataOfCard (n := 3) hKcard) 3) :=
      (Nat.card_congr e.toEquiv).trans
        (Nat.card_congr (CFSG.ClassicalGroups.UnitaryFlag.unitaryPSUEquivStated (n := 3) hKcard).toEquiv).symm
    have hno5 : ¬ 5 ∣ Nat.card S := by
      rwa [hEq]
    exact False.elim (hno5 h5)

end Certificates

section CertificatesFull


theorem component_models_of_twistedE6_compConfig
    {X : Type} [Group X] [Finite X] {n p : ℕ}
    {psi : (ggU .twistedE6 n 1).K →* X} {G0 A B1 D J L K : Subgroup X} {e : X}
    (hcfg : RCKRP.RCKCompConfig .twistedE6 n 1 psi p G0 A B1 D J L K e)
    (hrow : GGSixRCKJRow .III J) :
    LieModel (↥K ⧸ Subgroup.center ↥K) .PSU 6 2 1 ∨
    LieModel (↥K ⧸ Subgroup.center ↥K) .POmegaPlus 4 2 1 ∨
    LieModel (↥K ⧸ Subgroup.center ↥K) .POmegaMinus 5 2 1 ∨
    LieModel (↥K ⧸ Subgroup.center ↥K) .PSU 5 2 1 := by
  obtain ⟨labK, hlab, hLabel⟩ := twistedE6_compConfig_has_component_label hcfg
  obtain ⟨_, _, _, _, _, _, _, _, _, _,
    _, _, _, _, _, _, _, _, _, _,
    _, _, _, _, _, _, _, hKcomp, hJK, _⟩ := hcfg
  have hna : ∃ a b : ↥K ⧸ Subgroup.center ↥K, a * b ≠ b * a :=
    (ggQuasisimple_centerQuot hKcomp.2.2).2
  have h5 : 5 ∣ Nat.card (↥K ⧸ Subgroup.center ↥K) :=
    five_dvd_card_centerQuot_of_row_III_le hrow hJK
  exact twistedE6_three_component_models_of_five_dvd hlab hLabel hna h5

theorem k2At_or_plus_four_of_twistedE6_compConfig
    {X : Type} [Group X] [Finite X] {n p : ℕ}
    {psi : (ggU .twistedE6 n 1).K →* X}
    {G0 A B1 D J L K : Subgroup X} {e r : X} {V : Subgroup X}
    (hcfg : RCKRP.RCKCompConfig .twistedE6 n 1 psi p G0 A B1 D J L K e)
    (hrow : GGSixRCKJRow .III J)
    (hFour : FourAt J V r) (hCore : CoreCommAt J V r) (hShort : ShortAt J r) :
    K2At K V r ∨ LieModel (↥K ⧸ Subgroup.center ↥K) .POmegaPlus 4 2 1 := by
  have hmodels := component_models_of_twistedE6_compConfig hcfg hrow
  have hp3 : p = 3 :=
    prime_eq_three_of_twistedE6_compConfig n psi p G0 A B1 D J L K e hcfg
  obtain ⟨-, -, hp, hp2, hA, hBA, hDB, hDcard, hAN, -, hBNJ, hBCJ, hBcard, -, -, -,
    -, -, hJcomp, hOddJ, -, -, -, -, -, heD, hene, hKcomp, hJK, hOddK⟩ := hcfg
  obtain ⟨hBNK, d, hdD, -, hJd⟩ :=
    RCKRP.le_normalizer_and_exists_isComponentOf_of_plane
      hp hA hBA hDB hDcard hAN hBNJ hJcomp heD hene hKcomp hJK
  have hdB : d ∈ B1 := hDB hdD
  have hKperf : commutator ↥K = ⊤ := hKcomp.2.2.1
  subst p
  have hBpow : ∀ b ∈ B1, b ^ 3 = 1 := fun b hb => hA.2 b (hBA hb)
  have hd3 : d ^ 3 = 1 := hBpow d hdB
  have hunitary : ∀ m : ℕ, 4 ≤ m →
      LieModel (↥K ⧸ Subgroup.center ↥K) .PSU m 2 1 → K2At K V r := by
    intro m hm hLM
    obtain ⟨phi, hphiR, hphiK, hphiID⟩ :=
      exists_unitary_two_innerDiag_presentation hBNK hBpow hKperf hOddK hm hLM
    exact k2At_of_fixedSUBlockAt
      (fixedSUBlockAt_of_native_unitary_model hp hp2 hd3 phi hphiR hphiK
        (hBNK hdB) (hphiID d hdB) hJd hrow) hJK hFour hCore hShort
  rcases hmodels with hPSU6 | hPlus4 | hMinus5 | hPSU5
  · exact Or.inl (hunitary 6 (by norm_num) hPSU6)
  · exact Or.inr hPlus4
  · have hBab : CFSG.Open.IsElemAbelian 3 B1 := CFSG.Open.IsElemAbelian.mono hA hBA
    have hmodel : RCKRP.RCKClassicalModelIDAt .POmegaMinus K B1 :=
      rckClassicalModelIDAt_orthogonal_two_of_elemAbelian hp hp2 hBab hBNK hKperf hOddK
        hMinus5 (Or.inl ⟨rfl, by decide⟩)
    have hrank : 3 ^ 2 * Nat.card ↥(B1 ⊓ Subgroup.centralizer (J : Set X)) ≤ Nat.card B1 := by
      rw [hBCJ, hDcard]
      calc 3 ^ 2 * 3 ^ 2 = 3 ^ 4 := by ring
        _ ≤ Nat.card B1 := hBcard
    exact Or.inl (k2At_of_row_III_of_minus_modelID hp hp2 hBab hdB hBNK hrank hmodel hJd
      hrow hOddJ hOddK hJK hFour hCore hShort)
  · exact Or.inl (hunitary 5 (by norm_num) hPSU5)

open CFSG.LieType.Universal CFSG.StandardType.ClassicalPosition CFSG.StandardType.RCKRP

theorem k2At_of_native_plus_four_two
    {X : Type} [Group X] [Finite X] {K J V : Subgroup X} {d r : X}
    (phi : (ggU .POmegaPlus 4 1).K →* X)
    (hphiR : phi.range = K)
    (hphiK : phi.ker ≤ Subgroup.center (ggU .POmegaPlus 4 1).K)
    (hd3 : d ^ 3 = 1)
    (hdID : GGPsiInnerDiag (ggU .POmegaPlus 4 1).D phi d)
    (hJcomp : CFSG.Assembly.IsComponentOf J (K ⊓ Subgroup.centralizer {d}))
    (hrow : GGSixRCKJRow .III J)
    (hOddJ : Odd (Nat.card (Subgroup.center ↥J)))
    (hOddK : Odd (Nat.card (Subgroup.center ↥K)))
    (hJK : J ≤ K)
    (hFour : FourAt J V r) (hCore : CoreCommAt J V r) (hShort : ShortAt J r) :
    K2At K V r := by
  obtain ⟨s, -, hsodd, ε, hε, J', hJe, hJmap⟩ :=
    rckF1_POmegaPlus (p := 3) (k := 1) (f := 1)
      Nat.prime_three (by decide) hd3 (by decide) phi hphiR hphiK hdID hJcomp
  let j := Spin.spinMatrix (Spin.quadPlus 4 (GaloisField 2 1))
  have hSU : ∀ a ∈ ({j s} : Set (GL (Fin 4 ⊕ Fin 4) (GaloisField 2 1))), a ∈ j.range := by
    intro a ha
    rw [Set.mem_singleton_iff] at ha
    exact ⟨s, ha.symm⟩
  have hS : ∀ a ∈ ({j s} : Set (GL (Fin 4 ⊕ Fin 4) (GaloisField 2 1))),
      ∀ b ∈ ({j s} : Set (GL (Fin 4 ⊕ Fin 4) (GaloisField 2 1))), Commute a b := by
    intro a ha b hb
    rw [Set.mem_singleton_iff] at ha hb
    subst a
    subst b
    exact Commute.refl _
  have hoddS : ∀ a ∈ ({j s} : Set (GL (Fin 4 ⊕ Fin 4) (GaloisField 2 1))),
      Odd (orderOf a) := by
    intro a ha
    rw [Set.mem_singleton_iff] at ha
    subst a
    exact hsodd
  have hrow' : GGSixRCKJRow .III (J'.map phi) := by rw [hJmap]; exact hrow
  obtain ⟨e, he, heε, hcase⟩ :=
    exists_isPrimIdemIn_of_isPrimAdjIdemIn_POmegaPlus 1 1 _ hSU hS hε
  rcases hcase with rfl | ⟨hne, hpair, hεeq⟩
  ·
    have hadj : formAdj (RingHom.id (GaloisField 2 1))
        (LinearMap.toMatrix₂' (GaloisField 2 1)
          (QuadraticMap.polarBilin (Spin.quadPlus 4 (GaloisField 2 1)))) e = e :=
      hε.2.2.2.1
    by_cases hdeg2 : blockDegree (Algebra.adjoin (GaloisField 2 1)
        (Units.val '' ({j s} : Set (GL (Fin 4 ⊕ Fin 4) (GaloisField 2 1))))) e < 2
    ·
      have hnm : ¬ (e.rank = 4 ∧ ∀ x y : Fin 4 ⊕ Fin 4 → GaloisField 2 1,
          e.mulVec x = x → e.mulVec y = y → Spin.quadPlus 4 (GaloisField 2 1) x = 0 →
          Spin.quadPlus 4 (GaloisField 2 1) y = 0 →
          QuadraticMap.polar (Spin.quadPlus 4 (GaloisField 2 1)) x y = 0 →
          ¬ LinearIndependent (GaloisField 2 1) ![x, y]) := by
        rintro ⟨hrank, hminus⟩
        have hFE := ggSixLSevenFieldExtCase_omegaFourMinus_POmegaPlus
          4 (GaloisField 2 1) (by decide) 1 (GaloisField.card 2 1 (by decide))
          phi hphiK _ hSU hS hoddS hε hJe hdeg2 hrank hminus
        exact (not_fieldExtCase_of_row_III hrow' (by decide)) hFE
      obtain ⟨-, hdim, hLie⟩ :=
        parameters_of_row_III_of_fixed_plus_block (k := 1) (f := 1) (by decide)
          phi hphiK _ hSU hS hoddS he hadj hdeg2 hnm hJe hrow'
      have hEq : J' = (glBlockCentralizer j
          ({j s} : Set (GL (Fin 4 ⊕ Fin 4) (GaloisField 2 1))) e :
            Subgroup (ggU .POmegaPlus 4 1).K) :=
        eq_glBlockCentralizer_of_finrank_six_POmegaPlus (k := 1) (f := 1)
          _ hSU hS hoddS he hadj hdeg2 hJe hdim
      have hse : (j s : Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) (GaloisField 2 1)) * e = e :=
        mul_eq_self_of_blockDegree_lt_two_gf2 he hdeg2
      have hblock := blockOn_glBlockCentralizer_of_mul_eq_self j he hse
      have hact : (fun (u : spinGroup (Spin.quadPlus 4 (GaloisField 2 1))) v =>
          (j u : Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) (GaloisField 2 1)).mulVec v) =
          fun u v => Spin.spinAction (Spin.quadPlus 4 (GaloisField 2 1)) u v := by
        funext u v
        exact Spin.spinMatrix_mulVec _ u v
      have hJ'eq' : J' = (glBlockCentralizer j
          ({j s} : Set (GL (Fin 4 ⊕ Fin 4) (GaloisField 2 1))) e :
            Subgroup (ggU .POmegaPlus 4 1).K) := hEq
      have hblock' : BlockOn (fun u v => Spin.spinAction (Spin.quadPlus 4 (GaloisField 2 1)) u v)
          (LinearMap.range (Matrix.toLin' e)) (LinearMap.ker (Matrix.toLin' e)) J' := by
        rw [hact] at hblock
        exact hJ'eq'.symm ▸ hblock
      have hQdet : IsUnit (LinearMap.toMatrix₂' (GaloisField 2 1)
          (QuadraticMap.polarBilin (Spin.quadPlus 4 (GaloisField 2 1)))).det :=
        CFSG.StandardType.TableC.polarGram_isUnit_det _
          (Spin.nondegenerate_polarBilin_quadPlus 4 (GaloisField 2 1))
      have horth := polar_eq_zero_of_formAdj_eq_self
        (Spin.quadPlus 4 (GaloisField 2 1)) hQdet he.2.1 hadj
      have hLieJ : LieModel (↥J ⧸ Subgroup.center ↥J) .PSU 4 2 1 := by
        rwa [hJmap] at hLie
      exact k2At_of_omegaSixEmbed_shortAt_psu_four hOddJ hOddK hFour hCore hLieJ hShort
        (Or.inl ⟨4, phi, LinearMap.range (Matrix.toLin' e), LinearMap.ker (Matrix.toLin' e),
          J', hphiR, hphiK, hblock', hJmap, horth, hdim⟩)
    · by_cases hdeg4 : blockDegree (Algebra.adjoin (GaloisField 2 1)
          (Units.val '' ({j s} : Set (GL (Fin 4 ⊕ Fin 4) (GaloisField 2 1))))) e < 4
      ·
        exact k2At_of_fixedOrthBlockAt
          (fixedOrthBlockAt_of_binary_plus_selfDualTwo (k := 1) phi hphiR hphiK _
            hSU hS hoddS he hadj (by omega) hdeg4 hJe hJmap) hJK hFour hCore hShort
      ·
        have hFE := ggSixLSevenFieldExtCase_POmegaPlus
          4 (GaloisField 2 1) (by decide) 1 (GaloisField.card 2 1 (by decide))
          phi hphiK _ hSU hS hoddS hε hJe he heε (Or.inl ⟨rfl, by omega⟩)
        exact (not_fieldExtCase_of_row_III hrow' (by decide) hFE).elim
  ·
    by_cases hdeg2 : blockDegree (Algebra.adjoin (GaloisField 2 1)
        (Units.val '' ({j s} : Set (GL (Fin 4 ⊕ Fin 4) (GaloisField 2 1))))) e < 2
    · exact (false_of_row_III_of_dualPair_plus_block (k := 1) (f := 1) (by decide)
        phi hphiK (j s) ⟨s, rfl⟩ hsodd he hpair hεeq hdeg2 hJe hrow').elim
    · have hFE := ggSixLSevenFieldExtCase_POmegaPlus
        4 (GaloisField 2 1) (by decide) 1 (GaloisField.card 2 1 (by decide))
        phi hphiK _ hSU hS hoddS hε hJe he heε (Or.inr ⟨hne, by omega⟩)
      exact (not_fieldExtCase_of_row_III hrow' (by decide) hFE).elim

theorem k2At_of_twistedE6_compConfig
    {X : Type} [Group X] [Finite X] {n p : Nat}
    {psi : (ggU .twistedE6 n 1).K →* X}
    {G0 A B1 D J L K : Subgroup X} {e r : X} {V : Subgroup X}
    (hcfg : RCKRP.RCKCompConfig .twistedE6 n 1 psi p G0 A B1 D J L K e)
    (hrow : GGSixRCKJRow .III J)
    (hFour : FourAt J V r) (hCore : CoreCommAt J V r) (hShort : ShortAt J r) :
    K2At K V r := by
  rcases k2At_or_plus_four_of_twistedE6_compConfig hcfg hrow hFour hCore hShort with
    hK2 | hLM
  · exact hK2
  ·
    have hp3 : p = 3 :=
      prime_eq_three_of_twistedE6_compConfig n psi p G0 A B1 D J L K e hcfg
    obtain ⟨-, -, hp, -, hA, hBA, hDB, hDcard, hAN, -, hBNJ, hBCJ, -, -, -, -,
      -, -, hJcomp, hOddJ, -, -, -, -, -, heD, hene, hKcomp, hJK, hOddK⟩ := hcfg
    obtain ⟨hBNK, d, hdD, -, hJd⟩ :=
      le_normalizer_and_exists_isComponentOf_of_plane
        hp hA hBA hDB hDcard hAN hBNJ hJcomp heD hene hKcomp hJK
    have hdB : d ∈ B1 := hDB hdD
    have hd3 : d ^ 3 = 1 := by
      have hdp : d ^ p = 1 := hA.2 d (hBA hdB)
      rwa [hp3] at hdp
    have hdK : d ∈ Subgroup.normalizer (K : Set X) := hBNK hdB
    have hdJ : d ∈ Subgroup.centralizer (J : Set X) := by
      have hd : d ∈ B1 ⊓ Subgroup.centralizer (J : Set X) := by
        rw [hBCJ]
        exact hdD
      exact hd.2
    have hKperf : commutator ↥K = ⊤ := hKcomp.2.2.1
    have h5 : 5 ∣ Nat.card (↥J ⧸ Subgroup.center ↥J) :=
      five_dvd_card_centerQuot_of_row_III hrow
    obtain ⟨phi, hphiR, hphiK, hphiID⟩ :=
      exists_plus_four_two_innerDiag_presentation_of_fixed_five
        hJK hKperf hOddK hLM hdK hd3 hdJ h5
    exact k2At_of_native_plus_four_two phi hphiR hphiK hd3 hphiID hJd hrow
      hOddJ hOddK hJK hFour hCore hShort

end CertificatesFull

end CFSG.StandardType.RCKC1

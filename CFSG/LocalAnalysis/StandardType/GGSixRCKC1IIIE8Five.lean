module

public import CFSG.LocalAnalysis.StandardType.GGSixRCKC1IIIE8Transport
public import CFSG.LocalAnalysis.StandardType.GGSixRCKC1IIIThreeDivisor
public import CFSG.LocalAnalysis.StandardType.GGSixRCK1416Defs
import CFSG.LocalAnalysis.StandardType.GGE8TwoFiveAssembly
import CFSG.LocalAnalysis.StandardType.GGFieldFiveE8Centralizer
import CFSG.LocalAnalysis.StandardType.GGSixRCKC1IIpAction
import CFSG.LocalAnalysis.StandardType.GGSixRCKC1IIINativeMinus
import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeStepA
import CFSG.LieType.Universal.Unitary.Clause0
import CFSG.Blueprint.LieModelAPI
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeFamInBCDCharTwo

public section
namespace CFSG.StandardType.RCKC1
open CFSG CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.StandardType




theorem lieModel_centerQuot_of_equiv_statedSU_five_four
    {Y : Type} [Group Y] {F : Type} [Field F] [Finite F]
    (hF : Nat.card F = (2 ^ 2) ^ 2) (ε : Y ≃* CFSG.Open.StatedSU 5 (2 ^ 2) F) :
    LieModel (Y ⧸ Subgroup.center Y) .PSU 5 2 2 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI := Fintype.ofFinite F
  haveI : CharP F 2 := charP_of_card_eq_prime_pow (f := 4) (by
    rw [← Nat.card_eq_fintype_card, hF]
    norm_num)
  let η := ε.trans (CFSG.LieType.Universal.Unitary.equivStatedSU (p := 2) (f := 2) hF 5).symm
  let ηq := QuotientGroup.congr _ _ η (Subgroup.map_center_eq η)
  have hadm : CFSG.Open.StatedLieAdmissible .PSU 5 2 2 := by
    norm_num [CFSG.Open.StatedLieAdmissible]
  have hSM := CFSG.LieType.Universal.Unitary.statedClassicalModel_center_quotient (p := 2) (f := 2) (n := 5) hadm hF
  exact LieModel.of_mulEquiv ηq.symm
    ((LieModel.classical_iff (by simp [classicalTags])).mpr hSM)

theorem e8_five_compConfig_exists_minus_model
    {X : Type} [Group X] [Finite X] {n : ℕ}
    {ψ : (ggU .E8 n 1).K →* X} {G₀ A B₁ D J L K : Subgroup X} {e : X}
    (hcfg : RCKRP.RCKCompConfig .E8 n 1 ψ 5 G₀ A B₁ D J L K e)
    (hrow : GGSixRCKJRow .III J) :
    ∃ N : ℕ, LieModel (↥K ⧸ Subgroup.center ↥K) .POmegaMinus N 2 1 := by
  obtain ⟨hψ, u, hu, hC, hKn, hKm⟩ := e8_compConfig_native_centralizer hcfg
  have hmodels := FieldFiveE8.e8TwoFive_centralizer_models u hu
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -,
    -, -, hKcomp, hJK, -⟩ := hcfg
  rcases hmodels with ⟨K₀, hB, N, hM⟩ | ⟨F, _, _, hF, ⟨ε⟩⟩
  · have hKeq : K.comap ψ = K₀ := FieldFiveE8.eq_of_isComponentOf_of_isFiveB hB hKn
    rw [← hKeq] at hM
    let η := (Subgroup.equivMapOfInjective (K.comap ψ) ψ hψ).trans
      (MulEquiv.subgroupCongr hKm)
    let ηq := QuotientGroup.congr _ _ η (Subgroup.map_center_eq η)
    exact ⟨N, LieModel.of_mulEquiv ηq hM⟩
  · exfalso
    let C := G₀ ⊓ Subgroup.centralizer {e}
    let η := (Subgroup.equivMapOfInjective (Subgroup.centralizer {u}) ψ hψ).trans
      (MulEquiv.subgroupCongr hC)
    have hMC : LieModel (↥C ⧸ Subgroup.center ↥C) .PSU 5 2 2 :=
      lieModel_centerQuot_of_equiv_statedSU_five_four hF (η.symm.trans ε)
    have h27 : 3 ^ 3 ∣ Nat.card (↥C ⧸ Subgroup.center ↥C) :=
      (three_pow_three_dvd_card_centerQuot_of_row_III hrow).trans
        (RCKU33.card_centerQuot_dvd (hJK.trans hKcomp.1 : J ≤ C))
    rw [CFSG.SeitzReduction.UnitaryPilot.card_of_lieModel_PSU_two_pow hMC] at h27
    exact (by decide +kernel : ¬ 3 ^ 3 ∣ CFSG.Open.ordTwistedA 4 (2 ^ 2)) h27

theorem k2At_of_e8_five_compConfig
    {X : Type} [Group X] [Finite X] {n : ℕ}
    {ψ : (ggU .E8 n 1).K →* X} {G₀ A B₁ D J L K V : Subgroup X} {e r : X}
    (hcfg : RCKRP.RCKCompConfig .E8 n 1 ψ 5 G₀ A B₁ D J L K e)
    (hrow : GGSixRCKJRow .III J) (hFour : FourAt J V r)
    (hCore : CoreCommAt J V r) (hShort : ShortAt J r) : K2At K V r := by
  obtain ⟨N, hM⟩ := e8_five_compConfig_exists_minus_model hcfg hrow
  obtain ⟨-, -, hp, hp2, hA, hBA, hDB, hDcard, hAN, -, hBNJ, hBCJ, hBcard, -, -, -,
    -, -, hJcomp, hOddJ, -, -, -, -, -, heD, he1, hKcomp, hJK, hOddK⟩ := hcfg
  obtain ⟨hBNK, d, hdD, -, hJd⟩ := RCKRP.le_normalizer_and_exists_isComponentOf_of_plane
    hp hA hBA hDB hDcard hAN hBNJ hJcomp heD he1 hKcomp hJK
  have hdB : d ∈ B₁ := hDB hdD
  have hBab : CFSG.Open.IsElemAbelian 5 B₁ := CFSG.Open.IsElemAbelian.mono hA hBA
  have hmodel : RCKRP.RCKClassicalModelIDAt .POmegaMinus K B₁ :=
    rckClassicalModelIDAt_orthogonal_two_of_elemAbelian hp hp2 hBab hBNK hKcomp.2.2.1 hOddK
      hM (Or.inl ⟨rfl, hM.admissible.2.2⟩)
  have hrank : 5 ^ 2 * Nat.card ↥(B₁ ⊓ Subgroup.centralizer (J : Set X)) ≤ Nat.card B₁ := by
    rw [hBCJ, hDcard]
    calc 5 ^ 2 * 5 ^ 2 = 5 ^ 4 := by ring
      _ ≤ Nat.card B₁ := hBcard
  exact k2At_of_row_III_of_minus_modelID hp hp2 hBab hdB hBNK hrank hmodel hJd hrow
    hOddJ hOddK hJK hFour hCore hShort

end CFSG.StandardType.RCKC1

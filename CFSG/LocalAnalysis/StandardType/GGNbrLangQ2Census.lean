module

public import CFSG.LocalAnalysis.StandardType.GGNbrLangQ2CensusExtract
public import CFSG.LocalAnalysis.StandardType.GGNbrLangQ2CensusRigid
public import CFSG.LocalAnalysis.StandardType.GGNbrLangQ2CensusJBounds
public import CFSG.LocalAnalysis.StandardType.GGNbrLangQ2CensusCover
public import CFSG.LocalAnalysis.StandardType.GGNbrLangQ2CensusLinear
public import CFSG.LocalAnalysis.StandardType.GGNbrLangQ2CensusFieldTwo
public import CFSG.LocalAnalysis.StandardType.GGNbrLangQ2CensusSymp
public import CFSG.LocalAnalysis.StandardType.GGNbrLangQ2CensusOmegaPlus
public import CFSG.LocalAnalysis.StandardType.GGNbrLangQ2CensusOmegaMinus
public import CFSG.LocalAnalysis.StandardType.GGNbrLangQ2CensusTwA
public import CFSG.LocalAnalysis.StandardType.GGNbrLangQ2CensusE6
public import CFSG.LocalAnalysis.StandardType.GGNbrLangQ2CensusE7
public import CFSG.LocalAnalysis.StandardType.GGNbrLangQ2CensusE8
public import CFSG.LocalAnalysis.StandardType.GGNbrLangQ2CensusF4
public import CFSG.LocalAnalysis.StandardType.GGNbrLangQ2CensusTwE6
public import CFSG.LocalAnalysis.StandardType.GGNbrLangQ2CensusSmall
public import CFSG.LocalAnalysis.StandardType.GGNbrLangQ1Holds
public import CFSG.LocalAnalysis.StandardType.GGFieldCaseTableBIrred

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly


theorem q2c_rLevel_all : Q2CensusRLevel (fun _ => True) (fun _ => True) := by
  have h1 := q2c_rLevel_linear.or q2c_rLevel_fieldTwo
  have h2 := h1.or q2c_rLevel_symplectic
  have h3 := h2.or q2c_rLevel_orthogonalPlus
  have h4 := h3.or q2c_rLevel_orthogonalMinus
  have h5 := h4.or q2c_rLevel_twA
  have h6 := h5.or q2c_rLevel_E6
  have h7 := h6.or q2c_rLevel_E7
  have h8 := h7.or q2c_rLevel_E8
  have h9 := h8.or q2c_rLevel_F4
  have h10 := h9.or q2c_rLevel_twE6
  have h11 := h10.or q2c_rLevel_small
  refine Q2CensusRLevel.mono ?_ (fun _ _ => trivial) h11
  intro lab hΛ _
  obtain ⟨tag, rank, n⟩ := lab
  have hn : 1 ≤ n := hΛ.1
  cases tag <;> simp <;> omega

private theorem q2c_census_narrowed :
    ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G),
      GGConfig p B Bs x L D J → GGInnerDiagOn Bs L →
        ∀ (hN : Bs ≤ Subgroup.normalizer (J : Set G)) (d : ℕ) (K : Type) [Field K] [Finite K]
          (n : ℕ) (hKc : Nat.card K = 2 ^ n)
          (θ : ↥J ⧸ Subgroup.center ↥J ≃* LargeEvenProj (LargeEvenSLGroup (Fin d) K)),
          p ∣ d → p ∣ Nat.card K - 1 →
          ∃ kind : Q2RowKind,
            GGInnerDiagOnLab (fun p lab => q2RowFits kind p d (Nat.card K) lab) p Bs L := by
  intro G _ _ p B Bs x L D J hcfg hInner hN d K _ _ n hKc θ hpd hpq
  obtain ⟨lab, hmark⟩ := q2c_extract hcfg hInner
  have hp : p.Prime := hcfg.tableB_facts.1
  have hp2 : p ≠ 2 := hcfg.1.2.2.2.2.2.1.2.1
  have hJ : GGInnerDiagOn Bs J := ggBstarInnerDiagJInput_holds G p B Bs x L D J hcfg hInner
  have hd : 3 ≤ d :=
    q2c_three_le_d hp hp2 (largeEvenMarking_mono (fun _ _ _ _ _ _ _ => trivial) hJ) θ hpd
  have hn : 2 ≤ n := by
    by_contra hlt
    rcases (by omega : n = 0 ∨ n = 1) with rfl | rfl
    · have h1 : Nat.card K = 1 := by simpa using hKc
      have h2 : 1 < Nat.card K := Finite.one_lt_card
      omega
    · exact hp.not_dvd_one (by simpa [hKc] using hpq)
  have hpm : p ∣ 2 ^ n - 1 := by rw [← hKc]; exact hpq
  obtain ⟨hlow, hup⟩ := q2c_Jbounds hcfg hJ hN hd hn hpd hpm hKc θ
  obtain ⟨kind, -, hfit⟩ :=
    q2c_cover hcfg hmark hN hd hn hpd hpm hlow hup hKc θ q2c_rLevel_all trivial
  rw [← hKc] at hfit
  refine ⟨kind, ?_⟩
  refine largeEvenMarking_mono ?_ hmark
  rintro lab' R _ I F θ' ⟨hl, hs, hN', hb⟩
  exact ⟨hl ▸ hfit, hs, hN', hb⟩

theorem q2ResidualCensusInput_holds : Q2ResidualCensusInput := by
  intro G _ _ p B Bs x L D J hcfg hInner hN d K _ _ θ hpd hpq
  have hp : p.Prime := hcfg.tableB_facts.1
  have hp2 : p ≠ 2 := hcfg.1.2.2.2.2.2.1.2.1
  have hJ : GGInnerDiagOn Bs J := ggBstarInnerDiagJInput_holds G p B Bs x L D J hcfg hInner
  obtain ⟨-, m, -, hK⟩ :=
    q2c_card_two_pow hp hp2 (largeEvenMarking_mono (fun _ _ _ _ _ _ _ => trivial) hJ) θ hpd hpq
  exact q2c_census_narrowed G p B Bs x L D J hcfg hInner hN d K m hK θ hpd hpq

end CFSG.StandardType

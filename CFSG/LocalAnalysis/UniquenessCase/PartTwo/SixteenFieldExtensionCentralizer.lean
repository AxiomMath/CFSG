module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC165Bar
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenFieldExtensionNormalizer
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenFieldExtensionStabilizer
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC23Unique
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenFiveTen
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenInputs
import CFSG.LocalAnalysis.UniquenessCase.UC6S846c
public import CFSG.GH74.GLS.Stage2.Final.ModelOrd
public import CFSG.LocalAnalysis.AGLEmbedding.JStarReducedDefs
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanCaseTwoCMSection
public import CFSG.LocalAnalysis.AGLEmbedding.ResidualTools
public import CFSG.LocalAnalysis.GL83PartI.I713.Basic
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotMainGraphOmegaMinusPiecesEmbed
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotMainGraphOmegaMinusPiecesOrders
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotLeviFactPiece
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs16c
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC165ExclDirect
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC56Norm
public import CFSG.RankThree.PartOne.KC.OrthogonalEvenMinusExtraction

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem sp4_centralizer_ne_bot_of_field_extension
    (D : Data G) (hSg : UC6S846.SigmaStd D)
    (h61 : UC6.R6_1 D) (h127 : R127 D)
    {V₀ V : Subgroup G} (h125 : Hyp125 D V₀ V)
    (hsmall : mSub V₀ ≤ 2)
    {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 4 ∨ Nat.card K = 8)
    {p : ℕ} (hpK : p = Nat.card K - 1) (hpσ : p ∈ D.sig)
    (H : Subgroup (MulAut (Vtil V₀ V h125.isElemAbelian)))
    (hHA : H ≤ Mbar D.M V₀ V h125.isElemAbelian)
    (hHn : Mbar D.M V₀ V h125.isElemAbelian ≤
      normalizer (H : Set (MulAut (Vtil V₀ V h125.isElemAbelian))))
    (hcomm : commSub ⊤ H = ⊤)
    (hreal : (FFModel.nat (StatedSp 2 K)).Realizes H ⊤ (fixV H)) :
    Mbar D.M V₀ V h125.isElemAbelian ⊓
      centralizer (H : Set (MulAut (Vtil V₀ V h125.isElemAbelian))) ≠ ⊥ := by
  classical
  have hpPrime : p.Prime := by
    rcases hK with h4 | h8
    · rw [hpK, h4]; norm_num
    · rw [hpK, h8]; norm_num
  have hp3 : 3 ≤ p := by
    rcases hK with h4 | h8 <;> omega
  have hp2 : p ≠ 2 := by omega
  have hcardV₀ : Nat.card V₀ = 2 ^ mSub V₀ :=
    card_eq_two_pow_mSub h125.pairFacts.elemAbelian₀.isPGroup
  have hV0le4 : Nat.card V₀ ≤ 4 := by
    rw [hcardV₀]
    calc 2 ^ mSub V₀ ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) hsmall
      _ = 4 := by norm_num
  obtain ⟨E, hEM, hEel, hEcard⟩ :=
    UC6S846.exists_elemAbelian_card_of_le_pRank (M := D.M) (p := p) (k := 3)
      hpPrime (hSg.three_le p hpσ)
  let P : Subgroup ↥D.M := E.subgroupOf D.M
  have hPcard : Nat.card P = p ^ 3 := by
    dsimp only [P]
    calc Nat.card (E.subgroupOf D.M) = Nat.card E :=
          Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEM).toEquiv
      _ = p ^ 3 := hEcard
  have hPel : IsElemAbelian p P := hEel.subgroupOf D.M
  have hMst : D.M ≤ stabTil V₀ V :=
    le_stabTil h125.pairFacts.le_normalizer h125.pairFacts.le_normalizer₀
  let alpha : ↥D.M →* MulAut (Vtil V₀ V h125.isElemAbelian) :=
    barHom V₀ V h125.isElemAbelian hMst
  have hrange : alpha.range = Mbar D.M V₀ V h125.isElemAbelian := by
    dsimp only [alpha, Mbar]
    exact range_barHom V₀ V h125.isElemAbelian hMst
  have hPmapA : P.map alpha ≤ Mbar D.M V₀ V h125.isElemAbelian := by
    rw [← hrange]
    rintro _ ⟨x, -, rfl⟩
    exact MonoidHom.mem_range.mpr ⟨x, rfl⟩
  have hPmapP : IsPGroup p (P.map alpha) := hPel.isPGroup.map alpha
  by_contra hcent
  have hPmapH : P.map alpha ≤ H :=
    pSubgroup_le_of_sp4_natural_of_centralizer_eq_bot
      (W := Vtil V₀ V h125.isElemAbelian) (A := Mbar D.M V₀ V h125.isElemAbelian)
      (H := H) (K := K) (p := p)
      (s15_Infra_vtil_sq_eq_one V₀ V h125.isElemAbelian)
      hHA hHn hcomm hK hpK hreal hcent (P.map alpha) hPmapA hPmapP
  have hHrange : H ≤ alpha.range := by
    rw [hrange]
    exact hHA
  have hStab : ∀ w : Vtil V₀ V h125.isElemAbelian, ∃ B : Subgroup ↥D.M,
      IsPGroup p B ∧ IsElemAbelian p B ∧ ¬ IsCyclic ↥B ∧
        ∀ b ∈ B, alpha b w = w :=
    exists_isElemAbelian_not_isCyclic_fixing_of_nat_realizes
      (M := ↥D.M) (V := Vtil V₀ V h125.isElemAbelian) (K := K)
      (s15_Infra_vtil_sq_eq_one V₀ V h125.isElemAbelian)
      alpha H hHrange hreal hK p hpK P hPel hPcard hPmapH
  have hU : ∀ w ∈ V, w ≠ 1 →
      UniqueMax D.M (D.M ⊓ centralizer ({w} : Set G)) := by
    intro w hwV hw1
    by_cases hw0 : w ∈ V₀
    ·
      exact c23_uniqueMax_of_mem_v0 D h61 hV0le4 h125.pairFacts.le_normalizer₀
        hpPrime hp3 hpσ hEM hEel hEcard hw0 hw1
    ·
      let x : IntMod V h125.isElemAbelian := IntMod.mk h125.isElemAbelian ⟨w, hwV⟩
      let wbar : Vtil V₀ V h125.isElemAbelian := mkTil V₀ V h125.isElemAbelian x
      obtain ⟨B, hBp, -, hBnc, hBfix⟩ := hStab wbar
      let Bg : Subgroup G := B.map D.M.subtype
      have hBgP : IsPGroup p Bg := hBp.map D.M.subtype
      have hBgnc : ¬ IsCyclic ↥Bg := by
        intro hcyc
        exact hBnc ((Subgroup.equivMapOfInjective B D.M.subtype
          D.M.subtype_injective).isCyclic.2 hcyc)
      have hBgCElt : Bg ≤ F11.CElt D.M V₀ w := by
        intro b hb
        obtain ⟨b0, hb0, rfl⟩ := Subgroup.mem_map.mp hb
        refine ⟨b0.2, h125.pairFacts.le_normalizer₀ b0.2, ?_⟩
        have hfix : barHom V₀ V h125.isElemAbelian hMst b0
            (mkTil V₀ V h125.isElemAbelian x) = mkTil V₀ V h125.isElemAbelian x := by
          simpa only [alpha, wbar] using hBfix b0 hb0
        have hdisp := (barHom_fix_iff V₀ V h125.isElemAbelian hMst b0 x).1 hfix
        simpa only [Subgroup.subtype_apply, x, IntMod.mk, IntMod.val] using hdisp
      exact c23_uniqueMax_of_le_cElt D h61
        (Hyp125.hyp11 h127 h125) hV0le4 hpPrime hp2 hpσ hBgP hBgnc hwV hw0 hBgCElt
  have hTI : CFSG.CGT.Timmesfeld75.IsTI V :=
    s15_FiveTen_isTI_of_uniqueMax D h125.isElemAbelian
      h125.pairFacts.le_normalizer hU
  exact (r129_1_of_r127 D h127) V₀ V h125 hTI

end CFSG.LocalAnalysis.UniquenessCase.PartTwo

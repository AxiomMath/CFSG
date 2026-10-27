module

public import CFSG.LocalAnalysis.UniquenessCase.UCFront09b
public import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoDefs
import CFSG.RankThree.GroupTheory.SteinbergBMCrossPrimeLocalCore
import CFSG.LocalAnalysis.UniquenessCase.UCFront09R912A5
import CFSG.LocalAnalysis.UniquenessCase.UCFront09R93c
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC8R95S2A
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC8R95S2B
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC8R95S2C
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC8R95B0Z
public import CFSG.LocalAnalysis.UniquenessCase.UCKInputs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.F09

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup
open CFSG.Blueprint (LieModel)
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem r95_I_odd_index (hK461 : UCK.K461)
    (hSch : CFSG.AGLEmbedding.KFactCatalogSchreier) {D : Data G} {Y H D₃ : Subgroup G}
    (hyp : Hyp91 D Y H D₃) (hH : H ≠ ⊤) (hX : LieModel (BarO3 (Opp 3 Y)) .PSL 3 2 1) :
    ¬ 2 ∣ (I9 H ⊓ D.M).relIndex (I9 H) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hXY : Opp 3 Y ≤ Y := opp_le_self 3 Y
  have hXH : Opp 3 Y ≤ H := hXY.trans hyp.2.1.1
  have hHK : CFSG.Open.IsKGroup ↥H := CFSG.Open.IsKProper.isKGroup D.standing.kProper H hH
  have hXK : CFSG.Open.IsKGroup ↥(Opp 3 Y) := CFSG.Open.IsKGroup.of_le hHK hXH
  have hKG : CFSG.Open.IsKGroup ↥(I9 H ⊔ Opp 3 Y) :=
    CFSG.Open.IsKGroup.of_le hHK (sup_le (map_subtype_le _) hXH)
  have hE9 := not_hasE9_opp hyp
  have hDU : D₃ ∈ CFSG.LocalAnalysis.RankThreeUC.uniqueSet D.M :=
    hyp.1.2.2 D₃ (hyp.2.2.1.trans hXY) hyp.2.2.2
  have hCZ : centralizer (D₃ : Set G) ≤ D.M := (centralizer_le_normalizer _).trans
    (CFSG.LocalAnalysis.RankThreeUC.normalizer_le_of_mem_uniqueSet D.maxLocal hDU)
  have hHI : H ≤ normalizer (I9 H : Set G) :=
    CFSG.RankThree.GroupTheory.SteinbergBM.le_normalizer_inSubgroup_pPrimeCore 3 H
  have hI3 : ¬ 3 ∣ Nat.card (I9 H) := (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).1
    (CFSG.RankThree.GroupTheory.SteinbergBM.coprime_card_inSubgroup_pPrimeCore H)
  have hL32top : HasL32Quot (⊤ : Subgroup (BarO3 (Opp 3 Y))) :=
    ⟨BarO3 (Opp 3 Y), inferInstance,
      (Subgroup.topEquiv : ↥(⊤ : Subgroup (BarO3 (Opp 3 Y))) ≃* BarO3 (Opp 3 Y)).toMonoidHom,
      (Subgroup.topEquiv : ↥(⊤ : Subgroup (BarO3 (Opp 3 Y))) ≃* BarO3 (Opp 3 Y)).surjective,
      hX⟩
  have hX3 : ¬ IsPGroup 3 (BarO3 (Opp 3 Y)) := fun h =>
    r95_gB_not_three_group h (E := ⊤) hL32top
  have hKperf : ⁅Opp 3 Y, Opp 3 Y⁆ = Opp 3 Y :=
    Subgroup.isPerfect_iff.mp (isPerfect_opp hE9 hX3)
  have hKgen : ∀ B : Subgroup G, B ≤ Opp 3 Y → Opp 3 Y ≤ normalizer (B : Set G) →
      D₃ ≤ B → B = Opp 3 Y := fun B hBX hBn hDB =>
    eq_opp_of_normal hSch hXK hE9 hX3 hyp.2.2.1 hyp.2.2.2 hBX hBn hDB
  obtain ⟨hS, hnab⟩ := isSimpleGroup_barO3 hSch hXK hE9 hX3
  intro heven
  obtain ⟨U, W, hUO, hUK, hWU, hUW, hWK, hWne, hWmax, hcomm, hev⟩ :=
    r95s_exists_min_even hSch hKG hyp.2.2.1 hyp.2.2.2 (hXY.trans hyp.1.1) hCZ hKperf hKgen
      (hXH.trans hHI) hI3 heven
  obtain ⟨hch, hfix⟩ := r95s_chief_factor_two hyp.2.2.1 hyp.2.2.2 (hXY.trans hyp.1.1) hCZ
    (fun h => hI3 (h.trans (Subgroup.card_dvd_of_le hUO))) hUK hWU hUW hWK hWne hWmax hcomm hev
  obtain ⟨N, hNn, hN3, F, hF, hFin, n, hFc, hφ⟩ :=
    r95s_chief_quot_two hK461 hXK hE9 hKperf hyp.2.2.1 hyp.2.2.2 hKgen hch hfix
  haveI : N.Normal := hNn
  exact r95s_false_of_quot_sl2 hS hnab hX hN3 hFc hφ

end CFSG.LocalAnalysis.UniquenessCase.UC22.F09

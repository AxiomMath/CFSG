module

public import CFSG.LocalAnalysis.UniquenessCase.UCFront09b
public import CFSG.LocalAnalysis.UniquenessCase.UC1S4Defs462
public import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoDefs
import CFSG.RankThree.GroupTheory.SteinbergBMCrossPrimeLocalCore
import CFSG.LocalAnalysis.UniquenessCase.UCFront09R912A5
import CFSG.LocalAnalysis.UniquenessCase.UCFront09R93c
import CFSG.LocalAnalysis.UniquenessCase.UCFront09R93i
import CFSG.LocalAnalysis.UniquenessCase.UCFront09R93j

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.F09

open Subgroup
open CFSG.Blueprint (LieModel)

variable {G : Type} [Group G] [Finite G]

theorem I9_le_M_of_not_isL2 (hK461 : UCK.K461) (hK462 : UCK.K462)
    (hSch : CFSG.AGLEmbedding.KFactCatalogSchreier) {D : Data G} {Y H D₃ : Subgroup G}
    (hyp : Hyp91 D Y H D₃) (hH : H ≠ ⊤) (hX : ¬ IsPGroup 3 (BarO3 (Opp 3 Y)))
    (hL2 : ¬ ∃ p f : ℕ, LieModel (BarO3 (Opp 3 Y)) .PSL 2 p f) : I9 H ≤ D.M := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  by_contra hIM
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
  obtain ⟨N, hNn, hN3, hcases⟩ := exists_quot_cases_of_not_le hK461 hK462 hSch hKG hE9
    hyp.2.2.1 hyp.2.2.2 (hXY.trans hyp.1.1) hCZ
    (Subgroup.isPerfect_iff.mp (isPerfect_opp hE9 hX))
    (fun B hBX hBn hDB => eq_opp_of_normal hSch hXK hE9 hX hyp.2.2.1 hyp.2.2.2 hBX hBn hDB)
    (hXH.trans hHI) hI3 hIM
  obtain ⟨hS, hnab⟩ := isSimpleGroup_barO3 hSch hXK hE9 hX
  exact hL2 (exists_lieModel_of_quot_cases hS hnab hN3 hcases)

end CFSG.LocalAnalysis.UniquenessCase.UC22.F09

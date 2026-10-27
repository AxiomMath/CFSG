module

public import CFSG.LocalAnalysis.UniquenessCase.UCFront09R922A5Solv
public import CFSG.RankThree.PartTwo.KFacts.KS44OutSz
import CFSG.RankThree.S4Free.StellmacherSzAllProved
import CFSG.RankThree.S4Free.StellmacherWSz
import CFSG.LinearAlgebra.LinearGroups.OddPStableActionsSupport
public import CFSG.LocalAnalysis.UniquenessCase.UC6R2

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.F09

open CFSG.Open Subgroup
open CFSG.ABGLocalTools (IsSylowOf)

variable {G : Type} [Group G] [Finite G]

theorem le_calCGS_of_kProper
    (hKPSz : CFSG.RankThree.PartTwo.KFacts.KPSz) (hK : CFSG.Open.IsKProper G)
    (h3G : 3 ∣ Nat.card G) {V R : Subgroup G} (h3 : ¬ 3 ∣ Nat.card ↥V)
    (hVc : CFSG.QuasithinUnique.CharTwo V) (hRV : IsSylowOf 2 R V) (hR : R ≠ ⊥) :
    V ≤ UC6.calCGS R := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Nontrivial ↥R := (nontrivial_iff_ne_bot R).2 hR
  obtain ⟨W, hWc, hW1, hWn⟩ :=
    CFSG.RankThree.S4Free.Stell34.stellmacherSzAll_proved.{0, 0} ↥R hRV.isPGroup inferInstance
  have hadm : CFSG.RankThree.S4Free.IsAdmissibleHost (inclusion hRV.le) := by
    refine CFSG.RankThree.S4Free.isAdmissibleHost_of_not_three_dvd h3
      (inclusion_injective hRV.le) ?_ ?_
    · obtain ⟨Q, hQ⟩ := hRV.exists_sylow_eq_subgroupOf
      exact ⟨Q, by rw [hQ, inclusion_range]⟩
    · rw [CFSG.RankThree.S4Free.oTwo, ← CFSG.LinearGroups.pCore_eq_piCore Nat.prime_two]
      exact CFSG.QuasithinUnique.charTwo_iff_internal.1 hVc
  have hN := hWn ↥V (inclusion hRV.le) hadm
    (CFSG.RankThree.S4Free.szSections_of_kProper hKPSz hK h3G h3)
  have hCR : W.map R.subtype ≤ R := map_subtype_le W
  have heq : (W.map R.subtype).subgroupOf V = W.map (inclusion hRV.le) := by
    ext x
    simp only [mem_subgroupOf, mem_map]
    exact ⟨fun ⟨w, hw, hwx⟩ => ⟨w, hw, Subtype.ext hwx⟩,
      fun ⟨w, hw, hwx⟩ => ⟨w, hw, by rw [← hwx]; rfl⟩⟩
  have hVN : V ≤ normalizer (W.map R.subtype : Set G) :=
    (normal_subgroupOf_iff_le_normalizer (hCR.trans hRV.le)).1 (heq ▸ hN)
  refine hVN.trans ?_
  unfold UC6.calCGS
  refine le_iSup_of_le _ <| le_iSup_of_le ?_ <| le_iSup_of_le hCR <| le_iSup_of_le ?_ le_rfl
  · exact fun h => hW1 ((map_eq_bot_iff_of_injective _ R.subtype_injective).1 h)
  · rwa [Subgroup.subgroupOf, comap_map_eq_self_of_injective R.subtype_injective]

theorem I9_le_calCGS
    (hKPSz : CFSG.RankThree.PartTwo.KFacts.KPSz) {D : Data G} {Y H D₃ S : Subgroup G}
    (hY : Hyp97 D Y H D₃ S) (hR : pCoreOf 2 Y ≠ ⊥)
    (hRI : IsSylowOf 2 (pCoreOf 2 Y) (pCoreOf 2 Y ⊔ I9 H)) : I9 H ≤ UC6.calCGS (pCoreOf 2 Y) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hRH : pCoreOf 2 Y ≤ H := (CFSG.LieType.BorelTits.pCoreOf_le 2 Y).trans hY.1.2.1.1
  have hR2 := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 Y
  have h3G : 3 ∣ Nat.card G := by
    rw [← hY.1.2.2.2]
    exact Subgroup.card_subgroup_dvd_card D₃
  exact le_sup_right.trans (le_calCGS_of_kProper hKPSz D.standing.kProper h3G
    (not_three_dvd_card_sup_I9 hRH hR2) (charTwo_sup_I9 hY.2.2.1.2 hRH hR2) hRI hR)

end CFSG.LocalAnalysis.UniquenessCase.UC22.F09

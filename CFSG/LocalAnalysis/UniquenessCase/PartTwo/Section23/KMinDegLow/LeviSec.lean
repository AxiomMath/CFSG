module

public import CFSG.LocalAnalysis.UniquenessCase.UC22Defs2
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KMinDegLow.LeviData
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KMinDegLow.Section
import CFSG.LocalAnalysis.UniquenessCase.UC22P21c
public import CFSG.LocalAnalysis.UniquenessCase.UC22S20

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.MinDegLow

open CFSG.RankThree.PartTwo.Sec4.Ronan148V

variable {G : Type} [Group G]

theorem exists_leviData_of_nParamSingle
    (hSz : ∀ (X : Type) [Group X] (f : ℕ), IsSz X f → Nat.card X = CFSG.Open.ordSuzuki (2 ^ f))
    {Q : Type} [Group Q] [Finite Q] {n : ℕ} (h : NParamSingle Q n) (hn : 2 < n) :
    ∃ (T : Type) (_ : Group T) (_ : Finite T), IsSec T Q ∧ LeviData T n := by
  rcases h with hSzQ | hL2 | ⟨_, hU⟩ | ⟨_, hL⟩ | hSp4
  · exact ⟨Q, inferInstance, inferInstance, isSec_self, leviData_sz hSz hSzQ hn⟩
  · exact ⟨Q, inferInstance, inferInstance, isSec_self, leviData_l2 hL2 hn⟩
  · exact ⟨Q ⧸ Subgroup.center Q, inferInstance, inferInstance,
      isSec_of_surjective (QuotientGroup.mk' (Subgroup.center Q))
        (QuotientGroup.mk'_surjective (Subgroup.center Q)), leviData_u3 hU hn⟩
  · exact ⟨Q ⧸ Subgroup.center Q, inferInstance, inferInstance,
      isSec_of_surjective (QuotientGroup.mk' (Subgroup.center Q))
        (QuotientGroup.mk'_surjective (Subgroup.center Q)), leviData_l3 hL hn⟩
  · exact ⟨Q, inferInstance, inferInstance, isSec_self, leviData_sp4 hSp4 hn⟩

theorem exists_le_hinf_of_nParam {P : Subgroup G} {n : ℕ} (h : NParam (Hinf P) n) :
    ∃ Y : Subgroup G, Y ≤ Hinf P ∧ NParamSingle (Bar2 Y) n := by
  rcases h with hsingle | ⟨L₁, _, hL₁, _, _, _, htype⟩
  · exact ⟨Hinf P, le_rfl, hsingle⟩
  · refine ⟨L₁, hL₁.1.le, ?_⟩
    rcases htype L₁ (by simp) with h | h | ⟨rfl, h⟩
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl h))

theorem exists_leviData_sec [Finite G]
    (hSz : ∀ (X : Type) [Group X] (f : ℕ), IsSz X f → Nat.card X = CFSG.Open.ordSuzuki (2 ^ f))
    {L P : Subgroup G} (hPL : P ≤ L) {n : ℕ} (hN : NParam (Hinf P) n) (hn : 2 < n) :
    ∃ (T : Type) (_ : Group T) (_ : Finite T), IsSec T (Bar2 L) ∧ LeviData T n := by
  obtain ⟨Y, hYH, hY⟩ := exists_le_hinf_of_nParam hN
  have hYL : Y ≤ L := hYH.trans ((uc22p21c_Hinf_le P).trans hPL)
  obtain ⟨T, hTgrp, hTfin, hTsec, hTdata⟩ :=
    exists_leviData_of_nParamSingle hSz hY hn
  letI : Group T := hTgrp
  letI : Finite T := hTfin
  have hBarY_L : IsSec (Bar2 Y) ↥L := by
    have hq : IsSec (Bar2 Y) ↥Y :=
      isSec_of_surjective (QuotientGroup.mk' (CFSG.pCore 2 ↥Y))
        (QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥Y))
    have hincl : IsSec ↥Y ↥L :=
      IsSec.of_subgroup (H := Y.subgroupOf L)
        (isSec_of_mulEquiv_left (Subgroup.subgroupOfEquivOfLe hYL)
          (isSec_self (G := ↥(Y.subgroupOf L))))
    exact isSec_trans hq hincl
  have hT_L : IsSec T ↥L := isSec_trans hTsec hBarY_L
  haveI : IsSimpleGroup T := hTdata.simple
  have hnot : ¬ IsSolvable T := not_isSolvable_of_isSimpleGroup hTdata.nonab
  haveI : Fact (Nat.Prime 2) := Nat.fact_prime_two
  haveI : Group.IsNilpotent ↥(CFSG.pCore 2 ↥L) := CFSG.pCore_isNilpotent
  have hN : IsSolvable (CFSG.pCore 2 ↥L) := IsNilpotent.to_isSolvable
  exact ⟨T, hTgrp, hTfin,
    IsSec.quotient_of_isSolvable (N := CFSG.pCore 2 ↥L) hnot hN hT_L, hTdata⟩

end CFSG.LocalAnalysis.UniquenessCase.UC22.MinDegLow

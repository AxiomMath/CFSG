module

public import CFSG.LocalAnalysis.WeakClosure81.W16QDInputs
public import CFSG.LocalAnalysis.WeakClosure81.EightFiveRootRankU3
public import CFSG.ClassicalGroups.UnitaryFlag.StatedBridge
public import CFSG.LocalAnalysis.SectionRank.QTK.CentreFact.LayerPair
public import CFSG.LocalAnalysis.WeakClosure81.SevenSixteenKFacts

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Open CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag
open Subgroup

section Certified


theorem w16l_isU3Shape_of_perfect {Q : Type} [Group Q] [Finite Q] {n : ℕ}
    (hperf : commutator Q = ⊤) (hQ : IsPSUGp (Q ⧸ Subgroup.center Q) 3 n) :
    IsU3Shape Q n := by
  refine ⟨hperf, hQ, ?_⟩
  haveI : Group.IsPerfect Q := ⟨hperf⟩
  have hmodel : StatedClassicalModel (Q ⧸ Subgroup.center Q) .PSU 3 2 n :=
    CFSG.Blueprint.LieModel.statedClassicalModel_of_ne_zero (by norm_num) hQ
  have h1 : Nat.card (Subgroup.center Q) ∣
      Nat.card (CFSG.RankThree.PerfectCover.hopfMultiplier (Q ⧸ Subgroup.center Q)) :=
    CFSG.SectionRank.QTK.CentreFact.LayerPair.card_center_dvd_card_hopfMultiplier_quotient
  have h2 : Nat.card (CFSG.RankThree.PerfectCover.hopfMultiplier (Q ⧸ Subgroup.center Q)) =
      Nat.gcd 3 (2 ^ n + 1) :=
    CFSG.SectionRank.QTK.CentreFact.LayerPair.card_hopfMultiplier_psu_three hmodel
  rw [h2] at h1
  exact h1.trans (Nat.gcd_dvd_left 3 (2 ^ n + 1))

theorem w16l_exists_cover_unitarySU {Q : Type} [Group Q] [Finite Q] {n : ℕ}
    (hperf : commutator Q = ⊤) (hQ : IsPSUGp (Q ⧸ Subgroup.center Q) 3 n) :
    ∃ (F : Type) (_ : Field F) (hF : UnitaryFieldData 2 n F)
      (π : ↥(unitarySU 2 n F 3) →* Q) (ε : (Q ⧸ Subgroup.center Q) ≃* unitaryPSU hF 3),
      Function.Surjective π ∧ ∀ g, ε (QuotientGroup.mk (π g)) = unitaryProj hF 3 g := by
  haveI : Group.IsPerfect Q := ⟨hperf⟩
  obtain ⟨-, F, instField, instFinite, hFcard, ⟨e₀⟩⟩ :=
    CFSG.Blueprint.LieModel.statedClassicalModel_of_ne_zero (by norm_num) hQ
  letI : Field F := instField
  letI : Finite F := instFinite
  let hF : UnitaryFieldData 2 n F := unitaryFieldDataOfCard hFcard
  have hodd : Odd (Nat.card (Subgroup.center Q)) :=
    Odd.of_dvd_nat (show Odd 3 from ⟨1, by norm_num⟩)
      (w16l_isU3Shape_of_perfect hperf hQ).2.2
  obtain ⟨π, hπsurj, hπcomp⟩ :=
    exists_statedSU_cover_of_perfect (two_le_of_isPSUGp hQ) hFcard e₀ hodd
  refine ⟨F, instField, hF, π,
    e₀.trans (unitaryPSUEquiv hF (n := 3) (by norm_num)).symm, hπsurj, ?_⟩
  intro g
  have hε : (e₀.trans (unitaryPSUEquiv hF (n := 3) (by norm_num)).symm)
        (QuotientGroup.mk (π g)) =
      (unitaryPSUEquiv hF (n := 3) (by norm_num)).symm (QuotientGroup.mk g) := by
    rw [MulEquiv.trans_apply, hπcomp g]
  rw [hε, MulEquiv.symm_apply_eq]
  exact (unitaryPSUEquiv_unitaryProj hF (n := 3) (by norm_num) g).symm

end Certified

end CFSG.LocalAnalysis.WeakClosure81

end

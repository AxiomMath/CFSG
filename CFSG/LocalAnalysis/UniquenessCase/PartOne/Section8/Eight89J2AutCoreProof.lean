module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight89Defs
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight89KGroupBasic
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight89KJ2Normal
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight89KJ2Inner
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight89KJ2Outer

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

open Subgroup KInputs

theorem j2AutCore_holds :
    J2AutCore := by
  intro J _ _ hJ K hK S hS hN
  obtain ⟨hKq, hZ, hKalt⟩ := hK
  obtain ⟨hcard, hcenter⟩ := j2AutCore_card_center hJ
  have hKcard : Nat.card K = 1080 := by
    rw [card_eq_of_isAlt6_quot hKalt, hZ]
  have hnorm : ∀ N : Subgroup K, N.Normal → N = ⊤ ∨ N ≤ center K :=
    fun N hN => normal_eq_top_or_le_center_of_isQuasisimple hKq hN
  obtain ⟨hKN, h16⟩ := j2AutCore_comap_conj_dvd hcard hcenter K hKcard hnorm hZ S hS hN
  exact j2AutCore_eq_bot_of_comap_eq_bot hJ K hKcard S hS hN
    (j2AutCore_eq_bot_of_card_dvd_sixteen hJ K hKcard hnorm hZ _ hKN h16)

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

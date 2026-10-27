module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KStrongEmbedded72AltTen
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KStrongEmbedded72Rows
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.KInputsSolvableAltTen

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open
open CFSG.Blueprint (LieModel)
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)
open CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7


theorem kf7_altTen_case {p : ℕ} (hp : p.Prime) (hp5 : p = 5)
    {X : Type} [Group X] [Finite X] (hO : CFSG.pPrimeCore p X = ⊥)
    {L N : Subgroup X} (hLN : L.Normal) (hKL : genFittingFStar X ≤ L)
    (hshape : IsAlt ↥L 10) (hN : IsStronglyPEmbedded p N) :
    p = 5 ∧ IsAlt ↥L 10 ∧
      ∀ Y : Subgroup X, Y ≤ N → ⁅Y, Y⁆ = Y → ∀ (S : Type) [Group S],
        IsSimpleGroup S → ∀ f : ↥Y →* S, Function.Surjective f → IsAlt S 5 := by
  subst hp5
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  set K : Subgroup X := genFittingFStar X with hKdef
  obtain ⟨hKs, -, hKn, hKC, ⟨P, T, hPN, hPK, hT, hle, hne⟩⟩ := kf7_setup hp (by omega) hO hLN hKL hN
  haveI : K.Normal := hKn
  have hLsimple : IsSimpleGroup ↥L := by
    haveI : IsSimpleGroup (alternatingGroup (Fin 10)) :=
      alternatingGroup.isSimpleGroup (by simp)
    exact hshape.some.isSimpleGroup
  have hKLeqL : K = L := eq_of_le_of_normal_of_isSimpleGroup hKL hKs hLsimple
  let e : ↥K ≃* alternatingGroup (Fin 10) :=
    (MulEquiv.subgroupCongr hKLeqL).trans hshape.some
  obtain ⟨-, -, h60⟩ := altTen_alternative (X := X) hKC e T hle hne
  refine ⟨rfl, hshape, ?_⟩
  intro Y hYN hYperf S _ hS f hf
  haveI : Finite S := Finite.of_surjective f hf
  have htopY : (⊤ : Subgroup ↥Y).map Y.subtype = Y := by
    simpa using Subgroup.subgroupOf_map_subtype (H := (⊤ : Subgroup X)) (K := Y)
  have hperf : ⁅(⊤ : Subgroup ↥Y), (⊤ : Subgroup ↥Y)⁆ = ⊤ := by
    have hmap : (⁅(⊤ : Subgroup ↥Y), (⊤ : Subgroup ↥Y)⁆).map Y.subtype = Y := by
      rw [Subgroup.map_commutator, htopY, hYperf]
    have htop : (⊤ : Subgroup ↥Y).map Y.subtype = Y := htopY
    exact Subgroup.map_injective Y.subtype_injective (by rw [hmap, htop])
  exact isAlt_five_of_sectionsOrder60 hperf (h60 Y hYN hYperf) f hf

end CFSG.LocalAnalysis.UniquenessCase.UC22

end

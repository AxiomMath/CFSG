module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.CatalogModels
import CFSG.LocalAnalysis.UniquenessCase.UC22P22rm

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17.SzFive

open Subgroup CFSG.Open
open scoped Pointwise commutatorElement

section Tits

theorem phase45_false_of_tits {X : Type} [Group X] [Finite X] {L A₁ : Subgroup X}
    (hLn : L.Normal) (hLs : IsSimpleGroup L) (hLnab : ¬ IsMulCommutative L)
    (hCL : centralizer (L : Set X) = ⊥) {d : TauCeti.ValidLieTypeIndex} (hd : d.1 = .tits)
    (e : ↥L ≃* (TauCeti.CFSGIndex.lie d).Group) (hA1 : Nat.card A₁ = 31) : False := by
  haveI : L.Normal := hLn
  have hnab : ∃ a b : ↥L, a * b ≠ b * a := by
    by_contra h
    push Not at h
    exact hLnab (isMulCommutative_iff.mpr h)
  have hF : genFittingFStar X = L := UC22.uc22p22r_fstar_eq hLs hnab hCL
  obtain ⟨dd, hv⟩ := d
  simp only at hd
  subst hd
  have hR : CFSG.Blueprint.ReeTitsModel ↥L .Tits 2 1 :=
    CFSG.RankThree.PartOne.CTP.reeTitsModel_tits (S := ↥L) ⟨hv, ⟨e⟩⟩
  have hLM : UC22.F10.IsTits10 ↥L :=
    show CFSG.Blueprint.LieModel ↥L .Tits 0 2 1 from
      Or.inr (Or.inr (Or.inl ⟨rfl, by decide, hR⟩))
  have hT : UC22.F10.IsTits10 ↥(genFittingFStar X) := by
    rw [hF]
    exact hLM
  have hC : centralizer (genFittingFStar X : Set X) = ⊥ := by
    rw [hF]
    exact hCL
  have hdvd : 31 ∣ Nat.card X := by
    rw [← hA1]
    exact Subgroup.card_subgroup_dvd_card A₁
  rcases S19.k_titsOddPrimes_holds X hT hC 31 (by norm_num : Nat.Prime 31) (by norm_num) hdvd
    with h | h | h <;> omega

end Tits

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17.SzFive

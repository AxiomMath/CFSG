module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenThreeInputs
public import CFSG.GH74.Exceptional.LinearFourTwo
public import CFSG.RankThree.PartTwo.KFacts.KS14HJBasic

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

private theorem s15k_notj2_card_alt {X : Type} [Group X] {n : ℕ} [Nontrivial (Fin n)]
    (h : UC22.IsAlt X n) : Nat.card X = n.factorial / 2 := by
  obtain ⟨e⟩ := h
  rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup, Nat.card_fin]

private theorem s15k_notj2_card_center_three {X : Type} [Group X] {n : ℕ} [Nontrivial (Fin n)]
    (hq : UC22.IsAlt (X ⧸ Subgroup.center X) n)
    (hZ : Nat.card (Subgroup.center X) = 3) : Nat.card X = (n.factorial / 2) * 3 := by
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center X),
    s15k_notj2_card_alt hq, hZ]

private theorem s15k_notj2_card_lieModel_five {X : Type} [Group X] (h : IsLn X 5 1) :
    Nat.card X = 9999360 := by
  obtain ⟨-, K, instK, instFin, hKcard, ⟨e⟩⟩ :=
    CFSG.Blueprint.LieModel.statedClassicalModel h (by decide)
  letI : Field K := instK
  letI : Finite K := instFin
  have hK2 : Nat.card K = 2 := by simpa using hKcard
  calc Nat.card X
      = Nat.card (StatedProj (StatedSL 5 K)) := Nat.card_congr e.toEquiv
    _ = Nat.card (GL (Fin 5) K) :=
        Nat.card_congr
          (CFSG.GH74.Exceptional.statedProjStatedSLEquivOfCardTwo hK2 5).toEquiv
    _ = Nat.card (StatedSL 5 K) :=
        (Nat.card_congr
          ((MulEquiv.subgroupCongr
            (CFSG.GH74.Exceptional.statedSL_eq_top_of_card_two hK2 5)).trans
            Subgroup.topEquiv).toEquiv).symm
    _ = 9999360 := CFSG.Open.StatedAPI.card_statedSL_five_of_card_eq_two hK2

theorem rNotJ2_holds : RNotJ2 := by
  intro X _ hJ h
  have h0 : Nat.card X = 604800 := CFSG.RankThree.PartTwo.KFacts.KS14.card_eq_of_j2 hJ
  rcases h with h6 | hA6Z3 | h7 | hA7Z3 | h8 | hL
  · rw [s15k_notj2_card_alt h6] at h0
    norm_num at h0
  · obtain ⟨-, hZ, hq⟩ := hA6Z3
    rw [s15k_notj2_card_center_three hq hZ] at h0
    norm_num at h0
  · rw [s15k_notj2_card_alt h7] at h0
    norm_num at h0
  · obtain ⟨-, hZ, hq⟩ := hA7Z3
    rw [s15k_notj2_card_center_three hq hZ] at h0
    norm_num at h0
  · rw [s15k_notj2_card_alt h8] at h0
    norm_num at h0
  · rw [s15k_notj2_card_lieModel_five hL] at h0
    norm_num at h0

end CFSG.LocalAnalysis.UniquenessCase.PartTwo


module

public import CFSG.Quasithin.Vol2.KGFactC31RuReps
public import CFSG.Quasithin.Vol2.KGFactC31RuCoverCheck

@[expose] public section

namespace CFSG.Quasithin.KGC31.Ru

open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Certificates CFSG.Certificates.Native
  CFSG.Sporadic.RuSchreier CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.PairNative
  CFSG.Quasithin.KGC31 CFSG.Quasithin.KGC31.Native

theorem hWordsZ_letters : ∀ w ∈ hWordsZ, lettersOK 2 w = true :=
  List.all_eq_true.mp (by decide +kernel : hWordsZ.all (lettersOK 2) = true)

theorem hWordsA_letters : ∀ w ∈ hWordsA, lettersOK 2 w = true :=
  List.all_eq_true.mp (by decide +kernel : hWordsA.all (lettersOK 2) = true)

section Reps

theorem forall₂_repsZ : List.Forall₂ (Rep 4060) repsZA repsZG := by
  rw [repsZA, repsZG]
  refine List.rel_append ?_ ?_
  · rw [List.forall₂_map_left_iff, List.forall₂_map_right_iff]
    exact List.forall₂_same.2 fun w hw => rep_conjA (rep_abA (hWordsZ_letters w hw)) rep_ruZ
  · rw [List.forall₂_map_left_iff, List.forall₂_map_right_iff]
    exact List.forall₂_same.2 fun w hw => rep_wA (List.all_eq_true.mp
      (by decide +kernel : otherZW.all (lettersOK 6) = true) w hw)

theorem forall₂_repsA : List.Forall₂ (Rep 4060) repsAA repsAG := by
  rw [repsAA, repsAG]
  refine List.rel_append ?_ ?_
  · rw [List.forall₂_map_left_iff, List.forall₂_map_right_iff]
    exact List.forall₂_same.2 fun w hw => rep_conjA (rep_abA (hWordsA_letters w hw)) rep_ruA0
  · rw [List.forall₂_map_left_iff, List.forall₂_map_right_iff]
    exact List.forall₂_same.2 fun w hw => rep_abA (List.all_eq_true.mp
      (by decide +kernel : otherAW.all (lettersOK 2) = true) w hw)

end Reps

theorem ruJoin_base : (ruChainJoin.base.toList.map Fin.val) = ruJoinBase := by
  decide

theorem ruJoin_baseFaithful :
    BaseFaithful ruP ruJoinBase := by
  have h := baseFaithful_of_valid ruChainJoin_valid
  rw [ruChainJoin_sub, ← ruP_eq_sup, ruJoin_base] at h
  exact h

theorem ruJoinBase_lt : ∀ b ∈ ruJoinBase, b < 4060 := by decide

section Cover

end Cover

end CFSG.Quasithin.KGC31.Ru

end

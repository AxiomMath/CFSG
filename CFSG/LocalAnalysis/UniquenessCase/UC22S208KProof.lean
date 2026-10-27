module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S208K
import CFSG.LocalAnalysis.UniquenessCase.UC22S208KRankOne
import CFSG.LocalAnalysis.UniquenessCase.UC22S208KParab
import CFSG.LocalAnalysis.UniquenessCase.UC22S208KTorus
import CFSG.LocalAnalysis.UniquenessCase.UC22S208KRankTwo

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open Subgroup


private theorem s208k_goal_of_rankTwo_shape {X : Type} [Group X] [Finite X] {m : ℕ}
    (hodd : Odd (Nat.card (center X)))
    (hX : IsL3 X m ∨ IsSL3 X m ∨ IsSp4 X m ∨ IsU4 X m ∨ IsG2 X m ∨ Is3D4 X m ∨
      CFSG.Blueprint.LieModel X .twistedF4 0 2 m)
    {P : Subgroup X} (hP : IsParabolicTwo X P) (hPX : P ≠ ⊤) {n : ℕ} (hn : 2 < n)
    (h1 : IsL2 (Bar2 (Hinf P)) n ∨ IsSz (Bar2 (Hinf P)) n → S208kGoal P n)
    (hQ : S208kQ P n) : S208kGoal P n := by
  rcases hQ with h | h | h
  · exact h1 (Or.inl h)
  · exact h1 (Or.inr h)
  · exact (s208k_not_isSzL2Product_of_rankTwo hodd hX hP hPX (by omega) h).elim

theorem kLeviRank208_holds : KLeviRank208 := by
  intro X _ _ hqs hodd hshape P hP hPX n hn hQ
  change S208kQ P n at hQ
  change S208kGoal P n
  rcases hshape with ⟨m, hm, hX⟩ | hX | hX | hX | hX | hX | ⟨m, -, hX⟩ | hX
  · rcases hX with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact (s208k_false_of_rankOne (Or.inl h) hP hPX hQ).elim
    · exact (s208k_false_of_rankOne (Or.inr (Or.inl h)) hP hPX hQ).elim
    · exact s208k_goal_of_rankTwo_shape hodd (Or.inl h) hP hPX hn
        (s208k_goal_of_classical_rankTwo (Or.inl h) hm hP) hQ
    · exact (s208k_false_of_rankOne (Or.inr (Or.inr (Or.inl h))) hP hPX hQ).elim
    · exact s208k_goal_of_rankThree (Or.inl h) hm hP hQ
    · exact s208k_goal_of_rankTwo_shape hodd (Or.inr (Or.inr (Or.inr (Or.inl h)))) hP hPX hn
        (s208k_goal_of_classical_rankTwo (Or.inr (Or.inr (Or.inr h))) hm hP) hQ
    · exact s208k_goal_of_rankTwo_shape hodd (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))
        hP hPX hn (s208k_goal_of_isG2 h hm hP) hQ
    · exact s208k_goal_of_rankTwo_shape hodd
        (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))) hP hPX hn
        (s208k_goal_of_is3D4 h hn) hQ
    · exact s208k_goal_of_rankTwo_shape hodd
        (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))) hP hPX hn
        (s208k_goal_of_isF4 h hn) hQ
    · exact s208k_goal_of_rankTwo_shape hodd (Or.inr (Or.inr (Or.inl h))) hP hPX hn
        (s208k_goal_of_classical_rankTwo (Or.inr (Or.inr (Or.inl h))) hm hP) hQ
    · exact s208k_goal_of_rankTwo_shape hodd (Or.inr (Or.inl h)) hP hPX hn
        (s208k_goal_of_classical_rankTwo (Or.inr (Or.inl h)) hm hP) hQ
    · exact (s208k_false_of_rankOne (Or.inr (Or.inr (Or.inr h))) hP hPX hQ).elim
    · exact s208k_goal_of_rankThree (Or.inr (Or.inl h)) hm hP hQ
    · exact s208k_goal_of_rankThree (Or.inr (Or.inr h)) hm hP hQ
  · exact s208k_goal_of_rankTwo_shape hodd (Or.inr (Or.inr (Or.inr (Or.inl hX)))) hP hPX hn
      (s208k_goal_of_isU4_two hX hn) hQ
  · exact s208k_goal_of_isU5_two hX hn hQ
  · exact s208k_goal_of_isOmega8m_two hX hP hn hQ
  · exact s208k_goal_of_rankTwo_shape hodd
      (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hX)))))) hP hPX hn
      (s208k_goal_of_is3D4 hX hn) hQ
  · exact s208k_goal_of_rankTwo_shape hodd
      (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hX)))))) hP hPX hn
      (s208k_goal_of_is3D4 hX hn) hQ
  · exact (s208k_not_isQuasisimple_of_isSzL2Product hX hqs).elim
  · exact (s208k_not_isQuasisimple_of_isSU3CentralSquare hX hqs).elim

end CFSG.LocalAnalysis.UniquenessCase.UC22

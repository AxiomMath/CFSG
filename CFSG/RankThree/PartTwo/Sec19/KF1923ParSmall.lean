module

public import CFSG.RankThree.PartTwo.Sec19.KF1923ParSmallU42
public import CFSG.RankThree.PartTwo.Sec19.KF1923ParSmallLN
public import CFSG.RankThree.PartTwo.Sec19.KF1923ParSmallT6

public section

namespace CFSG.RankThree.PartTwo.Late

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo
open CFSG.Assembly.RankThreeEven (projSL projSU projSp)
open CFSG.RankThree.PartTwo.Sec19 (IsSmall194 IsTripleA6)

theorem ksm_case_both {X : Type} [Group X] (h : NoInvertingInParabolic X ∧
    NoSquareInvertingInParabolic X) :
    (IsNoncyclicOutType X → NoInvertingInParabolic X) ∧
      (¬ IsNoncyclicOutType X → NoSquareInvertingInParabolic X) :=
  ⟨fun _ => h.1, fun _ => h.2⟩

theorem ksm_case_L {X : Type} [Group X] (hnc : ¬ IsNoncyclicOutType X)
    (hsq : NoSquareInvertingInParabolic X) :
    (IsNoncyclicOutType X → NoInvertingInParabolic X) ∧
      (¬ IsNoncyclicOutType X → NoSquareInvertingInParabolic X) :=
  ⟨fun h => absurd h hnc, fun _ => hsq⟩

theorem kfPar_small {X : Type} [Group X] [Finite X]
    (hX : InK194 X)
    (hs : Nonempty (X ≃* Matrix.SpecialLinearGroup (Fin 3) (GaloisField 2 1)) ∨
      Nonempty (X ≃* projSL 3 (GaloisField 2 1)) ∨ Nonempty (X ≃* projSp 2 (GaloisField 2 1)) ∨
      Sec8.IsoGTwoEven X 1 ∨ Nonempty (X ≃* projSU 4 2 1) ∨
      Nonempty (X ≃* projSL 4 (GaloisField 2 1)) ∨ Nonempty (X ≃* projSL 5 (GaloisField 2 1)) ∨
      IsSmall194 X ∨ IsTripleA6 X ∨ Nonempty (X ≃* alternatingGroup (Fin 10))) :
    (IsNoncyclicOutType X → NoInvertingInParabolic X) ∧
      (¬ IsNoncyclicOutType X → NoSquareInvertingInParabolic X) := by
  have hq : CFSG.IsQuasisimple X := hX.1
  rcases hs with h | h | h | h | h | h | h | h | h | h
  ·
    obtain ⟨e⟩ := h
    have hN : Nat.card X = 168 := (Nat.card_congr e.toEquiv).trans ksm_card_sl_three_two
    exact ksm_case_both (ksm_both_of_map (ksm_map_of_nine (ksm_nine_of_card hN (by norm_num))))
  ·
    obtain ⟨e⟩ := h
    have hN : Nat.card X = 168 :=
      (Nat.card_congr e.toEquiv).trans CFSG.RankThree.PartTwo.Sec4.Ronan148L.card_projSL_three_two
    exact ksm_case_both (ksm_both_of_map (ksm_map_of_nine (ksm_nine_of_card hN (by norm_num))))
  ·
    exact (ksm_false_sp_four_two hq h).elim
  ·
    exact (ksm_false_g_two_two hq h).elim
  ·
    obtain ⟨e⟩ := h
    exact ksm_case_both (ksm_u42_both e)
  ·
    obtain ⟨e⟩ := h
    exact ksm_case_L (ksm_not_noncyclic_l4 e) (ksm_nsq_l4 e)
  ·
    obtain ⟨e⟩ := h
    exact ksm_case_L (ksm_not_noncyclic_l5 e) (ksm_nsq_l5 e)
  ·
    rcases h with h6 | h33
    · obtain ⟨eA6⟩ := h6
      exact ksm_case_both (ksm_both_of_map (ksm_map_of_nine
        (ksm_nine_of_nineFree (ksm_nineFree_a_six eA6))))
    · obtain ⟨eU33⟩ := h33
      exact ksm_case_both (ksm_both_of_map (ksm_map_of_nine
        (ksm_nine_of_nineFree (ksm_nineFree_u_three_three eU33))))
  ·
    exact ksm_case_both (ksm_both_of_map (ksm_tripleA6_nine h hq))
  ·
    exact ksm_case_both (ksm_both_of_map (ksm_map_of_nine (ksm_nine_A10 h)))

end CFSG.RankThree.PartTwo.Late

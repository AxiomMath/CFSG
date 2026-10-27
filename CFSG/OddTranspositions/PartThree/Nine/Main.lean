module

public import CFSG.OddTranspositions.PartThree.Nine.Statements

public section

namespace CFSG.OddTranspositions.PartThree.Nine

open CFSG.Timmesfeld.Bridge.Asc72
open CFSG.ProperTwoGeneratedCore.LocalCriterionCosetNormalizerIndex (cosetNormalizerPerm)

theorem theorem9_1_of_steps (hW : Lemma9_2Wreath) (h92 : Lemma9_2) (h93 : Lemma9_3)
    (h94 : Lemma9_4) (h95 : Lemma9_5) (h96 : Lemma9_6) (hQ : Lemma9_6Q) (h97 : Lemma9_7)
    (hF : Final9_1) : CFSG.OddTranspositions.PartThree.Theorem9_1 := by
  have key : ∀ n : ℕ, Th91Below n := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro G _ _ hlt D hC hH
      have hIH : Th91Below (Nat.card G) := ih (Nat.card G) hlt
      by_cases hwr : ∃ M : Subgroup G, CFSG.Timmesfeld.Bridge.Asc72.IsMinimalNormal M ∧
          ¬ IsSimpleGroup M
      · exact hW G D hC hH hwr
      · have hs := h92 G D hC hH fun M hM => by
          by_contra hns
          exact hwr ⟨M, hM, hns⟩
        have h3 := h93 G D hC hH hs
        obtain ⟨T⟩ : Nonempty (Sylow 2 (Halpha D hC.alpha)) := inferInstance
        obtain ⟨S, hTS⟩ := (T.isPGroup'.map (Halpha D hC.alpha).subtype).exists_le_sylow
        have h4 := h94 G D hC hH hs h3 T S hTS
        have h5 := h95 G D hC hH hs hIH h3 T S hTS h4
        have hsol : Group.IsSolvable (cosetNormalizerPerm ((S : Set G) ∩ D)).range := by
          rcases id h4 with ⟨-, -, -, h | h⟩
          · exact h
          · exact absurd h (h96 G D hC hH hs hIH h3 T S hTS h4 h5)
        obtain ⟨Q, hQ'⟩ := hQ G D hC hH hs h3 T S hTS h4 h5 hsol
        exact hF G D hC hH hs hIH h3 T S hTS h4 h5 Q hQ'
          (h97 G D hC hH hs hIH h3 T S hTS h4 h5 Q hQ')
  intro G _ _ D hC hsolv hrad hbend
  exact key (Nat.card G + 1) G (Nat.lt_succ_self _) D hC ⟨hsolv, hrad, hbend⟩

end CFSG.OddTranspositions.PartThree.Nine

module

public import CFSG.Quasithin.MS93.S38EMain
public import CFSG.Quasithin.MS93.FFMain
public import CFSG.Quasithin.H13.A5S1521b

public section

namespace CFSG.Quasithin.MS93

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank S32

theorem S38E.s38End_holds_of_d6
    (hD6 : S38E.D6Case) : S38End := by
  have halt8 : ∀ (P : Type) [Group P], IsRankTwoLie2Derived (P ⧸ Subgroup.center P) →
      (↥(alternatingGroup (Fin 8)) ≃* P) → False := by
    intro P _ hR e
    have h8 : 4 ≤ Nat.card (Fin 8) := by
      rw [Nat.card_eq_fintype_card, Fintype.card_fin]
      norm_num
    have hZ : Subgroup.center P = ⊥ :=
      center_eq_bot_of_mulEquiv e (alternatingGroup.center_eq_bot h8)
    have h20 : Nat.card (P ⧸ Subgroup.center P) = 20160 := by
      rw [card_quot_center_eq hZ, ← Nat.card_congr e.toEquiv,
        H13.card_alternatingGroup_fin 8 (by norm_num)]
      decide
    have hE := (CFSG.ComponentClassification.PSL3Four.excludes_alternating_models_stated
      (P ⧸ Subgroup.center P) (isPSL_three_two_two_of_card hR h20)).2.2 (Fin 8) (by simp)
    exact hE.false ((SmithC27.quotCenterEquivSelf hZ).trans e.symm)
  have hT : TypeFacts :=
    { g2 := fun _ _ _ _ _ _ hF hn e => card_quot_of_equiv_quasithinG2 hF hn e
      g2two := fun _ _ _ _ _ hF e => R3c2.not_isQuasisimple_quasithinG2_two hF e
      g2d := fun _ _ _ _ _ hF e => (card_quot_of_equiv_g2Derived hF e).2
      alt8 := halt8
      sl2 := fun _ _ hq hR _ _ _ _ hF e => false_of_equiv_statedSL_two hq hR hF e
      alt57 := fun _ _ hR _ hm e => false_of_equiv_alt hR hm e
      u33 := fun _ _ _ _ _ hF e => SmithC27.b42TypeU33_of_equiv hF e
      u33aut := fun _ _ _ _ _ hKX hXN hC hP => card_le_of_b42TypeU33 hKX hXN hC hP }
  have hSQ : SQTKQuot := fun _ _ _ _ _ _ hS f hf hQ =>
    H13.A5.sqtkGroup_of_surjective_quasisimple hS f hf hQ
  exact S38E.s38End_of ms14AS_holds hSQ hT S38E.sl3SecBound_holds hD6

end CFSG.Quasithin.MS93

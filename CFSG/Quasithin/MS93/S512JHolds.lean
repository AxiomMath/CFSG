module

public import CFSG.Quasithin.MS93.S512JMain
public import CFSG.Quasithin.MS93.S512LQ2
public import CFSG.Quasithin.MS93.Q2GHolds
public import CFSG.Quasithin.MS93.S512NR2
public import CFSG.Quasithin.MS93.S310QMain
public import CFSG.Quasithin.MS93.S5Q2X52Fin

public section

namespace CFSG.Quasithin.MS93

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible

namespace S512J

open S32

theorem three56ResL_holds
    (h32 : S32) (h52 : S52) (h53 : S53) (h54 : S54) (h55 : S55) (h56 : S56) :
    S512R.Three56ResL := by
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
  have hX2 := S33.s33X52_holds
  have h58 := S5B.s58_of h32 hX2 h52 h54 h55 h56
  have hn := S5B.s512Nat_holds_of_r2Cent h32 (S512N.r2Cent_holds h32)
  exact three56ResL_of_core ms14AS_holds hSQ hT h32 hX2 h52 h54 (Q2G.q2EvenZ_holds h32)
    (S512Z.oneCF_holds h32 hX2 h52 h54 h58 hn s310m_holds)
    (S512L.core_holds h32 h52 h53 h54 h55 h56)

end S512J

end CFSG.Quasithin.MS93

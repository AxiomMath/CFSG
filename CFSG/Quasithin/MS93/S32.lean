module

public import CFSG.Quasithin.MS93.S32XU
public import CFSG.Quasithin.MS93.S32G2L
public import CFSG.Quasithin.MS93.S32G2S
public import CFSG.Quasithin.MS93.S32Hat
public import CFSG.Quasithin.MS93.M15Main
public import CFSG.Quasithin.H13.A5S1521b
public import CFSG.Quasithin.MS93.M15G2Comm
public import CFSG.Quasithin.MS93.S32L3NS
public import CFSG.Quasithin.MS93.S32L3Two

public section

namespace CFSG.Quasithin.MS93

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank S32

theorem s32_holds :
    S32 := by
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
  have h45 : NoSL45 := fun _ _ hR _ hd e => false_of_equiv_statedSL_zmod hR hd e
  have hI : B5.B51IrrInputs :=
    FFC.b51IrrInputs_of_ffc asB42_holds asI16Cover_of FFC.asB51NonsplitOffSp4_holds
  have h51 : AsB51 := B5.asB51_holds
  exact s32_of h51 ms14AS_holds ms15AS_holds hSQ h45 s32PartXU_of
    (s32PartG2Large_of ms15G2Comm_holds hSQ) (s32PartG2Vertex_of ms15G2Comm_holds hSQ hT)
    (s32PartG2Struct_of h51 hSQ h45 hT hI) (s32PartHat_of h51 hSQ hT)
    (s32PartL3Two_of h51 hSQ hT) (s32PartL3NonSplit_of h51 hSQ hT)

end CFSG.Quasithin.MS93

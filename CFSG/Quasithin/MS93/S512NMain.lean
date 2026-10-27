module

public import CFSG.Quasithin.MS93.S512NCfg
public import CFSG.Quasithin.MS93.S512NNat
public import CFSG.Quasithin.MS93.S51Main
public import CFSG.Quasithin.H13.A5S1521b
public import CFSG.Quasithin.MS93.FFMain

public section

namespace CFSG.Quasithin.MS93

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible

@[expose] def S512N.R2Cent : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M T L : Subgroup G) (h : PUHyp M T L),
    PUMin M T L → critDist (puAmalgam h.le) = 4 →
    ∀ (k : ℕ) (F : Type) (_ : Field F) (_ : Fintype F) (a : ↥M →* ↥(StatedSp 2 F)),
      S5.IsSp4Data M T L k F a →
      ∀ α' ν μ₁ μ₂ : Vtx (puAmalgam h.le), S5B.IsChain512 h (2 ^ k) a α' ν μ₁ μ₂ →
        (Qv _ α').relIndex (ZM _ (baseA (puAmalgam h.le))) = 2 ^ k →
        (Qv _ (geo _ (baseA (puAmalgam h.le)) α' 2)).relIndex (ZM _ μ₁) = 2 ^ k →
        (S5.bSub h.le L (baseA _)).relIndex (ZM _ μ₁) = 2 ^ k →
        (S5.bSub h.le L μ₁).relIndex (ZM _ μ₂) = 2 ^ k →
        ⁅ZM _ μ₁, ZM _ (geo _ (baseA (puAmalgam h.le)) α' 2)⁆ ≤ S5.dSub h.le L (baseA _)

theorem S5B.s512Nat_holds (h14 : MS14AS) (hSQ : SQTKQuot)
    (hT : S32.TypeFacts) (h32 : S32) (hR : S512N.R2Cent) : S5B.S512Nat := by
  intro G _ _ M T L h hpu hb4 k F _ _ a hd α' ν μ₁ μ₂ hch hH1 hH2 hH3 hH4
  have hc := S512N.Cfg.of_chain h hb4 hch hH2 hH3 hH4
  obtain ⟨F', iF, fF, a', hcard, ha', hnat⟩ :=
    (hc.natHyp hd).isSumOfNaturalModulesVia h14 hSQ hT (s51_of h32) hpu hd
  refine ⟨F', iF, fF, a', hcard, ha', hnat, ?_⟩
  have hVL : ⁅S5.nclStab _ (baseA (puAmalgam h.le)) (ZM _ μ₁), puTrans h.le L (baseA _)⁆ ≤
      S5.nclStab _ (baseA (puAmalgam h.le)) (ZM _ μ₁) :=
    Subgroup.le_normalizer_iff_commutator_le_left.1
      ((puTrans_le_stab h.le L _).trans (S310.stab_le_normalizer_nclStab _ _ _))
  exact (Subgroup.commutator_mono hVL hVL).trans (hc.commutator_le_dSub hd
    (hR G M T L h hpu hb4 k F _ _ a hd α' ν μ₁ μ₂ hch hH1 hH2 hH3 hH4))

section Holds

open S32

theorem S5B.s512Nat_holds_of_r2Cent
    (h32 : S32) (hR : S512N.R2Cent) : S5B.S512Nat := by
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
  exact S5B.s512Nat_holds ms14AS_holds hSQ hT h32 hR

end Holds

end CFSG.Quasithin.MS93

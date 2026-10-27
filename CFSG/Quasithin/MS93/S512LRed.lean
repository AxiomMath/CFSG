module

public import CFSG.Quasithin.MS93.S512LCore
public import CFSG.Quasithin.H13.A5S1521b
public import CFSG.Quasithin.MS93.FFMain

public section

namespace CFSG.Quasithin.MS93

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open scoped commutatorElement

namespace S512L

@[expose] def CoreQ2 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M T L : Subgroup G) (h : PUHyp M T L),
    PUMin M T L → critDist (puAmalgam h.le) = 4 →
    ∀ (k : ℕ) (F : Type) (_ : Field F) (_ : Fintype F) (a : ↥M →* ↥(StatedSp 2 F)),
      S5.IsSp4Data M T L k F a → k = 1 →
      ∀ α' : Vtx (puAmalgam h.le), IsCritical _ (baseA _) α' → geo _ (baseA _) α' 1 = baseB _ →
      ∀ l : Submodule F (MSP.V4 F), S5.Case56 h (2 ^ k) a (geo _ (baseA (puAmalgam h.le)) α' 2) l →
      ∀ μ : Vtx (puAmalgam h.le),
        (∃ y ∈ stab _ (baseA (puAmalgam h.le)), μ = y • geo _ (baseA (puAmalgam h.le)) α' 2) →
        IsCritical _ μ (geo _ (baseA (puAmalgam h.le)) α' 2) →
        2 ^ k < (Qv _ (geo _ (baseA (puAmalgam h.le)) α' 2)).relIndex (ZM _ μ) →
        ⁅ZM (puAmalgam h.le) μ, ZM (puAmalgam h.le) (geo _ (baseA (puAmalgam h.le)) α' 2)⁆ ≤
          stabCenter _ (baseA (puAmalgam h.le)) →
        False

theorem core_of_coreQ2_aux (h14 : MS14AS) (hSQ : SQTKQuot)
    (hT : S32.TypeFacts) (h32 : S32) (h52 : S52) (h53 : S53) (h54 : S54) (h55 : S55)
    (h56 : S56) (hq2 : CoreQ2) : S512T.Core := by
  intro G _ _ M T L h hmin hb4 k F _ _ a hd α' hc hαβ l hl μ ⟨y, hy, hμy⟩ hcμ hbad hRc
  rcases Nat.lt_or_ge k 2 with hk | hk
  · exact hq2 G M T L h hmin hb4 k F _ _ a hd (by have := hd.1; omega) α' hc hαβ l hl μ
      ⟨y, hy, hμy⟩ hcμ hbad hRc
  · exact false_of_core h14 hSQ hT h32 h52 h53 h54 h55 h56 h hmin hb4 hd hk hc hαβ hl hy hμy
      hcμ hbad hRc

section Holds

open S32

theorem core_of_coreQ2
    (h32 : S32) (h52 : S52) (h53 : S53) (h54 : S54) (h55 : S55) (h56 : S56)
    (hq2 : CoreQ2) : S512T.Core := by
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
  exact core_of_coreQ2_aux ms14AS_holds hSQ hT h32 h52 h53 h54 h55 h56 hq2

end Holds

end S512L

end CFSG.Quasithin.MS93

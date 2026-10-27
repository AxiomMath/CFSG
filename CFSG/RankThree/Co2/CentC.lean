module

public import CFSG.RankThree.Co2.CentB
public import CFSG.RankThree.Co2.GoldVariant

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.RankThree.Co2

@[expose] def GoldschmidtStatement : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (S : Sylow 2 X) (A : Subgroup X), A ≤ S →
    IsMulCommutative A →
    (∀ a ∈ A, ∀ g : X, g⁻¹ * a * g ∈ (S : Subgroup X) → g⁻¹ * a * g ∈ A) →
    let M : Subgroup X := Subgroup.normalClosure (A : Set X)
    let π := QuotientGroup.mk' (CFSG.Open.goldschmidtOddCore M)
    let T := ((S : Subgroup X).subgroupOf M).map π ⊓
      CFSG.Open.goldschmidtLayer (M ⧸ CFSG.Open.goldschmidtOddCore M)
    CFSG.Open.pCore 2 (M ⧸ CFSG.Open.goldschmidtOddCore M) ⊔
        CFSG.Open.goldschmidtLayer (M ⧸ CFSG.Open.goldschmidtOddCore M) = ⊤ ∧
    (A.subgroupOf M).map π =
      CFSG.Open.pCore 2 (M ⧸ CFSG.Open.goldschmidtOddCore M) ⊔
        Subgroup.closure {t | t ∈ T ∧ t ^ 2 = 1} ∧
    ∀ K : Subgroup (M ⧸ CFSG.Open.goldschmidtOddCore M), CFSG.Open.IsComponentOf K ⊤ →
      CFSG.Open.goldschmidtSimpleType (K ⧸ Subgroup.center K)

namespace Co2CentHyp

variable {G : Type} [Group G] (h : Co2CentHyp G)

theorem VI_normal (hG : GoldschmidtStatement) : h.VI.Normal := by
  have := h.finite
  have hab : IsMulCommutative h.VI := ⟨⟨fun a b => Subtype.ext (h.VI_comm _ a.2 _ b.2)⟩⟩
  exact normal_of_goldschmidt_conclusion_of_E16 h.SI h.VI_le_SI
    (hG _ h.SI h.VI h.VI_le_SI hab h.VI_closed) h.VI_comm h.VI_sq h.card_VI h.VI_closed
    (eq_bot_iff.2 (sSup_le fun N hN => le_bot_iff.2 (h.VI_oddCore N hN.1 hN.2)))
    h.VI_centralizer_isPGroup h.VI_trans h.VI_card_le h.factorization_card_IG.le

theorem card_IG_of_goldschmidt (hG : GoldschmidtStatement) : Nat.card h.IG = 41287680 := by
  have hN := h.VI_normal hG
  rw [← h.card_normalizer_VI, Subgroup.normalizer_eq_top h.VI, Subgroup.card_top]

end Co2CentHyp

end CFSG.RankThree.Co2

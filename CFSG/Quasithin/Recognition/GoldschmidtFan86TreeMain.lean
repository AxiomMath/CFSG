module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86UnivTree
public import CFSG.Quasithin.Recognition.GoldschmidtFan86UnivAmalgam
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Split

public section

namespace CFSG.Quasithin.Fan86

open CFSG.Quasithin

@[expose] def FanTreeNoD10 : Prop :=
  ∀ (V G : Type) [Group G] [MulAction G V] (Γ : SimpleGraph V), FanTree Γ G →
    ∀ α β : V, Γ.Adj α β → Nat.card (Γ.neighborSet α) = 5 →
      ¬ Nonempty (oTwoQuot ↥(MulAction.stabilizer G α) ≃* DihedralGroup 5)

@[expose] def FanTreeOrder : Prop :=
  ∀ (V G : Type) [Group G] [MulAction G V] (Γ : SimpleGraph V), FanTree Γ G →
    ∀ α β : V, Γ.Adj α β → Nat.card (Γ.neighborSet α) = 5 →
      Nat.card ↥(MulAction.stabilizer G α ⊓ MulAction.stabilizer G β) = 2 ^ 11 ∨
        Nat.card ↥(MulAction.stabilizer G α ⊓ MulAction.stabilizer G β) = 2 ^ 12

@[expose] def FanTreeUnique : Prop :=
  ∀ (V G V' G' : Type) [Group G] [MulAction G V] [Group G'] [MulAction G' V']
    (Γ : SimpleGraph V) (Γ' : SimpleGraph V'), FanTree Γ G → FanTree Γ' G' →
    ∀ α β : V, Γ.Adj α β → Nat.card (Γ.neighborSet α) = 5 →
    ∀ α' β' : V', Γ'.Adj α' β' → Nat.card (Γ'.neighborSet α') = 5 →
      Nat.card ↥(MulAction.stabilizer G α ⊓ MulAction.stabilizer G β) =
        Nat.card ↥(MulAction.stabilizer G' α' ⊓ MulAction.stabilizer G' β') →
      (GoldAmalgam.ofSubgroupPair (MulAction.stabilizer G α) (MulAction.stabilizer G β)).IsIso
        (GoldAmalgam.ofSubgroupPair (MulAction.stabilizer G' α') (MulAction.stabilizer G' β'))

@[expose] def FanTreeMain : Prop :=
  (∀ (V G : Type) [Group G] [MulAction G V] (Γ : SimpleGraph V), FanTree Γ G →
      ∀ α β : V, Γ.Adj α β → Nat.card (Γ.neighborSet α) = 5 →
        ¬ Nonempty (oTwoQuot ↥(MulAction.stabilizer G α) ≃* DihedralGroup 5) ∧
        (Nat.card ↥(MulAction.stabilizer G α ⊓ MulAction.stabilizer G β) = 2 ^ 11 ∨
          Nat.card ↥(MulAction.stabilizer G α ⊓ MulAction.stabilizer G β) = 2 ^ 12)) ∧
  ∀ (V G V' G' : Type) [Group G] [MulAction G V] [Group G'] [MulAction G' V']
    (Γ : SimpleGraph V) (Γ' : SimpleGraph V'), FanTree Γ G → FanTree Γ' G' →
    ∀ α β : V, Γ.Adj α β → Nat.card (Γ.neighborSet α) = 5 →
    ∀ α' β' : V', Γ'.Adj α' β' → Nat.card (Γ'.neighborSet α') = 5 →
      Nat.card ↥(MulAction.stabilizer G α ⊓ MulAction.stabilizer G β) =
        Nat.card ↥(MulAction.stabilizer G' α' ⊓ MulAction.stabilizer G' β') →
      (GoldAmalgam.ofSubgroupPair (MulAction.stabilizer G α) (MulAction.stabilizer G β)).IsIso
        (GoldAmalgam.ofSubgroupPair (MulAction.stabilizer G' α') (MulAction.stabilizer G' β'))

theorem fanTreeMain_iff : FanTreeMain ↔ FanTreeNoD10 ∧ FanTreeOrder ∧ FanTreeUnique := by
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨fun V G _ _ Γ T α β hαβ hα => (h1 V G Γ T α β hαβ hα).1,
      fun V G _ _ Γ T α β hαβ hα => (h1 V G Γ T α β hαβ hα).2, h2⟩
  · rintro ⟨h1, h2, h3⟩
    exact ⟨fun V G _ _ Γ T α β hαβ hα =>
      ⟨h1 V G Γ T α β hαβ hα, h2 V G Γ T α β hαβ hα⟩, h3⟩

section Reduction

open Univ

theorem fanNoD10_of_fanTreeNoD10 (hT : FanTreeNoD10) : FanNoD10 := by
  intro A C B _ _ _ X hX hD
  obtain ⟨f⟩ := isIso_stabilizer_pair X
  obtain ⟨e⟩ := hD
  exact hT (Vtx X) X.Universal X.treeGraph (fanTree_of_hyp53 hX) (baseA X) (baseB X)
    (adj_baseA_baseB X) (card_neighborSet_inl hX _) ⟨(oTwoQuotMulEquiv f.eA).symm.trans e⟩

theorem fanOrder_of_fanTreeOrder (hT : FanTreeOrder) : FanOrder := by
  intro A C B _ _ _ X hX
  obtain ⟨f⟩ := isIso_stabilizer_pair X
  have h := hT (Vtx X) X.Universal X.treeGraph (fanTree_of_hyp53 hX) (baseA X) (baseB X)
    (adj_baseA_baseB X) (card_neighborSet_inl hX _)
  rwa [← Nat.card_congr f.eC.toEquiv] at h

theorem fanUnique_of_fanTreeUnique (hT : FanTreeUnique) : FanUnique := by
  intro A C B A' C' B' _ _ _ _ _ _ X X' hX hX' hcard
  obtain ⟨f⟩ := isIso_stabilizer_pair X
  obtain ⟨f'⟩ := isIso_stabilizer_pair X'
  have hc : Nat.card ↥(MulAction.stabilizer X.Universal (baseA X) ⊓
        MulAction.stabilizer X.Universal (baseB X)) =
      Nat.card ↥(MulAction.stabilizer X'.Universal (baseA X') ⊓
        MulAction.stabilizer X'.Universal (baseB X')) :=
    (Nat.card_congr f.eC.toEquiv).symm.trans (hcard.trans (Nat.card_congr f'.eC.toEquiv))
  exact (isIso_stabilizer_pair X).trans ((hT (Vtx X) X.Universal (Vtx X') X'.Universal
    X.treeGraph X'.treeGraph (fanTree_of_hyp53 hX) (fanTree_of_hyp53 hX')
    (baseA X) (baseB X) (adj_baseA_baseB X) (card_neighborSet_inl hX _)
    (baseA X') (baseB X') (adj_baseA_baseB X') (card_neighborSet_inl hX' _) hc).trans
    (isIso_stabilizer_pair X').symm)

theorem fanMain_of_fanTreeMain (h : FanTreeMain) : FanMain := by
  obtain ⟨h1, h2, h3⟩ := fanTreeMain_iff.1 h
  exact fanMain_iff.2 ⟨fanNoD10_of_fanTreeNoD10 h1, fanOrder_of_fanTreeOrder h2,
    fanUnique_of_fanTreeUnique h3⟩

end Reduction

end CFSG.Quasithin.Fan86

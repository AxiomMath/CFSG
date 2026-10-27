module

public import CFSG.LocalAnalysis.StandardType.GGKGroupFusionSeitzExcComp
public import CFSG.LocalAnalysis.StandardType.GGKGroupFusionSeitzExcOrder

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.AGLEmbeddingD2

@[expose] def GGSeitzExcTitsThreeInput : Prop :=
  ∀ (K : Type) [Group K] [Finite K] (d : TauCeti.ValidLieTypeIndex), d.1 = .tits →
    Nonempty (K ≃* (TauCeti.CFSGIndex.lie d).Group) →
      ∀ X : Subgroup K, X ≠ ⊤ → ¬ 3 ∣ X.index →
        Group.IsSolvable ↥X ∨
          (IsSimpleGroup ↥(commutator ↥X) ∧ Nat.card ↥(commutator ↥X) = 5616)

@[expose] def GGSeitzExcTitsFiveInput : Prop :=
  ∀ (K : Type) [Group K] [Finite K] (d : TauCeti.ValidLieTypeIndex), d.1 = .tits →
    Nonempty (K ≃* (TauCeti.CFSGIndex.lie d).Group) →
      ∀ X : Subgroup K, X ≠ ⊤ → ¬ 5 ∣ X.index →
        Group.IsSolvable ↥X ∨
          (IsSimpleGroup ↥(commutator ↥X) ∧ Nat.card ↥(commutator ↥X) = 7800)

theorem ggCenter_eq_bot_of_not_isSolvable {S : Type} [Group S] [IsSimpleGroup S]
    (h : ¬ Group.IsSolvable S) : Subgroup.center S = ⊥ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center S) with hc | hc
  · exact hc
  · refine absurd (Group.isSolvable_of_comm fun a b => ?_) h
    have hb : b ∈ Subgroup.center S := hc ▸ Subgroup.mem_top b
    exact (Subgroup.mem_center_iff.mp hb a)

theorem ggExists_component_of_layer_ne_bot {G : Type} [Group G] {A : Subgroup G}
    (hL : LargeEvenLayer A ≠ ⊥) : ∃ C : Subgroup G, IsComponentOf C A := by
  by_contra hcon
  push Not at hcon
  exact hL (sSup_eq_bot.mpr fun C hC => absurd hC (hcon C))

section Marked


theorem ggKGroupFusionAt_of_derived_card
    (hSch : CFSG.LocalAnalysis.ComponentInitial.SchreierFor InCatalog)
    {S : TauCeti.CFSGIndex → ℕ → Prop} (m : ℕ) (hm : m = 5616 ∨ m = 7800)
    (h : ∀ (i : TauCeti.CFSGIndex) (p : ℕ), S i p → ∀ (K : Type) [Group K] [Finite K],
      IsSimpleGroup K → Nonempty (K ≃* i.Group) →
        ∀ X : Subgroup K, X ≠ ⊤ → ¬ p ∣ X.index →
          Group.IsSolvable ↥X ∨
            (IsSimpleGroup ↥(commutator ↥X) ∧ Nat.card ↥(commutator ↥X) = m)) :
    GGKGroupFusionAt S := by
  intro W _ _ p H E i hi hyp hL hKH he
  exfalso
  have hns := ggSeitzExc_not_isSolvable hSch hyp hL
  rcases h i p hi _ hyp.2.1.1 he _ (ggSeitzExc_subgroupOf_ne_top hKH)
      (ggSeitzExc_not_dvd_index hyp) with hsol | ⟨hs, hcard⟩
  · exact hns hsol
  obtain ⟨C, hC⟩ := ggExists_component_of_layer_ne_bot hL
  obtain ⟨eC⟩ := ggSeitzExc_quotComponent_equiv hSch hyp hs hns hC
  have hCs : IsSimpleGroup ↥C := eC.isSimpleGroup
  have hXns : ¬ Group.IsSolvable ↥(commutator ↥(H.subgroupOf (CFSG.generalizedFitting W))) :=
    fun h' => hns (ggIsSolvable_of_commutator h')
  have hCns : ¬ Group.IsSolvable ↥C := fun h' =>
    hXns (Group.isSolvable_of_isSolvable_injective (f := eC.symm.toMonoidHom) eC.symm.injective)
  have hZ := ggCenter_eq_bot_of_not_isSolvable hCns
  have hcardC : Nat.card (↥C ⧸ Subgroup.center ↥C) = m := by
    rw [Nat.card_congr ((QuotientGroup.quotientMulEquivOfEq hZ).trans
      QuotientGroup.quotientBot).toEquiv, Nat.card_congr eC.toEquiv, hcard]
  obtain ⟨-, hmark⟩ := hyp.2.2.1 C hC
  obtain ⟨lab, -, hmod⟩ := largeEvenMarking_markedModel_centerQuot hmark
  have hne := ggMarkedModel_card_ne hmod
  rcases hm with rfl | rfl
  · exact hne.1 hcardC
  · exact hne.2 hcardC

theorem ggKGroupFusionAt_titsThree
    (hSch : CFSG.LocalAnalysis.ComponentInitial.SchreierFor InCatalog)
    (hT : GGSeitzExcTitsThreeInput) : GGKGroupFusionAt GGKFSeitzTitsThree :=
  ggKGroupFusionAt_of_derived_card hSch 5616 (Or.inl rfl)
    fun _ _ ⟨hp, d, hi, hd⟩ K _ _ _ he _ hX h3 => by
      subst hp hi
      exact hT K d hd he _ hX h3

theorem ggKGroupFusionAt_titsFive
    (hSch : CFSG.LocalAnalysis.ComponentInitial.SchreierFor InCatalog)
    (hT : GGSeitzExcTitsFiveInput) : GGKGroupFusionAt GGKFSeitzTitsFive :=
  ggKGroupFusionAt_of_derived_card hSch 7800 (Or.inr rfl)
    fun _ _ ⟨hp, d, hi, hd⟩ K _ _ _ he _ hX h5 => by
      subst hp hi
      exact hT K d hd he _ hX h5

end Marked

end CFSG.StandardType

module

public import CFSG.Quasithin.Vol2.Ch10StatementsD

public section

namespace CFSG.Quasithin.Vol2.Ch10

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13

@[expose] def Stmt10_3_1 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L I : Subgroup G), Hyp10 G T L I →
    fsuCVM T L I = ⊥ ∧ ∀ K : Subgroup G, IsLi T L K → IsTISetIn ⁅fsuVM T L I, K⁆ ⊤

@[expose] def Stmt10_3_2 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L I : Subgroup G), Hyp10 G T L I →
    ∀ z ∈ quasithinOmegaOneCenter T ⊓ fsuVM T L I, z ≠ 1 →
      ¬ Subgroup.centralizer ({z} : Set G) ≤ fsuM T L

@[expose] def Stmt10_3_3 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L I : Subgroup G), Hyp10 G T L I →
    ∀ t v₁ v₂ : G, IsData10_2_11 T L I t v₁ v₂ →
      Nonempty (↥(Kz T L (v₁ * v₂) ⊔ T) ⧸ CFSG.pCore 2 ↥(Kz T L (v₁ * v₂) ⊔ T) ≃* SymFiveWrTwo)

@[expose] def StmtClose10 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L I : Subgroup G), Hyp10 G T L I →
    ∃ K : Subgroup G, quasithinIsMaximalLocal T K ∧ quasithinIsFaithfulLocal T K ∧
      CFSG.IsQuasisimple (↥K ⧸ CFSG.pCore 2 ↥K) ∧ ¬ T ≤ Subgroup.normalizer (K : Set G) ∧
      Nonempty (↥K ⧸ CFSG.pCore 2 ↥K ≃* alternatingGroup (Fin 5))

theorem card_SL_three_two : Nat.card (Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) = 168 := by
  rw [Matrix.card_SL_field]
  simp [Fin.prod_univ_three]

theorem not_sl_three_two_equiv_alternating_five
    (e : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2) ≃* alternatingGroup (Fin 5)) : False := by
  have h := Nat.card_congr e.toEquiv
  rw [card_SL_three_two, nat_card_alternatingGroup, Nat.card_fin] at h
  norm_num [Nat.factorial] at h

end CFSG.Quasithin.Vol2.Ch10

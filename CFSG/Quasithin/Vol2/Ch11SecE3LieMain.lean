module

public import CFSG.Quasithin.Vol2.Ch11SecE3LieL2Up
public import CFSG.Quasithin.Vol2.Ch11SecE3LieSzLow
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19IdOrders
public import CFSG.Quasithin.Vol2.Ch11SecBNPLie

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecE3

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.E1

@[expose] def E114LieCited : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T : Subgroup G), SQTKGroup G →
    IsSimpleGroup (ASInputs.FStar G) → quasithinIsSylowTwo T →
    CFSG.generalizedFitting G ⊔ T = ⊤ → ∀ n : ℕ, 2 ≤ n →
      (IsPSU 3 2 n (ASInputs.FStar G) ∨ IsPSL 3 2 n (ASInputs.FStar G) ∨
        IsPSp4 2 n (ASInputs.FStar G)) → E1.nParam (⊤ : Subgroup G) = n

section

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem one_le_nParam_of_not_odd (hG : ¬ Odd (Nat.card G)) :
    (1 : ℕ∞) ≤ E1.nParam (⊤ : Subgroup G) := by
  unfold E1.nParam
  rw [Subgroup.card_top, ite_eq_right hG]
  exact le_iInf₂ fun i hi => by exact_mod_cast hi.1

omit [Finite G] in
theorem not_odd_of_card {H : Subgroup G} (hH : Nat.card H = 168 ∨ Nat.card H = 360) :
    ¬ Odd (Nat.card G) := by
  intro hodd
  have h := Odd.of_dvd_nat hodd (Subgroup.card_subgroup_dvd_card H)
  rcases hH with hH | hH <;> rw [hH] at h <;> exact absurd h (by decide)

theorem two_le_of_isPSU_or_isPSp4 {X : Type} [Group X] {n : ℕ}
    (h : IsPSU 3 2 n X ∨ IsPSp4 2 n X) : 2 ≤ n := by
  rcases h with ⟨⟨-, hn1, -, hne⟩, -⟩ | ⟨⟨-, hn1, -, hne⟩, -⟩
  all_goals
    by_contra hlt
    obtain rfl : n = 1 := by omega
    exact hne (by simp)

theorem nParam_eq_of_typeLie (hC : E114LieCited) {T : Subgroup G} (hSQ : SQTKGroup G)
    (hFs : IsSimpleGroup (ASInputs.FStar G)) (hT : quasithinIsSylowTwo T)
    (hFT : CFSG.generalizedFitting G ⊔ T = ⊤)
    (h1 : IsPSL 3 2 1 (ASInputs.FStar G) ∨ IsAlt 6 (ASInputs.FStar G) →
      E1.nParam (⊤ : Subgroup G) ≤ 1)
    {n : ℕ} (hn : 1 ≤ n) (hty : SecB.TypeLie n (ASInputs.FStar G)) :
    E1.nParam (⊤ : Subgroup G) = n := by
  rcases hty with h | h | h | h | h | ⟨rfl, h⟩
  · exact nParam_eq_of_isPSL22 h hFs hT hFT
  · exact nParam_eq_of_isSz h hFs hT hFT
  · exact hC G T hSQ hFs hT hFT n (two_le_of_isPSU_or_isPSp4 (Or.inl h)) (Or.inl h)
  · rcases Nat.lt_or_ge n 2 with hlt | hn2
    · have h1n : n = 1 := by omega
      subst h1n
      refine le_antisymm (h1 (Or.inl h)) ?_
      exact one_le_nParam_of_not_odd (not_odd_of_card (H := CFSG.generalizedFitting G)
        (Or.inl (CFSG.QuasithinUnique.Id2519.card_of_psl_three_two h)))
    · exact hC G T hSQ hFs hT hFT n hn2 (Or.inr (Or.inl h))
  · exact hC G T hSQ hFs hT hFT n (two_le_of_isPSU_or_isPSp4 (Or.inr h)) (Or.inr (Or.inr h))
  · refine le_antisymm (h1 (Or.inr h)) ?_
    obtain ⟨e⟩ : Nonempty (ASInputs.FStar G ≃* alternatingGroup (Fin 6)) := h
    refine one_le_nParam_of_not_odd (not_odd_of_card (H := CFSG.generalizedFitting G)
      (Or.inr ?_))
    rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup, Nat.card_eq_fintype_card,
      Fintype.card_fin]
    decide

end

end CFSG.Quasithin.Vol2.Ch11.SecE3

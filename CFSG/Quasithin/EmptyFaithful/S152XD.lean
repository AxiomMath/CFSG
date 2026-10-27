module

public import CFSG.Quasithin.EmptyFaithful.S152XC
public import CFSG.Quasithin.EmptyFaithful.S151cStmt2
public import CFSG.Quasithin.EmptyFaithful.S152UF112

public section

namespace CFSG.Quasithin.S152X

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits
open CFSG.Quasithin.He9 (isQuasithinSub_of)

variable {G : Type} [Group G] [Finite G]

theorem listed_kS5 (H : Subgroup G) (φ : OTwoQuot H ≃* Equiv.Perm (Fin 5)) :
    IsRankOneListed (OTwoQuot (kS5 H φ)) := by
  obtain ⟨e⟩ := nonempty_oTwoQuot_kS5 H φ
  obtain ⟨f⟩ := He9.nonempty_psl2_gf4_mulEquiv_alternating
  exact Or.inl ⟨2, by norm_num, ⟨e.trans f.symm⟩⟩

namespace S5Ctx

variable {T Mc M H Y₁ : Subgroup G} {φ : OTwoQuot H ≃* Equiv.Perm (Fin 5)} (c : S5Ctx T Mc M H Y₁ φ)

section Small

variable (hF : Nat.card (OTwoQuot (Y₁ ⊔ rcOf Mc M)) = 10 ∨ Nat.card (OTwoQuot (Y₁ ⊔ rcOf Mc M)) = 20)

include c hF

theorem borel_L₁_eq : borelOf (Y₁ ⊔ rcOf Mc M) T = T ⊓ (Y₁ ⊔ rcOf Mc M) :=
  inf_normalizer_eq_of_card c.sylow_L₁ hF

theorem borel_L₁_le_T : borelOf (Y₁ ⊔ rcOf Mc M) T ≤ T :=
  (c.borel_L₁_eq hF).le.trans inf_le_left

theorem borel_L₁_le_normalizer_K :
    borelOf (Y₁ ⊔ rcOf Mc M) T ≤ Subgroup.normalizer (kS5 H φ : Set G) :=
  (c.borel_L₁_le_T hF).trans c.T_le_normalizer_K

theorem charTwo_K : CharTwo (kS5 H φ ⊔ T ⊔ borelOf (Y₁ ⊔ rcOf Mc M) T) := by
  have h : kS5 H φ ⊔ T ⊔ borelOf (Y₁ ⊔ rcOf Mc M) T = H := by
    rw [sup_eq_left.2 ((c.borel_L₁_le_T hF).trans le_sup_right)]
    exact sup_kS5_eq φ c.hT
  rw [h]
  exact c.charTwo_H

theorem hyp111 (hlist : IsRankOneListed (OTwoQuot (Y₁ ⊔ rcOf Mc M))) :
    Hyp111 (Y₁ ⊔ rcOf Mc M) (kS5 H φ) T where
  h1 :=
    { finite := inferInstance
      pgroup := c.T_pgroup
      normalizes := c.T_le_normalizer_L₁
      sylow := c.sylow_L₁
      listed := hlist
      borel_le := c.borel_K_le_normalizer_L₁
      charTwo := c.charTwo_L₁TB }
  h2 :=
    { finite := inferInstance
      pgroup := c.T_pgroup
      normalizes := c.T_le_normalizer_K
      sylow := isSylowTwoOf_inf_kS5 φ c.hT
      listed := listed_kS5 H φ
      borel_le := c.borel_L₁_le_normalizer_K hF
      charTwo := c.charTwo_K hF }
  o2 := c.o2_eq_bot

end Small

include c

theorem false_of_S5_small (hF204 : He9.Input15204F112)
    (hq : Nonempty (OTwoQuot (Y₁ ⊔ rcOf Mc M) ≃* DihedralGroup 5) ∨
      Nonempty (OTwoQuot (Y₁ ⊔ rcOf Mc M) ≃* ↥(CFSG.Open.Sz 0))) : False := by
  have hF : Nat.card (OTwoQuot (Y₁ ⊔ rcOf Mc M)) = 10 ∨ Nat.card (OTwoQuot (Y₁ ⊔ rcOf Mc M)) = 20 := by
    rcases hq with ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩
    · left
      rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, DihedralGroup.card]
    · right
      rw [Nat.card_congr e.toEquiv]
      exact card_sz_zero_eq_twenty
  have hlist : IsRankOneListed (OTwoQuot (Y₁ ⊔ rcOf Mc M)) := by
    rcases hq with ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩
    · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨e⟩)))
    · exact Or.inr (Or.inl ⟨0, ⟨e⟩⟩)
  have hS : (T.subgroupOf (T ⊔ borelOf (Y₁ ⊔ rcOf Mc M) T)).Normal := by
    rw [sup_eq_left.2 (c.borel_L₁_le_T hF), Subgroup.subgroupOf_self]
    infer_instance
  exact hF204 G (Y₁ ⊔ rcOf Mc M) (kS5 H φ) T (c.hyp111 hF hlist)
    (isQuasithinSub_of c.hs.qtfe.qtke _) (Or.inl hS) hq (nonempty_oTwoQuot_kS5 H φ)

end S5Ctx

end CFSG.Quasithin.S152X

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.S152X

theorem input15208F112At_S5_D10 (h1515 : StageLemma1515CE) (h1519 : StageLemma1519)
    (h15207 : StageLemma15207) (hF204 : He9.Input15204F112) :
    Input15208F112At (Equiv.Perm (Fin 5)) (DihedralGroup 5) := by
  intro G _ _ T Mc M hs H hH Y₁ hY₁ hφ hq
  obtain ⟨φ⟩ := hφ
  exact (S5Ctx.mk hs hH (h1515 G T Mc M hs.qtfe hs.mf hs.ce) (h1519 G T Mc M hs.qtfe hs.mf hs.ce)
    hY₁ (h15207 G T Mc M hs Y₁ hY₁) : S5Ctx T Mc M H Y₁ φ).false_of_S5_small hF204 (Or.inl hq)

theorem input15208F112At_S5_Sz0 (h1515 : StageLemma1515CE) (h1519 : StageLemma1519)
    (h15207 : StageLemma15207) (hF204 : He9.Input15204F112) :
    Input15208F112At (Equiv.Perm (Fin 5)) ↥(CFSG.Open.Sz 0) := by
  intro G _ _ T Mc M hs H hH Y₁ hY₁ hφ hq
  obtain ⟨φ⟩ := hφ
  exact (S5Ctx.mk hs hH (h1515 G T Mc M hs.qtfe hs.mf hs.ce) (h1519 G T Mc M hs.qtfe hs.mf hs.ce)
    hY₁ (h15207 G T Mc M hs Y₁ hY₁) : S5Ctx T Mc M H Y₁ φ).false_of_S5_small hF204 (Or.inr hq)

@[expose] def Input15208F112Rest : Prop :=
  Input15208F112At (Equiv.Perm (Fin 3)) (Equiv.Perm (Fin 3)) ∧
  Input15208F112At (Equiv.Perm (Fin 3)) (DihedralGroup 5) ∧
  Input15208F112At (Equiv.Perm (Fin 3)) ↥(CFSG.Open.Sz 0) ∧
  Input15208F112At (Equiv.Perm (Fin 5)) (Equiv.Perm (Fin 3))

theorem input15208F112_of_rest (h1515 : StageLemma1515CE) (h1519 : StageLemma1519)
    (h15206 : StageLemma15206) (h15207 : StageLemma15207) (hF204 : He9.Input15204F112)
    (hR : Input15208F112Rest) : Input15208F112 :=
  input15208F112_of_cases h15206 hR.1 hR.2.1 hR.2.2.1 hR.2.2.2
    (input15208F112At_S5_D10 h1515 h1519 h15207 hF204) (input15208F112At_S5_Sz0 h1515 h1519 h15207 hF204)

end CFSG.Quasithin

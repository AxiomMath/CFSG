module

public import CFSG.Quasithin.EmptyFaithful.F112RC
public import CFSG.Quasithin.EmptyFaithful.S152XD

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.S152X
open CFSG.Quasithin.He9 (isQuasithinSub_of)

namespace F112RR

variable {G : Type} [Group G] [Finite G]

namespace S5Ctx

variable {T Mc M H Y₁ : Subgroup G} {φ : OTwoQuot H ≃* Equiv.Perm (Fin 5)}
  (c : CFSG.Quasithin.S152X.S5Ctx T Mc M H Y₁ φ)
  (hq₁ : Nonempty (OTwoQuot (Y₁ ⊔ rcOf Mc M) ≃* Equiv.Perm (Fin 3)))

include c hq₁

theorem borel_L₁_eq_S3 : borelOf (Y₁ ⊔ rcOf Mc M) T = T ⊓ (Y₁ ⊔ rcOf Mc M) := by
  obtain ⟨e⟩ := hq₁
  have hc : Nat.card (OTwoQuot (Y₁ ⊔ rcOf Mc M)) = 2 ^ 1 * 3 := by
    rw [Nat.card_congr e.toEquiv, card_perm_fin_three]
  exact inf_normalizer_eq_of_card_quot c.sylow_L₁ le_rfl (by norm_num) (by decide) hc

theorem borel_L₁_le_T_S3 : borelOf (Y₁ ⊔ rcOf Mc M) T ≤ T :=
  (borel_L₁_eq_S3 c hq₁).le.trans inf_le_left

theorem hyp111_S3 : Hyp111 (Y₁ ⊔ rcOf Mc M) (kS5 H φ) T where
  h1 :=
    { finite := inferInstance
      pgroup := c.T_pgroup
      normalizes := c.T_le_normalizer_L₁
      sylow := c.sylow_L₁
      listed := Or.inl ⟨1, le_rfl, isL2Quot_one_iff_perm3.mpr hq₁⟩
      borel_le := c.borel_K_le_normalizer_L₁
      charTwo := c.charTwo_L₁TB }
  h2 :=
    { finite := inferInstance
      pgroup := c.T_pgroup
      normalizes := c.T_le_normalizer_K
      sylow := isSylowTwoOf_inf_kS5 φ c.hT
      listed := listed_kS5 H φ
      borel_le := (borel_L₁_le_T_S3 c hq₁).trans c.T_le_normalizer_K
      charTwo := by
        have h : kS5 H φ ⊔ T ⊔ borelOf (Y₁ ⊔ rcOf Mc M) T = H := by
          rw [sup_eq_left.2 ((borel_L₁_le_T_S3 c hq₁).trans le_sup_right)]
          exact sup_kS5_eq φ c.hT
        rw [h]
        exact c.charTwo_H }
  o2 := c.o2_eq_bot

end S5Ctx

end F112RR

end CFSG.Quasithin

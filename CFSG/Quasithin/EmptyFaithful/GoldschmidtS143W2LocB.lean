module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtS143W2Ctx
public import CFSG.Quasithin.EmptyFaithful.S1422LocBasic

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.QuasithinUnique.Ch1
  CFSG.QuasithinUnique.Tight CFSG.QuasithinUnique.BenderBranch
  CFSG.ComponentClassification.AschbacherTightEmbedding

namespace S143

namespace InspW2

variable {G : Type} [Group G] [Finite G] {T M : Subgroup G} {g : G} {A : Subgroup G} {t d x : G}

theorem card_qOf (h : Ctx T M g A t d x) : Nat.card ↥(qOf T) = 64 := by
  have hDU : dOf T M ≤ Subgroup.centralizer (uOfL22 T M : Set G) := inf_le_right
  have hprod := card_sup_mul_card_inf_of_le_centralizer hDU
  have hcZ : Nat.card ↥(quasithinOmegaOneCenter T) = 2 := h.c.hyp.card_omegaOneCenter
  have hDeq : dOf T M ⊓ uOfL22 T M = quasithinOmegaOneCenter T := by
    apply le_antisymm
    · intro u hu
      rw [← h.c.centerOf_uOfL22_eq]
      exact ⟨hu.2, Subgroup.mem_centralizer_iff.mpr fun v hv =>
        (Subgroup.mem_centralizer_iff.mp (hDU hu.1) v hv)⟩
    · intro u hu
      refine ⟨Z_le_dOf h.c hu, ?_⟩
      rw [← h.c.centerOf_uOfL22_eq] at hu
      exact hu.1
  have hD4 : Nat.card ↥(dOf T M) = 4 := by rw [h.hD, Nat.card_zpowers, h.hd4]
  rw [hDeq, hcZ, hD4, h.c.c15.q8sq.1, sup_comm, ← h.c19.a.q_eq] at hprod
  omega

theorem card_T (h : Ctx T M g A t d x) : Nat.card ↥T = 512 := by
  rw [card_T_eq h.c, card_qOf h]

theorem card_mcOf (h : Ctx T M g A t d x) : Nat.card ↥(mcOf T) = 4608 := by
  rw [card_eq_card_oTwoQuot_mul,
    show Nat.card (oTwoQuot ↥(mcOf T)) = 72 from h.c.card_OTwoQuot_mcOf]
  have := card_qOf h
  unfold qOf at this
  rw [this]

end InspW2

end S143

end CFSG.Quasithin

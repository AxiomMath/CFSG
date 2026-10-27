module

public import CFSG.Quasithin.EmptyFaithful.S152He9Q
public import CFSG.Quasithin.EmptyFaithful.QTKELocal
public import CFSG.Quasithin.EmptyFaithful.S152He9A5
public import CFSG.Quasithin.EmptyFaithful.S152He9X

public section

namespace CFSG.Quasithin.He9

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.LieType.BorelTits
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

@[expose] def sOf (T K₁ : Subgroup G) : Subgroup G := T ⊓ Subgroup.normalizer (K₁ : Set G)

@[expose] noncomputable def l1Of (T Mc M : Subgroup G) : Subgroup G := yOf152 T Mc M ⊔ rcOf Mc M

@[expose] noncomputable def g0Of (T Mc M K₁ : Subgroup G) : Subgroup G := l1Of T Mc M ⊔ K₁ ⊔ sOf T K₁

@[expose] def Input15204F112 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L1 L2 S : Subgroup G), Hyp111 L1 L2 S →
    IsQuasithinSub (L1 ⊔ L2 ⊔ S) →
    ((S.subgroupOf (S ⊔ borelOf L1 S)).Normal ∨ (S.subgroupOf (S ⊔ borelOf L2 S)).Normal) →
    (Nonempty (OTwoQuot L1 ≃* DihedralGroup 5) ∨ Nonempty (OTwoQuot L1 ≃* ↥(CFSG.Open.Sz 0))) →
    Nonempty (OTwoQuot L2 ≃* ↥(alternatingGroup (Fin 5))) → False

theorem isQuasithinSub_of (hK : quasithinIsQTKECat G) (X : Subgroup G) : IsQuasithinSub X := by
  intro p hp hp2 R _ hR1 hR2
  exact (CFSG.SectionRank.pRank_mono hp.one_lt inf_le_right).trans
    (pRank_le_two_of_isTwoLocal hK ⟨R, hR1, hR2, rfl⟩ hp hp2)

omit [Finite G] in
theorem S_le_T {T K₁ : Subgroup G} : sOf T K₁ ≤ T := inf_le_left

omit [Finite G] in
theorem S_le_normalizer_K₁ {T K₁ : Subgroup G} : sOf T K₁ ≤ Subgroup.normalizer (K₁ : Set G) :=
  inf_le_right

theorem l1_normalizer {T Mc M : Subgroup G} : Subgroup.normalizer (yOf152 T Mc M : Set G) ⊓
    Subgroup.normalizer (rcOf Mc M : Set G) ≤ Subgroup.normalizer (l1Of T Mc M : Set G) :=
  Subgroup.inf_normalizer_le_normalizer_sup _ _

theorem rc_le_l1 {T Mc M : Subgroup G} : rcOf Mc M ≤ l1Of T Mc M := le_sup_right

theorem Y_le_l1 {T Mc M : Subgroup G} : yOf152 T Mc M ≤ l1Of T Mc M := le_sup_left

namespace Ctx15204

variable {T Mc M H K₁ K₂ : Subgroup G} {π : ↥H →* W5} (c : Ctx15204 T Mc M H K₁ K₂ π)

include c

theorem S_pgroup : IsPGroup 2 (sOf T K₁) := c.hs.qtfe.sylow.1.to_le inf_le_left

theorem rc_le_S : rcOf Mc M ≤ sOf T K₁ := le_inf c.rc_le_T c.rc_le_normalizer₁

theorem S_le_normalizer_L₁ : sOf T K₁ ≤ Subgroup.normalizer (l1Of T Mc M : Set G) :=
  fun _ hx => l1_normalizer ⟨c.T_le_normalizer_Y hx.1, c.T_le_normalizer_rc hx.1⟩

theorem S_inf_L₁ : sOf T K₁ ⊓ l1Of T Mc M = rcOf Mc M :=
  (F1.eq_of_isSylowTwoOf_le c.y.iso.1 inf_le_right (c.S_pgroup.to_le inf_le_left)
    (le_inf c.rc_le_S rc_le_l1)).symm

theorem sylow_L₁ : IsSylowTwoOf (sOf T K₁ ⊓ l1Of T Mc M) (l1Of T Mc M) := by
  rw [c.S_inf_L₁]
  exact c.y.iso.1

theorem sylow_K₁ : IsSylowTwoOf (sOf T K₁ ⊓ K₁) K₁ := by
  have hSyl := c.wr.isSylow_S c.hT
  have hK₁N : K₁ ≤ H ⊓ Subgroup.normalizer (K₁ : Set G) := le_inf c.wr.le₁ Subgroup.le_normalizer
  exact A4.isSylowTwoOf_inf_normal hSyl hK₁N inf_le_right

theorem borel₂_le_HM : borelOf K₁ (sOf T K₁) ≤ H ⊓ M :=
  fun _ hx => ⟨c.wr.le₁ (Subgroup.mem_inf.1 hx).1,
    c.wr.borel_le_M c.hs c.hH c.h1519 c.hT hx⟩

theorem borel₂_le_normalizer_L₁ : borelOf K₁ (sOf T K₁) ≤ Subgroup.normalizer (l1Of T Mc M : Set G) :=
  fun _ hx => l1_normalizer ⟨c.inf_normalizer_Y (c.borel₂_le_HM hx),
    c.inf_normalizer_rc (c.borel₂_le_HM hx)⟩

theorem borel₁_le : borelOf (l1Of T Mc M) (sOf T K₁) ≤ rcOf Mc M := by
  intro g hg
  have hS : sOf T K₁ ⊓ l1Of T Mc M = rcOf Mc M := c.S_inf_L₁
  unfold borelOf at hg
  rw [hS] at hg
  exact c.y.normalizer_rc_le hg

theorem borel₁_le_normalizer_K₁ :
    borelOf (l1Of T Mc M) (sOf T K₁) ≤ Subgroup.normalizer (K₁ : Set G) :=
  fun _ hx => S_le_normalizer_K₁ (c.rc_le_S (c.borel₁_le hx))

theorem charTwo_M : CharTwo M := by
  obtain ⟨P, hP⟩ := exists_sylow_of_quasithinIsSylowTwo c.hs.qtfe.sylow
  exact c.hs.qtfe.qtke.2.1 M c.y.data.inM.1.1 ⟨P, hP ▸ c.y.data.T_le⟩

theorem L₁_le_M : l1Of T Mc M ≤ M := sup_le c.y.hYM c.y.hRM

theorem S_le_M : sOf T K₁ ≤ M := S_le_T.trans c.y.data.T_le

theorem charTwo_L₁SB : CharTwo (l1Of T Mc M ⊔ sOf T K₁ ⊔ borelOf K₁ (sOf T K₁)) := by
  refine charTwo_of_pCore_centralizer_le c.charTwo_M ?_ ?_
  · exact sup_le (sup_le c.L₁_le_M c.S_le_M) (fun x hx => (c.borel₂_le_HM hx).2)
  · exact inf_le_left.trans (c.y.O2M_le_rc.trans (rc_le_l1.trans
      (le_sup_left.trans le_sup_left)))

theorem charTwo_H : CharTwo H := by
  obtain ⟨P, hP⟩ := exists_sylow_of_quasithinIsSylowTwo c.hs.qtfe.sylow
  subst hP
  exact CFSG.Quasithin.charTwo_of_inH c.hs.qtfe.qtke.2.1 P c.hH.1

theorem charTwo_K₁S : CharTwo (K₁ ⊔ sOf T K₁) := by
  refine charTwo_of_relIndex_le_two c.charTwo_H c.hT
    (sup_le c.wr.le₁ (S_le_T.trans c.hT.1)) ?_
  have h1 : (K₁ ⊔ sOf T K₁).relIndex T ∣ (sOf T K₁).relIndex T :=
    Subgroup.relIndex_dvd_of_le_left T le_sup_right
  have h2 : (sOf T K₁).relIndex T = 2 := c.wr.relIndex_S c.hT
  rw [h2] at h1
  exact Nat.le_of_dvd (by norm_num) h1

theorem charTwo_K₁SB : CharTwo (K₁ ⊔ sOf T K₁ ⊔ borelOf (l1Of T Mc M) (sOf T K₁)) := by
  have : K₁ ⊔ sOf T K₁ ⊔ borelOf (l1Of T Mc M) (sOf T K₁) = K₁ ⊔ sOf T K₁ :=
    sup_eq_left.2 ((c.borel₁_le.trans c.rc_le_S).trans le_sup_right)
  rw [this]
  exact c.charTwo_K₁S

theorem listed_L₁ : IsRankOneListed (OTwoQuot (l1Of T Mc M)) := by
  rcases c.y.iso.2.2 with ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩
  · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨e⟩)))
  · exact Or.inr (Or.inl ⟨0, ⟨e⟩⟩)

theorem quot_K₁ : Nonempty (OTwoQuot K₁ ≃* ↥(alternatingGroup (Fin 5))) := by
  obtain ⟨e⟩ := c.wr.nonempty_oTwoQuot₁
  exact ⟨e.trans (MulEquiv.refl _)⟩

theorem listed_K₁ : IsRankOneListed (OTwoQuot K₁) := by
  obtain ⟨e⟩ := c.quot_K₁
  obtain ⟨f⟩ := nonempty_psl2_gf4_mulEquiv_alternating
  exact Or.inl ⟨2, by norm_num, ⟨e.trans f.symm⟩⟩

theorem hyp111 (ho2 : pCoreOf 2 (g0Of T Mc M K₁) = ⊥) :
    Hyp111 (l1Of T Mc M) K₁ (sOf T K₁) where
  h1 :=
    { finite := inferInstance
      pgroup := c.S_pgroup
      normalizes := c.S_le_normalizer_L₁
      sylow := c.sylow_L₁
      listed := c.listed_L₁
      borel_le := c.borel₂_le_normalizer_L₁
      charTwo := c.charTwo_L₁SB }
  h2 :=
    { finite := inferInstance
      pgroup := c.S_pgroup
      normalizes := S_le_normalizer_K₁
      sylow := c.sylow_K₁
      listed := c.listed_K₁
      borel_le := c.borel₁_le_normalizer_K₁
      charTwo := c.charTwo_K₁SB }
  o2 := ho2

theorem normal_S_B₁ :
    ((sOf T K₁).subgroupOf (sOf T K₁ ⊔ borelOf (l1Of T Mc M) (sOf T K₁))).Normal := by
  have : sOf T K₁ ⊔ borelOf (l1Of T Mc M) (sOf T K₁) = sOf T K₁ :=
    sup_eq_left.2 (c.borel₁_le.trans c.rc_le_S)
  rw [this, Subgroup.subgroupOf_self]
  infer_instance

theorem false_of_o2_eq_bot (hF : Input15204F112) (ho2 : pCoreOf 2 (g0Of T Mc M K₁) = ⊥) : False :=
  hF G (l1Of T Mc M) K₁ (sOf T K₁) (c.hyp111 ho2)
    (isQuasithinSub_of c.hs.qtfe.qtke _) (Or.inl c.normal_S_B₁) c.y.iso.2.2 c.quot_K₁

end Ctx15204

end CFSG.Quasithin.He9

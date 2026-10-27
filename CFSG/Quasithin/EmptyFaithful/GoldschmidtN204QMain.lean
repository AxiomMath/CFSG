module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtN204QHyp
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtN204QRank
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtN204Main

public section

namespace CFSG.Quasithin.He9

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.N204

variable {G : Type} [Group G] [Finite G]

namespace Ctx15204

variable {T Mc M H K₁ K₂ : Subgroup G} {π : ↥H →* W5} (c : Ctx15204 T Mc M H K₁ K₂ π)

include c

theorem hyp111Mod (hS : IsSylowTwoOf (sOf T K₁) (g0Of T Mc M K₁))
    (hC₁ : CharTwoMod (g1Of T Mc M K₁) (pCoreOf 2 (g0Of T Mc M K₁)))
    (hC₂ : CharTwoMod (g2Of T K₁) (pCoreOf 2 (g0Of T Mc M K₁))) :
    Hyp111Mod (l1Of T Mc M) K₁ (sOf T K₁) where
  sylow := hS
  pgroup := c.S_pgroup
  normalizes₁ := c.S_le_normalizer_L₁
  normalizes₂ := S_le_normalizer_K₁
  sylow₁ := c.sylow_L₁
  sylow₂ := c.sylow_K₁
  listed₁ := c.listed_L₁
  listed₂ := c.listed_K₁
  borel₁ := c.borel₂_le_normalizer_L₁
  borel₂ := c.borel₁_le_normalizer_K₁
  charTwo₁ := hC₁
  charTwo₂ := by
    have : K₁ ⊔ sOf T K₁ ⊔ borelOf (l1Of T Mc M) (sOf T K₁) = K₁ ⊔ sOf T K₁ :=
      sup_eq_left.2 ((c.borel₁_le.trans c.rc_le_S).trans le_sup_right)
    rw [this]
    exact hC₂

end Ctx15204

theorem input15204F112Q_of (hF : Input15204F112) : Input15204F112Q := by
  intro G _ _ T Mc M H K₁ K₂ π c _ hS hC₁ hC₂
  have hm := c.hyp111Mod hS hC₁ hC₂
  set N := l1Of T Mc M ⊔ K₁ ⊔ sOf T K₁ with hN
  have hL1N : l1Of T Mc M ≤ N := le_sup_left.trans le_sup_left
  have hK₁N : K₁ ≤ N := le_sup_right.trans le_sup_left
  have hbS : borelOf (l1Of T Mc M) (sOf T K₁) ≤ sOf T K₁ := c.borel₁_le.trans c.rc_le_S
  refine hF _ _ _ _ (hyp111_twoImg hm) ?_ (Or.inl ?_) ?_ ?_
  · rw [twoImg_sup_eq_top]
    exact isQuasithinSub_twoQuot (isQuasithinSub_of c.hs.qtfe.qtke N)
  · rw [twoImg_borelOf hm.pgroup hL1N (F7.isSylowTwoOf_pCoreOf_le hm.sylow) hm.sylow₁,
      sup_eq_left.2 (twoImg_mono hbS), Subgroup.subgroupOf_self]
    infer_instance
  · obtain ⟨f⟩ := nonempty_oTwoQuot_twoImg hL1N
    rcases c.y.iso.2.2 with ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩
    · exact Or.inl ⟨f.trans e⟩
    · exact Or.inr ⟨f.trans e⟩
  · obtain ⟨e⟩ := c.quot_K₁
    obtain ⟨f⟩ := nonempty_oTwoQuot_twoImg hK₁N
    exact ⟨f.trans e⟩

theorem input15204Dichotomy_of_F112 (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h39 : A39ForSQTK)
    (h15112 : StageLemma15112) (h15206 : StageLemma15206) (h15207 : StageLemma15207)
    (hF : Input15204F112) : Input15204Dichotomy :=
  input15204Dichotomy_of_F112Q h37 h38 h39 h15112 h15206 h15207 (input15204F112Q_of hF)

end CFSG.Quasithin.He9

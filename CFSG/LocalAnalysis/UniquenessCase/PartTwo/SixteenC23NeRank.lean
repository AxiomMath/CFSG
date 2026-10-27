module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC23NeNsDefs
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven2TwentyTwoSwapPair
public import CFSG.GroupTheory.ElementaryAbelianTransport
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenInfra
public import CFSG.Monster.B.Fischer.Fi22Order

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Quasithin.FFC CFSG.Open Subgroup
  CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

private theorem c23ne_rk_eq_three_of_card_eight {V₀ V : Subgroup G} {hV : IsElemAbelian 2 V}
    {W : Subgroup (Vtil V₀ V hV)} (hW : Nat.card ↥W = 8) : rk ↥W = 3 := by
  unfold rk
  rw [hW, show (8 : ℕ) = 2 ^ 3 by norm_num, padicValNat.prime_pow]

private theorem c23ne_rank_preTil_of_card_eight {V₀ V : Subgroup G} {hV : IsElemAbelian 2 V}
    {W : Subgroup (Vtil V₀ V hV)} (hW : Nat.card ↥W = 8) (hV₀V : V₀ ≤ V)
    (h2 : mSub V₀ = 2) : mSub (preTil V₀ V hV W) = 5 := by
  have hsum := s15_Infra_mSub_eq_rk_imgTil_add V₀ V (preTil V₀ V hV W) hV
    (preTil_le V₀ V hV W)
  rw [imgTil_preTil V₀ V hV W] at hsum
  have hle : V₀ ≤ preTil V₀ V hV W := by
    intro g hg
    rw [mem_preTil_iff_of_mem V₀ V hV _ (hV₀V hg)]
    have h1 : mkTil V₀ V hV (IntMod.mk hV ⟨g, hV₀V hg⟩) = 1 := by
      rw [← map_one (mkTil V₀ V hV), mkTil_eq_iff]
      change g * 1⁻¹ ∈ V₀
      simpa using hg
    rw [h1]
    exact Subgroup.one_mem _
  rw [inf_eq_right.2 hle, h2, c23ne_rk_eq_three_of_card_eight hW] at hsum
  omega

private theorem c23ne_rank_V_of_eq {D : Data G} {V₀ V L : Subgroup G}
    {hV : IsElemAbelian 2 V} {x : G} {K₁ K₂ : Subgroup G}
    (h : C23NeNs D V₀ V L hV x K₁ K₂) (h2 : mSub V₀ = 2) : mSub V = 8 := by
  have hsum := s15_Infra_mSub_eq_rk_imgTil_add V₀ V V hV le_rfl
  rw [s15_Infra_imgTil_top V₀ V hV, inf_eq_right.2 h.pf.le, h2] at hsum
  have hrk : rk ↥(⊤ : Subgroup (Vtil V₀ V hV)) = 6 := by
    unfold rk
    rw [Subgroup.card_top]
    have hcard : Nat.card (Vtil V₀ V hV) = 64 := c23_core_card_top h.ctx.core
    rw [hcard, show (64 : ℕ) = 2 ^ 6 by norm_num, padicValNat.prime_pow]
  rw [hrk] at hsum
  omega

theorem c23ne_rank_V₀_Y {D : Data G} {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V} {x : G}
    {K₁ K₂ : Subgroup G} (h : C23NeNs D V₀ V L hV x K₁ K₂) :
    mSub V₀ = 2 ∧ mSub (c23neY V K₁ K₂) = 1 := by
  have hYle : c23neY V K₁ K₂ ≤ V₀ := h.Y_le
  have hlt : c23neY V K₁ K₂ < V₀ := lt_of_le_of_ne hYle h.Y_ne
  have hcardlt : Nat.card ↥(c23neY V K₁ K₂) < Nat.card ↥V₀ := Subgroup.card_lt_of_lt hlt
  have hYpg : IsPGroup 2 ↥(c23neY V K₁ K₂) :=
    (CFSG.Open.IsElemAbelian.mono h.pf.elemAbelian₀ hYle).isPGroup
  have hVpg : IsPGroup 2 ↥V₀ := h.pf.elemAbelian₀.isPGroup
  have hYcard : Nat.card ↥(c23neY V K₁ K₂) = 2 ^ mSub (c23neY V K₁ K₂) :=
    card_eq_two_pow_mSub hYpg
  have hVcard : Nat.card ↥V₀ = 2 ^ mSub V₀ := card_eq_two_pow_mSub hVpg
  rw [hYcard, hVcard] at hcardlt
  have hlt' : mSub (c23neY V K₁ K₂) < mSub V₀ :=
    (Nat.pow_lt_pow_iff_right (by norm_num : 1 < 2)).1 hcardlt
  have hYne : mSub (c23neY V K₁ K₂) ≠ 0 := by
    intro h0
    have hc1 : Nat.card ↥(c23neY V K₁ K₂) = 1 := by rw [hYcard, h0, pow_zero]
    exact h.Y_ne_bot ((Subgroup.card_eq_one).1 hc1)
  have hYpos : 1 ≤ mSub (c23neY V K₁ K₂) := Nat.one_le_iff_ne_zero.2 hYne
  have hsmall := h.small
  omega

theorem c23ne_card_imgTil {D : Data G} {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V} {x : G}
    {K₁ K₂ : Subgroup G} (h : C23NeNs D V₀ V L hV x K₁ K₂) :
    Nat.card ↥(imgTil (c23neY V K₁ K₂) V hV V₀) = 2 := by
  have hYle : c23neY V K₁ K₂ ≤ V₀ := h.Y_le
  have hrk := c23ne_rank_V₀_Y h
  have hsum := s15_Infra_mSub_eq_rk_imgTil_add (c23neY V K₁ K₂) V V₀ hV h.pf.le
  rw [inf_eq_right.2 hYle, hrk.1, hrk.2] at hsum
  have hrk1 : rk ↥(imgTil (c23neY V K₁ K₂) V hV V₀) = 1 := by omega
  rw [CFSG.Quasithin.card_eq_two_pow (s15_Infra_vtil_sq_eq_one (c23neY V K₁ K₂) V hV)
    (imgTil (c23neY V K₁ K₂) V hV V₀), hrk1]
  norm_num

theorem c23ne_ranks {D : Data G} {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V} {x : G}
    {K₁ K₂ : Subgroup G} (h : C23NeNs D V₀ V L hV x K₁ K₂) (h2 : mSub V₀ = 2) :
    mSub V = 8 ∧ mSub (wSub V₀ V hV L) = 5 ∧ mSub (wSub V₀ V hV (conjSubgroup L x)) = 5 := by
  refine ⟨c23ne_rank_V_of_eq h h2, ?_, ?_⟩
  · rw [wSub]
    exact c23ne_rank_preTil_of_card_eight h.ctx.core.card₁ h.pf.le h2
  · rw [wSub]
    exact c23ne_rank_preTil_of_card_eight h.ctx.core.card₂ h.pf.le h2

theorem c23ne_sup_inf_blocks {D : Data G} {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V} {x : G}
    {K₁ K₂ : Subgroup G} (h : C23NeNs D V₀ V L hV x K₁ K₂) :
    wSub V₀ V hV L ⊔ wSub V₀ V hV (conjSubgroup L x) = V ∧
      wSub V₀ V hV L ⊓ wSub V₀ V hV (conjSubgroup L x) = V₀ := by
  refine ⟨?_, ?_⟩
  · unfold wSub
    rw [← s16c167_twenty_two_preTil_sup V₀ V hV, h.ctx.core.sup_eq, preTil_top]
  · unfold wSub
    rw [← s16c167_twenty_two_preTil_inf V₀ V hV, h.ctx.core.inf_eq, preTil_bot,
      inf_eq_right.2 h.pf.le]

theorem c23ne_perm_blocks {D : Data G} {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V} {x : G}
    {K₁ K₂ : Subgroup G} (h : C23NeNs D V₀ V L hV x K₁ K₂) :
    ∀ m ∈ D.M,
      (conjSubgroup (wSub V₀ V hV L) m = wSub V₀ V hV L ∧
        conjSubgroup (wSub V₀ V hV (conjSubgroup L x)) m =
          wSub V₀ V hV (conjSubgroup L x)) ∨
      (conjSubgroup (wSub V₀ V hV L) m = wSub V₀ V hV (conjSubgroup L x) ∧
        conjSubgroup (wSub V₀ V hV (conjSubgroup L x)) m = wSub V₀ V hV L) := by
  intro m hm
  have hms : m ∈ stabTil V₀ V := h.stab hm
  have hmem : actTil V₀ V hV ⟨m, hms⟩ ∈ Mbar D.M V₀ V hV :=
    actTil_mem_barSub V₀ V hV hm hms
  have hmem' : (actTil V₀ V hV ⟨m, hms⟩)⁻¹ ∈ Mbar D.M V₀ V hV :=
    (Mbar D.M V₀ V hV).inv_mem hmem
  have hperm := h.ctx.core.perm ((actTil V₀ V hV ⟨m, hms⟩)⁻¹) hmem'
  have hpre₁ : preTil V₀ V hV ((wTil V₀ V hV L).map
      ((actTil V₀ V hV ⟨m, hms⟩)⁻¹).toMonoidHom) =
      conjSubgroup (preTil V₀ V hV (wTil V₀ V hV L)) m :=
    s15_Infra_preTil_map_actTil V₀ V hV hms (wTil V₀ V hV L)
  have hpre₂ : preTil V₀ V hV ((wTil V₀ V hV (conjSubgroup L x)).map
      ((actTil V₀ V hV ⟨m, hms⟩)⁻¹).toMonoidHom) =
      conjSubgroup (preTil V₀ V hV (wTil V₀ V hV (conjSubgroup L x))) m :=
    s15_Infra_preTil_map_actTil V₀ V hV hms (wTil V₀ V hV (conjSubgroup L x))
  rcases hperm with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · left
    exact ⟨by unfold wSub; rw [← hpre₁, h1], by unfold wSub; rw [← hpre₂, h2]⟩
  · right
    exact ⟨by unfold wSub; rw [← hpre₁, h1], by unfold wSub; rw [← hpre₂, h2]⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo

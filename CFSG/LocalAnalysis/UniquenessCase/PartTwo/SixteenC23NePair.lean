module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC23NeModPair
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC23NeBridge
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC23AGen

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Quasithin.FFC CFSG.Open Subgroup
  CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

private theorem c23ne_preTil_pBlock {D : Data G} {V₀ V L L' : Subgroup G}
    {hV : IsElemAbelian 2 V} {x : G} {K₁ K₂ : Subgroup G}
    (h : C23NeNs D V₀ V L hV x K₁ K₂) :
    preTil (c23neY V K₁ K₂) V hV
      (c23nePBlock (c23neY V K₁ K₂) V₀ V hV h.Y_le (wTil V₀ V hV L')) =
        wSub V₀ V hV L' :=
  c23ne_preTil_comap hV h.Y_le _

theorem c23ne_pair_of_ns (D : Data G) {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V} {x : G}
    {K₁ K₂ : Subgroup G} (h154 : Hyp154 D V₀ V L) (h : C23NeNs D V₀ V L hV x K₁ K₂) :
    C23NePair D.M V₀ V (wSub V₀ V hV L) (wSub V₀ V hV (conjSubgroup L x)) (c23neY V K₁ K₂) := by
  have hrk := c23ne_rank_V₀_Y h
  have hr := c23ne_ranks h hrk.1
  have hP := c23ne_modPair_of_ns h
  have hw : wSub V₀ V hV (conjSubgroup L x) = conjSubgroup (wSub V₀ V hV L) x :=
    s15_Infra_wSub_conjSubgroup V₀ V L hV (h.stab h.ctx.hxM)
  have hOne := c23ne_bridge_oneSided hV (h.Y_le.trans h.pf.le) h.pf.le_normalizer h.Y_norm hrk.2 hP
  have hRk := c23ne_bridge_rankLe hV h.pf.le_normalizer h.Y_norm hP
  have hRk' := c23ne_bridge_rankLe hV h.pf.le_normalizer h.Y_norm hP.symm
  rw [c23ne_preTil_pBlock h, c23ne_preTil_pBlock h] at hOne hRk hRk'
  exact
  { elem := hV
    norm := h.pf.le_normalizer
    normV₀ := h.pf.le_normalizer₀
    normY := h.Y_norm
    le₁ := preTil_le V₀ V hV _
    le₂ := preTil_le V₀ V hV _
    sup := (c23ne_sup_inf_blocks h).1
    inf := (c23ne_sup_inf_blocks h).2
    leY := h.Y_le
    rank_V := hr.1
    rank_N₁ := hr.2.1
    rank_N₂ := hr.2.2
    rank_V₀ := hrk.1
    rank_Y := hrk.2
    perm := c23ne_perm_blocks h
    cent := fun w hw' hw1 => by
      rw [hw] at hw'
      exact c23a_cent_union D h154 h.ctx.hxM hw' hw1
    oneSided := hOne
    rankLe := hRk
    rankLe' := hRk' }

theorem c23ne_twoElt_of_ns {D : Data G} {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V} {x : G}
    {K₁ K₂ : Subgroup G} (h : C23NeNs D V₀ V L hV x K₁ K₂) :
    ∀ t ∈ D.M, (∃ j : ℕ, orderOf t = 2 ^ j) → ¬ V ≤ centralizer ({t} : Set G) →
      mSub (commElt V t) ≤ 2 →
        commElt V t ≤ wSub V₀ V hV L ∨ commElt V t ≤ wSub V₀ V hV (conjSubgroup L x) := by
  have hP := c23ne_modPair_of_ns h
  have hT := c23ne_bridge_twoElt hV (h.Y_le.trans h.pf.le) h.pf.le_normalizer h.Y_norm hP
  rw [c23ne_preTil_pBlock h, c23ne_preTil_pBlock h] at hT
  exact hT

end CFSG.LocalAnalysis.UniquenessCase.PartTwo

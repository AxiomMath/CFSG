module

public import CFSG.Quasithin.EmptyFaithful.S152He9N

public section

namespace CFSG.Quasithin.He9

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.LieType.BorelTits
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

theorem YCtx.normalizer_pCoreY_le {T Mc M : Subgroup G} (c : YCtx T Mc M) :
    Subgroup.normalizer (pCoreOf 2 (yOf152 T Mc M) : Set G) ≤ M := by
  have hloc : IsTwoLocal (Subgroup.normalizer (pCoreOf 2 (yOf152 T Mc M) : Set G)) :=
    ⟨pCoreOf 2 (yOf152 T Mc M), c.pCoreY_ne_bot, pCoreOf_isPGroup 2 _, rfl⟩
  have hMle : M ≤ Subgroup.normalizer (pCoreOf 2 (yOf152 T Mc M) : Set G) :=
    c.normal.trans (normalizer_le_normalizer_pCoreOf 2 _)
  have hM : quasithinIsMaxTwoLocal M := c.data.inM.1
  exact (hM.2 _ hloc hMle).le

namespace Ctx15204

variable {T Mc M H K₁ K₂ : Subgroup G} {π : ↥H →* W5} (c : Ctx15204 T Mc M H K₁ K₂ π)

include c

theorem pCoreY_le_S : pCoreOf 2 (yOf152 T Mc M) ≤ sOf T K₁ := c.y.pCoreY_le_rc.trans c.rc_le_S

theorem charTwo_G₀_of_inf_center (hJ : thompsonJ T ≤ sOf T K₁)
    (hU : IsUniqueM (yOf152 T Mc M ⊔ T) M) (hne : pCoreOf 2 (g0Of T Mc M K₁) ≠ ⊥)
    (hZ : pCoreOf 2 (g0Of T Mc M K₁) ⊓ (T ⊓ Subgroup.centralizer (T : Set G)) ≠ ⊥) :
    CharTwo (g0Of T Mc M K₁) := by
  obtain ⟨hSN, -⟩ := c.sylow_G₀ hJ hU hne
  have hN : g0Of T Mc M K₁ ≤ Subgroup.normalizer (pCoreOf 2 (g0Of T Mc M K₁) : Set G) :=
    le_normalizer_pCoreOf 2 _
  have hTtop : IsSylowTwoOf T ⊤ := isSylowTwoOf_of_le151 c.hs.qtfe.sylow le_top
  have hCN : CharTwo (Subgroup.normalizer (pCoreOf 2 (g0Of T Mc M K₁) : Set G)) :=
    charTwo_normalizer_of_inf_center c.hs.qtfe.qtke.2.1 hTtop (pCoreOf_isPGroup 2 _) hZ
  refine charTwo_of_relIndex_le_two hCN hSN hN ?_
  rw [Subgroup.relIndex_eq_one.mpr S_le_G₀]
  norm_num

theorem charTwo_G₀_of_charTwo_Lc {Lc : Subgroup G}
    (hn : (Lc.subgroupOf (g0Of T Mc M K₁)).Normal) (hKL : K₁ ≤ Lc) (hLcG : Lc ≤ g0Of T Mc M K₁)
    (hS : IsSylowTwoOf (sOf T K₁) (g0Of T Mc M K₁)) (hL : CharTwo Lc) :
    CharTwo (g0Of T Mc M K₁) := by
  have hQG : pCoreOf 2 (yOf152 T Mc M) ≤ g0Of T Mc M K₁ :=
    (c.pCoreY_le_S).trans S_le_G₀
  have hQM₁ : pCoreOf 2 (yOf152 T Mc M) ≤ pCoreOf 2 (M ⊓ g0Of T Mc M K₁) :=
    le_pCoreOf_of_le_normalizer (le_inf ((pCoreOf_le 2 _).trans c.y.hYM) hQG)
      (fun g hg => normalizer_le_normalizer_pCoreOf 2 _ (c.y.normal hg.1)) (pCoreOf_isPGroup 2 _)
  exact centralizer_pCoreOf_le_of_sup hn (c.g0_eq hKL hLcG) hL c.charTwo_M₁
    ⟨sOf T K₁, c.S_pgroup, c.S_le_M₁, hS.2.2⟩ hQM₁
    (fun g hg => ⟨c.y.normalizer_pCoreY_le hg.2, hg.1⟩)

omit c in
theorem charTwo_Lc_of_charTwo_G₀ {Lc : Subgroup G} (hn : (Lc.subgroupOf (g0Of T Mc M K₁)).Normal)
    (hLcG : Lc ≤ g0Of T Mc M K₁) (hG : CharTwo (g0Of T Mc M K₁)) : CharTwo Lc :=
  CharTwo.of_normal hG hLcG hn

end Ctx15204

@[expose] def Input15204OTwoZ : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T Mc M H K₁ K₂ : Subgroup G) (π : ↥H →* W5),
    Ctx15204 T Mc M H K₁ K₂ π → pCoreOf 2 (g0Of T Mc M K₁) ≠ ⊥ →
    IsSylowTwoOf (sOf T K₁) (g0Of T Mc M K₁) →
    ¬ pCoreOf 2 (yOf152 T Mc M) ≤ pCoreOf 2 (g0Of T Mc M K₁) →
    (T ⊓ Subgroup.centralizer (T : Set G)) ⊓ g0Of T Mc M K₁ ≤ pCoreOf 2 (g0Of T Mc M K₁)

@[expose] def Input15204CharTwoLc : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T Mc M H K₁ K₂ : Subgroup G) (π : ↥H →* W5),
    Ctx15204 T Mc M H K₁ K₂ π → pCoreOf 2 (g0Of T Mc M K₁) ≠ ⊥ →
    IsSylowTwoOf (sOf T K₁) (g0Of T Mc M K₁) →
    ¬ pCoreOf 2 (yOf152 T Mc M) ≤ pCoreOf 2 (g0Of T Mc M K₁) →
    ∀ Lc : Subgroup G, Lc ∈ cComp (g0Of T Mc M K₁) → K₁ ≤ Lc →
      (Lc.subgroupOf (g0Of T Mc M K₁)).Normal → CharTwo Lc

theorem input15204Dichotomy_of_charTwoLc (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h39 : A39ForSQTK)
    (hL : Input15204CharTwoLc) : Input15204Dichotomy := by
  intro G _ _ T Mc M H K₁ K₂ π c ho2 hS hP
  obtain ⟨Lc, hLc, hKL, hn⟩ := c.exists_Lc h37 h38 h39 ho2 hS
  exact c.charTwo_G₀_of_charTwo_Lc hn hKL (le_of_mem_cComp hLc) hS
    (hL G T Mc M H K₁ K₂ π c ho2 hS hP Lc hLc hKL hn)

end CFSG.Quasithin.He9

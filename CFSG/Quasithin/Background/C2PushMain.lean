module

public import CFSG.Quasithin.Background.C2PushThree
public import CFSG.Quasithin.Background.F1Models

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.C2Push
open scoped commutatorElement

@[expose] def ASC24OneMoved (G : Type) [Group G] [Finite G] : Prop :=
  ∀ H R M L : Subgroup G, HypC23 H R M → L ∈ cComp H → CharTwo L →
    CFSG.IsQuasisimple (↥L ⧸ CFSG.pCore 2 ↥L) →
    IsSylowTwoOf (R ⊓ L) L → ¬ R ≤ Subgroup.normalizer (L : Set G) →
      (L ≤ M ∨ (IsChi0Block H L ∧
        (∃ V : Subgroup G, IsTwoReducedIn (L ⊔ (R ⊓ Subgroup.normalizer (L : Set G))) V ∧
          ∃ A : Subgroup G, A ≤ R ⊓ Subgroup.normalizer (L : Set G) ∧
            IsFFOffender (L ⊔ (R ⊓ Subgroup.normalizer (L : Set G))) V A) ∧
        IsBorelOfBlock L (L ⊓ M)))

theorem asc24OneMoved_of_asc24One {G : Type} [Group G] [Finite G] (h : ASC24One G) :
    ASC24OneMoved G :=
  fun H R M L hyp hL hLc hLq hsyl _ => h H R M L hyp hL hLc hLq hsyl

variable {G : Type} [Group G] [Finite G]

theorem le_of_le_normalizer_of_hypC23 {T Mc M H R L : Subgroup G} (h : quasithinQTFE14Cat G T Mc)
    (hM : InM T M) (hyp : HypC23 M R H) (hL : L ∈ cComp M) (hLc : CharTwo L)
    (hLq : CFSG.IsQuasisimple (↥L ⧸ CFSG.pCore 2 ↥L))
    (hRN : R ≤ Subgroup.normalizer (L : Set G)) : L ≤ H := by
  have hMne : pCoreOf 2 M ≠ ⊥ := pCoreOf_ne_bot_of_isTwoLocal hM.1.1
  have hloc : quasithinIsLocal T L :=
    isLocal_of_mem_cComp_of_sylow (isSylowTwoOf_of_quasithinIsSylowTwo h.sylow hM.2) hMne hL
  have hXc : IsXClass L :=
    ⟨ne_bot_of_mem_cComp hL, eq_oTwoUpper_of_perfect (perfect_of_mem_cComp hL), hLc⟩
  have hRp : IsPGroup 2 R := hyp.radical.isPGroup
  have hRne : R ≠ ⊥ := hyp.radical.2.1
  have hrad : IsTwoRadicalIn (L ⊔ R) R :=
    isTwoRadicalIn_sup_of_le_normalizer hyp.radical hL hLq hRN
  have hPR : pCoreOf 2 (L ⊔ R) ≤ R := c2_1_pCore_le hrad
  have hcharLR : CharTwo (L ⊔ R) := A4.charTwo_sup hLc hRN hRp
  have hZR : omegaOneCenterOf R ≤ omegaOneCenterOf (pCoreOf 2 (L ⊔ R)) := by
    refine (Subgroup.closure_le _).mpr fun z hz => ?_
    obtain ⟨hzc, hz2⟩ := hz
    have hzR : z ∈ R := hzc.1
    have hzCP : z ∈ Subgroup.centralizer (pCoreOf 2 (L ⊔ R) : Set G) :=
      Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr hPR) hzc.2
    have hzP : z ∈ pCoreOf 2 (L ⊔ R) := hcharLR ⟨Subgroup.mem_sup_right hzR, hzCP⟩
    have hzΩ : z ∈ omegaOneCenterOf (pCoreOf 2 (L ⊔ R)) :=
      Subgroup.subset_closure ⟨⟨hzP, hzCP⟩, hz2⟩
    exact hzΩ
  have hVY : VY L = ⊥ := by
    by_contra hne
    exact h.faithful_empty L (isFaithfulLocal_iff_isXf.mpr ⟨hloc, hXc, hne⟩)
  have hsub : IsSubnormal L (L ⊔ R) :=
    A4.subnormal_of_normal le_sup_left
      ((Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).mpr
        (sup_le Subgroup.le_normalizer hRN))
  have hcomm1 : ⁅omegaOneCenterOf (pCoreOf 2 (L ⊔ R)), L⁆ = ⊥ := by
    by_contra hne
    exact (a4_9 hXc hsub).mp hne hVY
  have hcomm2 : ⁅L, omegaOneCenterOf R⁆ = ⊥ := by
    rw [Subgroup.commutator_comm]
    have h1 := Subgroup.commutator_mono hZR (le_refl L)
    rw [hcomm1] at h1
    exact le_bot_iff.mp h1
  have hZRne : omegaOneCenterOf R ≠ ⊥ :=
    CFSG.QuasithinUnique.Setup.omegaOneCenterOf_ne_bot hRp hRne
  have hLcent : L ≤ Subgroup.centralizer (omegaOneCenterOf R : Set G) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm2
  have hLM : L ≤ M := le_of_mem_cComp hL
  have hLcgs : L ≤ cgsIn M R := fun x hx =>
    inf_normalizer_le_cgsIn_of_char (A4.omegaOneCenterOf_le R) hZRne
      (CFSG.QuasithinUnique.Setup.characteristic_omegaOneCenterOf R)
      ⟨hLM hx, Subgroup.centralizer_le_normalizer _ (hLcent hx)⟩
  exact hLcgs.trans hyp.cgs

end CFSG.Quasithin

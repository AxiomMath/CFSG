module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenTwentyFiveShape
public import CFSG.Quasithin.Vol2.Ch11SecU1Mem2

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17

open Subgroup CFSG.Open CFSG.Quasithin CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo CFSG.LocalAnalysis.WeakClosure81
open CFSG.LocalAnalysis.RankThreeUC
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

theorem gap17_25_comap_centralizer_isPGroup
    {D : Data G} {V₀ V L : Subgroup G} (c : Ctx17_17 D V₀ V L)
    (h20 : R17_20At D V₀ V) (hC117 : C117 D V₀ V) (hJ2 : IsSpor (Bar2 L) .J2) :
    IsPGroup 2 ↥((Subgroup.centralizer (((barSub V₀ V c.hyp125.isElemAbelian L).subgroupOf
        (barSub V₀ V c.hyp125.isElemAbelian (L ⊔ D.T))) :
          Set ↥(barSub V₀ V c.hyp125.isElemAbelian (L ⊔ D.T)))).comap
      (gap17_25_action c.hyp125 c)) := by
  classical
  have hV := c.hyp125.isElemAbelian
  have hMnorm : D.M ≤ Subgroup.normalizer (L : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer c.mem_calC.1.le).1 (h20 L c).2.1
  have hL1 : barSub V₀ V hV L ≠ ⊥ := gap17_25_barSub_L_ne_bot c h20 hC117
  have hsimple : IsSimpleGroup (Bar2 L) := by
    obtain ⟨e⟩ := hJ2
    exact (MulEquiv.isSimpleGroup_congr e).mpr CFSG.Sporadic.J2.isSimpleGroup_J2
  set Y : Subgroup (MulAut (Vtil V₀ V hV)) := barSub V₀ V hV (L ⊔ D.T)
  set K : Subgroup ↥Y := (barSub V₀ V hV L).subgroupOf Y
  have hKspor : IsSpor ↥K .J2 := gap17_25_barSub_isSpor c hJ2 hL1
  obtain ⟨eK⟩ := hKspor
  have hsimpleK : IsSimpleGroup ↥K :=
    (MulEquiv.isSimpleGroup_congr eK).mpr CFSG.Sporadic.J2.isSimpleGroup_J2
  have hcardK : Nat.card ↥K = 604800 :=
    (Nat.card_congr eK.toEquiv).trans CFSG.Sporadic.J2.card_J2
  have hcenterK : Subgroup.center ↥K = ⊥ :=
    @CFSG.Quasithin.H13.FiveNorm.center_eq_bot_of_card_not_prime ↥K _ hsimpleK (by
      rw [hcardK]
      norm_num)
  have hKnormal : K.Normal := gap17_25_barSub_normal c hMnorm
  have hLC : K ⊓ Subgroup.centralizer (K : Set ↥Y) = ⊥ := by
    refine le_bot_iff.1 fun x hx => ?_
    have hxK : x ∈ K := hx.1
    have hxc : (⟨x, hxK⟩ : ↥K) ∈ Subgroup.center ↥K := by
      rw [Subgroup.mem_center_iff]
      intro y
      apply Subtype.ext
      exact Subgroup.mem_centralizer_iff.1 hx.2 (y : ↥Y) y.2
    have hx1 : (⟨x, hxK⟩ : ↥K) = 1 := by
      simpa [hcenterK] using hxc
    exact Subgroup.mem_bot.2 (by
      have h := congrArg (fun z : ↥K => (z : ↥Y)) hx1
      simpa using h)
  obtain ⟨n, hn⟩ := exists_index_barSub_pow_two c.hyp125 c hMnorm
  have hnK : K.index = 2 ^ n := by
    simpa only [K, Y] using hn
  have htwo : ∀ q : ↥Y, ∃ k : ℕ, q ^ 2 ^ k ∈ K := by
    intro q
    exact ⟨n, by
      simpa [hnK] using @Subgroup.pow_index_mem ↥Y _ K hKnormal q⟩
  have hC2 : IsPGroup 2 (Subgroup.centralizer (K : Set ↥Y)) :=
    CFSG.Quasithin.Vol2.Ch11.SecU1.Comp.isPGroup_two hLC htwo
  have hker : IsPGroup 2 (gap17_25_action c.hyp125 c).ker :=
    gap17_25_action_ker_isPGroup c.hyp125 c hMnorm hsimple hL1
  change IsPGroup 2 ↥((Subgroup.centralizer (K : Set ↥Y)).comap
    (gap17_25_action c.hyp125 c))
  exact IsPGroup.comap_of_ker_isPGroup hC2 (gap17_25_action c.hyp125 c) hker

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17

module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs16a
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenCore
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenKbar
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenLin
public import Certificates.Kernel.J4Count.FixCE
public import CFSG.Certificates.Kernel.LocalCompTits.Span
public import CFSG.LocalAnalysis.ComponentInitial.PGroupRankOneClassification
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239PairsSporSimpleTop
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Vol2NativeListed
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Vol2NativeThree
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.Equivariance
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.SL2ModulesBorel
public import CFSG.Quasithin.Background.A3Structure318Red
public import CFSG.Quasithin.Background.A3Structure36A
public import CFSG.Quasithin.Background.A3Structure36BAction
public import CFSG.Quasithin.Background.A3Structure36BBase
public import CFSG.Quasithin.Background.A3Structure36BCase3Base
public import CFSG.Quasithin.Background.A3Structure36BCasesBase
public import CFSG.Quasithin.Background.A3Structure36BCommonBase
public import CFSG.Quasithin.Background.A3Structure36BFrattini
public import CFSG.Quasithin.Background.A3Structure36BHeisBase
public import CFSG.Quasithin.Background.A3Structure36BHomocyclic
public import CFSG.Quasithin.Background.A3Structure36BPrimeDataBase
public import CFSG.Quasithin.Background.A3Structure36BStarBase
public import CFSG.Quasithin.Background.A3Structure36Base
public import CFSG.Quasithin.Background.A3Structure37Base
public import CFSG.Quasithin.Background.A3Structure37Comm
public import CFSG.Quasithin.Background.A3Structure37Frattini
public import CFSG.Quasithin.Background.A3Structure37KeyBase
public import CFSG.Quasithin.Background.A3Structure37Schur
public import CFSG.Quasithin.Background.A3Structure38Part3
public import CFSG.Quasithin.Background.B1MoreElevenE
public import CFSG.Quasithin.Background.B1MoreNineG
public import CFSG.Quasithin.Background.B4ModelsAction
public import CFSG.Quasithin.Background.B4ModelsIso
public import CFSG.Quasithin.Background.C2Basic
public import CFSG.Quasithin.Background.C2Inputs
public import CFSG.Quasithin.Background.E3Cent
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtJ4LocCheck
public import CFSG.Quasithin.Vol2.Ch1Local
public import Certificates.Data.CFSGNative.MonsterB.Rep4371Model
public import Certificates.Kernel.J4Count.FixCPairBase1
public import Certificates.Kernel.J4Count.KFactsBase

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

section Concrete

variable {D : Data G} {V₀ V L : Subgroup G}

theorem s15_Three_wStar_eq_bot (h : Hyp151 D V₀ V L) (hV : IsElemAbelian 2 V)
    (hL : barSub V₀ V hV L = ⊥) : wStar D.M V₀ V hV L = ⊥ := by
  have hWeq : wSub V₀ V hV L = V₀ := s15_Infra_wSub_eq_of_barSub_eq_bot h.hyp125 hV hL
  exact s15_Core_imgTil_eq_bot_of_le (V₀ := v1Sub D.M V₀ V hV L) (V := V)
    (U := wSub V₀ V hV L) hV (by rw [hWeq]; exact s15_Infra_le_v1Sub D.M V₀ V hV L)

theorem s15_Three_barSub_ne_bot (h : Hyp151 D V₀ V L)
    {φ : MulAut (vStar D.M V₀ V h.isElemAbelian L)}
    (hφ : InducesTransvection φ (wStar D.M V₀ V h.isElemAbelian L)) :
    barSub V₀ V h.isElemAbelian L ≠ ⊥ := by
  intro hL
  have h1 := hφ.2
  rw [s15_Three_wStar_eq_bot h h.isElemAbelian hL,
    commSub_eq_bot_iff.2 (bot_le : (⊥ : Subgroup _) ≤ fixV (Subgroup.zpowers φ)), rk_bot] at h1
  omega

theorem s15_Three_stableUnder_wStar (h : Hyp151 D V₀ V L) (hV : IsElemAbelian 2 V) :
    StableUnder (lStar D.M V₀ V hV L) (wStar D.M V₀ V hV L) := by
  intro x hx u hu
  obtain ⟨g, hgL, rfl⟩ := (mem_barSub (v1Sub D.M V₀ V hV L) V hV L x).1 hx
  have hgM : (g : G) ∈ D.M := h.le hgL
  have hgn : (g : G) ∈ nBar D.M V₀ V hV L := by
    rw [s15_Infra_mem_nBar_iff h.hyp125 hV hgM,
      conjSubgroup_eq_iff_mem_normalizer.2 (Subgroup.le_normalizer hgL)]
  rw [← preBarSub_stabSub_wStar D h hV] at hgn
  obtain ⟨-, hh, he⟩ := (mem_preBarSub _ _ _ hV _).1 hgn
  exact (mem_stabSub.1 he u).2 hu

theorem s15_Three_commSub_wStar (h : Hyp151 D V₀ V L) (hV : IsElemAbelian 2 V) :
    commSub (wStar D.M V₀ V hV L) (lStar D.M V₀ V hV L) = wStar D.M V₀ V hV L := by
  have hMs1 : D.M ≤ stabTil (v1Sub D.M V₀ V hV L) V :=
    le_stabTil h.hyp125.pairFacts.le_normalizer (s15_Infra_le_normalizer_v1Sub h.hyp125 hV)
  have hWcomm : commSub (wTil V₀ V hV L) (barSub V₀ V hV L) = wTil V₀ V hV L := by
    have h1 := s15_Lin_commSub_commSub_eq_of_no_two_quotient (s15_Infra_vtil_sq_eq_one V₀ V hV)
      (s15_Kbar_no_two_quotient h)
    simpa only [wTil] using h1
  apply le_antisymm
  · rw [commSub, Subgroup.closure_le]
    rintro c ⟨x, hx, w, hw, rfl⟩
    exact (wStar D.M V₀ V hV L).mul_mem (s15_Three_stableUnder_wStar h hV x hx w hw)
      ((wStar D.M V₀ V hV L).inv_mem hw)
  · set C := commSub (wStar D.M V₀ V hV L) (lStar D.M V₀ V hV L) with hC
    set S := preTil (v1Sub D.M V₀ V hV L) V hV C with hS
    have hV₀S : V₀ ≤ S := by
      intro v hv
      have hvV : v ∈ V := by
        have := h.hyp125.pairFacts.le
        exact this hv
      rw [hS, mem_preTil_iff_of_mem _ _ hV _ hvV]
      have : mkTil (v1Sub D.M V₀ V hV L) V hV (IntMod.mk hV ⟨v, hvV⟩) = 1 := by
        rw [← map_one (mkTil (v1Sub D.M V₀ V hV L) V hV), mkTil_eq_iff]
        change v * (1 : G)⁻¹ ∈ v1Sub D.M V₀ V hV L
        simpa using s15_Infra_le_v1Sub D.M V₀ V hV L hv
      rw [this]
      exact C.one_mem
    set Q := imgTil V₀ V hV S with hQ
    have hwQ : wTil V₀ V hV L ≤ Q := by
      rw [← hWcomm, commSub, Subgroup.closure_le]
      rintro c ⟨x', hx', u, hu, rfl⟩
      obtain ⟨g, hgL, rfl⟩ := (mem_barSub V₀ V hV L x').1 hx'
      obtain ⟨y, rfl⟩ := mkTil_surjective V₀ V hV u
      have hyW : y.val ∈ wSub V₀ V hV L := by
        rw [wSub, mem_preTil]
        exact ⟨y, rfl, hu⟩
      have hg1 : (g : G) ∈ stabTil (v1Sub D.M V₀ V hV L) V := hMs1 (h.le hgL)
      have hgs : actStab V₀ V hV g y = actStab (v1Sub D.M V₀ V hV L) V hV ⟨g, hg1⟩ y := by
        apply IntMod.val_injective
        rw [actStab_apply_val, actStab_apply_val]
      show _ ∈ imgTil V₀ V hV S
      rw [mem_imgTil]
      refine ⟨actStab V₀ V hV g y * y⁻¹, ?_, ?_⟩
      · rw [hS, mem_preTil]
        refine ⟨actStab V₀ V hV g y * y⁻¹, rfl, ?_⟩
        rw [map_mul, map_inv, hgs, ← actTil_mk]
        refine Subgroup.subset_closure ⟨_, actTil_mem_barSub _ V hV hgL hg1, _, ?_, rfl⟩
        exact (mem_imgTil _ V hV _ _).2 ⟨y, hyW, rfl⟩
      · rw [map_mul, map_inv, ← actTil_mk]
    intro q hq
    obtain ⟨z, hzW, rfl⟩ := (mem_imgTil (v1Sub D.M V₀ V hV L) V hV (wSub V₀ V hV L) q).1 hq
    have hzmem : mkTil V₀ V hV z ∈ wTil V₀ V hV L := by
      obtain ⟨a, ha, hamem⟩ := (mem_preTil V₀ V hV (wTil V₀ V hV L)).1 hzW
      rwa [IntMod.val_injective ha] at hamem
    obtain ⟨s, hsS, hsz⟩ := (mem_imgTil V₀ V hV S _).1 (hwQ hzmem)
    have hzs : z.val * s.val⁻¹ ∈ S := by
      have h1 := (mkTil_eq_iff V₀ V hV s z).1 hsz
      have h2 : z.val * s.val⁻¹ = (s.val * z.val⁻¹)⁻¹ := by group
      rw [h2]
      exact S.inv_mem (hV₀S h1)
    have hzS : z.val ∈ S := by
      have := S.mul_mem hzs hsS
      simpa using this
    obtain ⟨a, ha, hamem⟩ := (mem_preTil _ V hV C).1 hzS
    rwa [IntMod.val_injective ha] at hamem

end Concrete

end CFSG.LocalAnalysis.UniquenessCase.PartTwo

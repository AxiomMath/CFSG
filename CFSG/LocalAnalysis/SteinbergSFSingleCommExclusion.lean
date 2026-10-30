module

public import CFSG.LocalAnalysis.SteinbergSFSingleCommParts
public import CFSG.LocalAnalysis.EvenBN.Sp4.Main
public import CFSG.LocalAnalysis.EvenBN.Sp4.SliceSylowBootstrap
public import CFSG.LocalAnalysis.EvenBN.Sp4.BothTrivialField
public import Certificates.Kernel.ThCent.Leaves

public section

namespace CFSG.LocalAnalysis.EvenBN.Sp4

open Subgroup CFSG.Open CFSG.Blueprint
open CFSG.LocalAnalysis.SymplecticFourStandard GomiFusion
open CFSG.LocalAnalysis.SymplecticFourStandard.SingleCommParts
  (SCSetting SixHStatement EmbStatement SixKStatement FieldFusionStatement CanonicityStatement)
open CFSG.ComponentClassification.UnbalancedCatalog.SpChain CFSG.QuasithinUnique.Setup.X7b
  CFSG.RankThree.PartOne.KCRootAxis

theorem singleCommutatorExclusion_of_parts
    (hPartH : SixHStatement) (hPartEmb : EmbStatement) (hPartK : SixKStatement)
    (hPartFF : FieldFusionStatement) (hPartN5 : CanonicityStatement) :
    SingleCommutatorExclusion := by
  intro G _ _ _ hKP hcore L hL n hn K _ _ _ hK T hT t htT ht P φ hφP i
  intro TG PG Q ZP U A V B M N D E E₀ J₀ F Fi hfull hne hbot
  have ht2 : orderOf (t : G) = 2 := (Subgroup.orderOf_coe t).trans ht
  have hct : standardComponentOddCore (centralizer ({(t : G)} : Set G)) = ⊥ := hcore _ ht2
  obtain ⟨hO, hLn, hperf⟩ := standard_simple_setting hL hn hK φ T hT htT ht hct
  have hS := setup_of_standard hL hn hK φ T hT htT ht hct
  have hPG : PG = pull φ (antiUnipotent K) := by
    change (P : Subgroup L).map L.subtype = ((antiUnipotent K).comap φ.toMonoidHom).map L.subtype
    rw [← hφP, comap_map_eq_self_of_injective φ.injective]
  have hZP : ZP = pull φ (antiUnipotentCenter K) := by
    change (center ↥PG).map PG.subtype = _
    rw [hPG, center_pull_antiUnipotent]
  have hfull' : {x : G | ∃ m ∈ normalizer ((pull φ (antiUnipotent K) ⊔ TG : Subgroup G) :
      Set G), x = m⁻¹ * (t : G) * m} =
      {x | ∃ z ∈ pull φ (antiUnipotentCenter K), x = (t : G) * z} := by
    rw [← hPG, ← hZP]
    exact hfull
  obtain ⟨hTG₀, hF⟩ := FullCenter.FCHyp.of_setup hS (hO := hO) hLn hfull'
  have hnab : ∃ a b : G, a * b ≠ b * a := by
    by_contra hab
    push Not at hab
    exact hLn ⟨fun l hl g => by
      rw [hab g l, mul_inv_cancel_right]
      exact hl⟩
  have hTG : TG = zpowers (t : G) := hTG₀
  clear_value ZP PG TG
  subst hTG hPG hZP
  have hSet : SCSetting L K n φ (t : G) i :=
    { kproper := hKP, nonabelian := hnab, oddCore := hO, standard := hL, not_normal := hLn,
      oddCore_centralizer := hct, fc := hF, ne_bot := hne, eq_bot := hbot }
  have hHc := hPartH hSet
  have hEc := hPartEmb hSet hHc
  have hKc := hPartK hSet hHc hEc
  have hFc := hPartFF hSet hHc hEc hKc
  have hNc := hPartN5 hSet
  have hST : SingleCommParts.S φ (t : G) i ≤ SingleCommParts.Tplus φ (t : G) i :=
    hHc.sup_t ▸ le_sup_left
  have hQT : pull φ (antiUnipotent K) ⊔ zpowers (t : G) ≤ SingleCommParts.Tplus φ (t : G) i :=
    le_sup_left.trans (le_sup_left.trans (le_sup_left.trans le_sup_left))
  have htS : (t : G) ∉ SingleCommParts.S φ (t : G) i := fun h => by
    have : (t : G) ∈ SingleCommParts.S φ (t : G) i ⊓ zpowers (t : G) := ⟨h, mem_zpowers _⟩
    rw [hHc.inf_t] at this
    exact hS.t_ne_one (mem_bot.mp this)
  have hPS : pull φ (antiUnipotent K) ≤ SingleCommParts.S φ (t : G) i := by
    exact hKc.centralizer_S.symm.le.trans inf_le_left
  have hfr : ∀ g ∈ normalizer (SingleCommParts.Tplus φ (t : G) i : Set G),
      ∃ s ∈ SingleCommParts.S φ (t : G) i, g * s⁻¹ ∈ centralizer ({(t : G)} : Set G) := by
    intro g hg
    have htT : (t : G) ∈ SingleCommParts.Tplus φ (t : G) i := hQT (mem_sup_right (mem_zpowers _))
    have hgT : g⁻¹ * (t : G) * g ∈ SingleCommParts.Tplus φ (t : G) i :=
      (mem_normalizer_iff''.mp hg _).mp htT
    obtain ⟨s, hs, hgs⟩ := hKc.slice g hgT
    refine ⟨s, hs, ?_⟩
    rw [mem_centralizer_singleton_iff]
    calc g * s⁻¹ * (t : G) = g * (s⁻¹ * (t : G) * s) * s⁻¹ := by group
      _ = g * (g⁻¹ * (t : G) * g) * s⁻¹ := by rw [hgs]
      _ = (t : G) * (g * s⁻¹) := by group
  haveI : Group.IsPerfect G := hperf
  exact false_of_slice ht2 hF.setup.cent_le (exists_sylow_pull φ) hHc.isPGroup_Tplus hQT hST hNc
    hFc.slice htS fun W hW hTW hWN =>
      BothTrivialField.isMulCommutative_quot hF.setup hfr hFc.normalizer_le hST hPS hQT hW hTW hWN

end CFSG.LocalAnalysis.EvenBN.Sp4


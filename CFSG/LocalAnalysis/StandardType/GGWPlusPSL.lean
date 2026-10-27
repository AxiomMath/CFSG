module

public import CFSG.LocalAnalysis.StandardType.GGWPlusDefs
public import CFSG.LocalAnalysis.StandardType.GGWPlusAutomizer
public import CFSG.LocalAnalysis.StandardType.GGWPlusPosition
public import CFSG.LocalAnalysis.StandardType.GGWPlusModel
public import CFSG.LocalAnalysis.StandardType.GGTableBTypeATorus
public import CFSG.LocalAnalysis.StandardType.GGPGLTorality
public import CFSG.LocalAnalysis.StandardType.GGSixStepTwoAutK

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly TableB CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag TypeA

theorem ggWPlusTableB_PSL {d p : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    (hp : p.Prime) (hp2 : p ≠ 2) (hpK : p ∣ Nat.card K - 1) (hd : 5 ≤ d) (h4 : 4 ≤ Nat.card K)
    (hsec : SLHasSections d K) :
    GGWPlusTableB p (projectiveSL d K) (Set.range (conjAut d K)) := by
  intro M _ _ L' E θ hE hP hZ A M₁ E₁ h hXA hAN hAp hME hEA hCM hAM hAE hpow hh hhp hAh
  have hL : GGTorusLift p (d - 2) (projectiveSL d K) :=
    TypeA.ggTorusLift_sub_two hp hpK (by omega) hsec
  have hr : p ^ (d - 2) ≤ Nat.card (ggLAutImage L' θ E) :=
    pow_le_card_ggLAutImage hP hp hL
  have hsc : GGTorusSelfCent p (ggLAutImage L' θ E) :=
    ggTorusSelfCent_ggLAutImage hP hp hZ
  have hA : IsElemAbelian p (ggLAutImage L' θ E) :=
    ggIsElemAbelian_map (ggIsElemAbelian_subgroupOf hP.2.1 _) (ggLAut L' θ)
  have hI : (ggLAutImage L' θ E : Set (MulAut (projectiveSL d K))) ⊆
      Set.range (conjAut d K) := by
    intro a ha
    simp only [ggLAutImage, Subgroup.mem_map] at ha
    obtain ⟨x, hx, rfl⟩ := ha
    have hxe : (⟨(x : M), hE hx⟩ : Subgroup.normalizer (L' : Set M)) = x :=
      Subtype.ext rfl
    rw [← hxe]
    exact hP.2.2.2.1 ⟨(x : M), hx⟩
  have hX := ggSolvQuotLeTwo_PSL hp hp2 hpK hd h4 hsec hA hI hr hsc
  haveI : ((MulAut.conj : projectiveSL d K →* MulAut (projectiveSL d K)).range).Normal :=
    ggInnNormal _
  haveI : Finite (MulAut (projectiveSL d K)) :=
    Finite.of_injective (fun f : MulAut (projectiveSL d K) =>
      (f : projectiveSL d K → projectiveSL d K)) DFunLike.coe_injective
  exact wplus_of_automizer hp hp2 _
    (ggLAutImage L' θ E) hX A M₁ E₁ hXA hAN hAp hME hEA hCM hAM hAE hpow h hh hAh

end CFSG.StandardType

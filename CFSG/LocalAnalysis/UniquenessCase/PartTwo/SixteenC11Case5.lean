module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC11Case5GlueB
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC11Case5GlueC
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenResults10

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
  CFSG.LocalAnalysis.WeakClosure81

variable {G : Type} [Group G] [Finite G]

private theorem s16c11_case5_barSub_wClos {V₀ V X : Subgroup G} (hV : IsElemAbelian 2 V)
    (hX : X ≤ stabTil V₀ V) :
    barSub V₀ V hV (E3.wClos V 0 X) = ⨆ A ∈ E3.gammaSet V 0 X, barSub V₀ V hV A := by
  unfold E3.wClos
  rw [barSub_iSup_of_le hV (K := fun A => ⨆ (_ : A ∈ E3.gammaSet V 0 X), A)
    (fun A => iSup_le fun hA => hA.1.trans hX)]
  exact iSup_congr fun A =>
    barSub_iSup_of_le hV (K := fun _ : A ∈ E3.gammaSet V 0 X => A)
      (fun hA => hA.1.trans hX)

theorem s16c11_normalizer_le_of_case5 (D : Data G) (hin : In10 D) (h1217 : R1217 D)
    (h1610 : R16_10_2 D) {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (hc : Counterex16 D V₀ V L hV) (hout : Out10 D V₀ V hV) (h5 : Case168_5 D V₀ V hV L) :
    normalizer (E3.wClos V 0 D.T : Set G) ≤ D.M := by
  classical
  have h125 : Hyp125 D V₀ V := hc.setting.hyp16.hyp125
  have hTst : D.T ≤ stabTil V₀ V :=
    D.sylowM.le.trans (le_stabTil h125.pairFacts.le_normalizer h125.pairFacts.le_normalizer₀)
  let 𝒮 : Set (Subgroup (MulAut (Vtil V₀ V hV))) :=
    barSub V₀ V hV '' E3.gammaSet V 0 D.T
  have hjoin : (⨆ A ∈ 𝒮, A) = barSub V₀ V hV (E3.wClos V 0 D.T) := by
    change (⨆ A ∈ barSub V₀ V hV '' E3.gammaSet V 0 D.T, A) =
      barSub V₀ V hV (E3.wClos V 0 D.T)
    rw [iSup_image]
    exact (s16c11_case5_barSub_wClos hV hTst).symm
  have h𝒮 : ∀ A ∈ 𝒮, A = ⊥ ∨ A ∈ E3.aSet 2 (Mbar D.M V₀ V hV) := by
    rintro A ⟨B, hB, rfl⟩
    exact s16c11_case5_gamma_dichotomy D hin hc hout h5 hB
  have h2 : IsPGroup 2 ↥(⨆ A ∈ 𝒮, A) := by
    rw [hjoin]
    refine IsPGroup.to_le ?_ (barSub_mono V₀ V hV (wClos_zero_le V D.T))
    unfold barSub
    exact (IsPGroup.comap_subtype (K := stabTil V₀ V) D.sylowM.isPGroup).map
      (actTil V₀ V hV)
  obtain ⟨P, hPY, hPp, hPc, hPN⟩ :=
    s16c11_case5_core_of_natOmegaPlus h5.2.2.1
      (barSub_mono V₀ V hV hc.setting.hyp151.le) (s16c11_case5_mbar_le_normalizer D hc h5)
      (s16c11_case5_dvd_card_mbar D h5) h𝒮 h2
  have hPW : P ≤ normalizer ((barSub V₀ V hV (E3.wClos V 0 D.T) : Subgroup _) : Set _) := by
    rw [← hjoin]
    exact hPN
  have hp3 : 3 ∈ D.sig := by
    rw [h5.2.2.2]
    exact Set.mem_singleton 3
  exact s16c11_normalizer_le_of_bar_noncyclic D hin.h61 hV h125 hp3 hPY hPp hPc hPW

end CFSG.LocalAnalysis.UniquenessCase.PartTwo

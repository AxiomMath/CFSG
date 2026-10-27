module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1Ch47Defs
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1Ch47OrdA
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1Ch47OrdB
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1Ch47OrdC
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenResultsB

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

theorem s16c1_cases_of_gaps (D : Data G) (h45 : R16_45 D) (hord : R16_47_ord_gap D)
    {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V} (hS : Sect16 D V₀ V L hV)
    (hc : Case167_1 D V₀ V hV L) (hL : L ∈ calC D.M) (hU4 : IsU4 (Bar2 L) 1)
    {x : IntMod V hV} (hx : Setup1645 D V hV x) (hch : Chosen1647 D V₀ V x.val)
    (hSyl : IsSylowIn 2 (D.T ⊓ centralizer ({x.val} : Set G)) (centralizer ({x.val} : Set G)))
    (h46 : Concl1646 L x.val) (hcard : Nat.card ↥V = 2 * Nat.card ↥(uOne V x.val)) :
    ∀ h ∈ centralizer ({x.val} : Set G), ∀ w ∈ V,
      w ∉ pCoreOf 2 (centralizer ({x.val} : Set G)) →
        ⁅w, h⁻¹ * w * h⁆ ∈ pCoreOf 2 (centralizer ({x.val} : Set G)) ∨
          ∃ d ∈ ({3, 5, 17} : Set ℕ),
            (w * (h⁻¹ * w * h)) ^ d ∈ pCoreOf 2 (centralizer ({x.val} : Set G)) := by
  intro h hh w hwV hw
  by_cases hcomm : ⁅w, h⁻¹ * w * h⁆ ∈ pCoreOf 2 (centralizer ({x.val} : Set G))
  · exact Or.inl hcomm
  right
  have hP := hS.setting.hyp151.hyp125.pairFacts
  have hVc : InCalV D.M V := hyp123_inCalV hS.setting.hyp151.hyp125.1
  have hzV : x.val ∈ V := x.val_mem
  obtain ⟨hVM, hMV⟩ := s16c1_not_le_of_noncomm hVc hzV hcard hh hwV hw hcomm
  have hQM : pCoreOf 2 (centralizer ({x.val} : Set G)) ≤ D.M := s16c1_pCoreOf_le_M D hSyl
  have hV₀M : V₀ ≤ D.M := hP.le.trans hP.le_M
  have hO : InCalO 1 D.M V₀ V h := by
    refine s16c1_inCalO_one' hP.elemAbelian hQM hh hcard hVM hMV (fun hne => ?_) (fun hne => ?_)
    · exact (s16c1_V₀_inter_conj_ne_bot D hP.elemAbelian hP.le hV₀M hP.le_normalizer₀ hne hzV
        hx.ne_one hSyl hh).1
    · exact (s16c1_V₀_inter_conj_ne_bot D hP.elemAbelian hP.le hV₀M hP.le_normalizer₀ hne hzV
        hx.ne_one hSyl hh).2
  have hstar : conjSubgroup V h ∈ calOStar 1 D.M V₀ V := by
    rw [← h45 V₀ V L hV hS hc]
    exact ⟨h, rfl, hO⟩
  exact hord V₀ V L hV hS hc hL hU4 x hx hch hSyl h46 hcard h hh hstar w hwV hw hcomm

end CFSG.LocalAnalysis.UniquenessCase.PartTwo

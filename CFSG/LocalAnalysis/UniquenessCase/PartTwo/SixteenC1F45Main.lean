module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenResultsB
public import CFSG.LocalAnalysis.WeakClosure81.SixFiveL

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

theorem s16c1_45_bot {D : Data G} (h43 : R16_43_4 D) {V₀ V L : Subgroup G}
    {hV : IsElemAbelian 2 V} (hS : Sect16 D V₀ V L hV) (hc : Case167_1 D V₀ V hV L)
    (hV₀ : V₀ = ⊥) {g : G} (h1 : InCalO 1 D.M V₀ V g) :
    conjSubgroup V g ∈ calOStar 1 D.M V₀ V := by
  have hVg : ¬ conjSubgroup V g ≤ D.M := h1.1.1
  have hVM : ¬ V ≤ conjSubgroup D.M g := h1.2.1
  have hm : E3.mQuot (conjSubgroup V g) D.M ≤ 1 := h1.2.2.1
  have hVg2 : IsPGroup 2 (conjSubgroup V g) :=
    E3.isPGroup_conjSubgroup (CFSG.Open.IsElemAbelian.isPGroup hV) g
  have hmq : E3.mQuot (conjSubgroup V g) (conjSubgroup V g ⊓ D.M) =
      E3.mQuot (conjSubgroup V g) D.M := by
    unfold E3.mQuot
    rw [Subgroup.inf_relIndex_left]
  have hm1 : E3.mQuot (conjSubgroup V g) (conjSubgroup V g ⊓ D.M) = 1 := by
    rw [hmq]
    have hne : E3.mQuot (conjSubgroup V g) D.M ≠ 0 := by
      intro h0
      have h0' : E3.mQuot (conjSubgroup V g) (conjSubgroup V g ⊓ D.M) = 0 := hmq.trans h0
      have heq : conjSubgroup V g ⊓ D.M = conjSubgroup V g :=
        (E3.mQuot_eq_zero_iff hVg2 inf_le_left).1 h0'
      exact hVg (heq ▸ inf_le_right)
    omega
  have hA : (conjSubgroup V g ⊓ D.M) ∈ E3.gammaSet V 1 D.M :=
    ⟨inf_le_right, g, inf_le_left, hm1⟩
  have hyp : Hyp1643 D V₀ V 1 (conjSubgroup V g ⊓ D.M) g :=
    ⟨Or.inr ⟨hV₀, rfl⟩, hA, inf_le_left⟩
  rcases h43 V₀ V L hV hS hc 1 (conjSubgroup V g ⊓ D.M) g hyp hV₀ with hle | hstar
  · exact absurd hle hVM
  · exact hstar.1

theorem s16c1_45_hyp65 {D : Data G} {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (hS : Sect16 D V₀ V L hV) (hV₀ : V₀ ≠ ⊥) {g : G} (h1 : InCalO1 1 D.M V₀ V g) :
    CFSG.LocalAnalysis.WeakClosure81.Hyp65 1 D.M V₀ V g := by
  have h : Hyp125 D V₀ V := hS.setting.hyp16.hyp125
  have hp := h.pairFacts
  have hV₀in : InCalV D.M V₀ :=
    ⟨hV₀, hp.le.trans hp.le_M, hp.le_normalizer₀, hp.elemAbelian₀⟩
  have hTI₀ : CFSG.CGT.Timmesfeld75.IsTI V₀ := by
    rcases h.1 with ⟨-, hbot⟩ | h2
    · exact absurd hbot hV₀
    · exact h2.1.2.2.2.1
  exact ⟨hV, hp.le, hV₀, h.normalizer_eq, normalizer_eq_of_inCalV D hV₀in, hTI₀, h1⟩

theorem s16c1_45_ne_bot
    {D : Data G} (h42 : R16_42 D) {V₀ V L : Subgroup G}
    {hV : IsElemAbelian 2 V} (hS : Sect16 D V₀ V L hV) (hc : Case167_1 D V₀ V hV L)
    (hV₀ : V₀ ≠ ⊥) {g : G} (h1 : InCalO1 1 D.M V₀ V g) :
    conjSubgroup V g ∈ calOStar 1 D.M V₀ V := by
  have hr : ((mSub V₀ + 1 : ℕ) : ℕ∞) < rMV D.M V := by
    have h4 : ((mSub V₀ + 4 : ℕ) : ℕ∞) ≤ rMV D.M V := (h42 V₀ V L hV hS hc).1
    have hlt : ((mSub V₀ + 1 : ℕ) : ℕ∞) < ((mSub V₀ + 4 : ℕ) : ℕ∞) :=
      WithTop.coe_lt_coe.2 (by omega)
    exact lt_of_lt_of_le hlt h4
  exact ⟨g, rfl, (s16c1_45_hyp65 hS hV₀ h1).inCalOStar_of_lt_rMV hr⟩

theorem r16_45_of
    (D : Data G) (h42 : R16_42 D) (h43 : R16_43_4 D) (h44 : R16_44 D) : R16_45 D := by
  intro V₀ V L hV hS hc
  apply Set.Subset.antisymm
  · intro X hX
    have hX1 := hX
    rw [h44 V₀ V L hV hS hc] at hX1
    obtain ⟨g', rfl, h1⟩ := hX1
    by_cases hV₀ : V₀ = ⊥
    · exact s16c1_45_bot h43 hS hc hV₀ h1.1
    · exact s16c1_45_ne_bot h42 hS hc hV₀ h1
  · rintro X ⟨g, rfl, hg⟩
    exact ⟨g, rfl, hg.1⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo

module

public import CFSG.LocalAnalysis.WeakClosure81.SixFour
public import CFSG.LocalAnalysis.WeakClosure81.SevenOne
public import CFSG.CGT.Timmesfeld75.Cfg214Gen
public import CFSG.CGT.Timmesfeld75.L2Real
public import CFSG.LargeExtraspecial.S9TIXC
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.InvolutionCountingOrderFormula
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.DefsSetting

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.UC22
open Subgroup
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

structure Hyp65 (n : ℕ) (M V₀ V : Subgroup G) (g : G) : Prop where
  elemAbelian : IsElemAbelian 2 V
  le : V₀ ≤ V
  ne_bot : V₀ ≠ ⊥
  normalizer_eq : normalizer (V : Set G) = M
  normalizer₀ : normalizer (V₀ : Set G) = M
  isTI : CFSG.CGT.Timmesfeld75.IsTI V₀
  inCalO1 : InCalO1 n M V₀ V g

@[expose] def Z0Of (M V₀ : Subgroup G) (g : G) : Subgroup G := V₀ ⊓ conjSubgroup M g

@[expose] def YOf (M V₀ : Subgroup G) (g : G) : Subgroup G := conjSubgroup V₀ g ⊓ M

@[expose] def L0Of (M V₀ : Subgroup G) (g : G) : Subgroup G := Z0Of M V₀ g ⊔ YOf M V₀ g

@[expose] def KOf (M V : Subgroup G) (g : G) : Subgroup G := UOf M V g ⊔ BOf M V g

@[expose] def COf (M V₀ V : Subgroup G) (g : G) : Subgroup G :=
  LOf V g ⊓ centralizer (L0Of M V₀ g : Set G)

theorem UOf_swap (M V : Subgroup G) (g : G) :
    UOf (conjSubgroup M g) (conjSubgroup V g) g⁻¹ = BOf M V g := by
  unfold UOf BOf
  rw [conjSubgroup_conjSubgroup_inv]

theorem BOf_swap (M V : Subgroup G) (g : G) :
    BOf (conjSubgroup M g) (conjSubgroup V g) g⁻¹ = UOf M V g := by
  unfold BOf UOf
  rw [conjSubgroup_conjSubgroup_inv]

theorem NOf_swap (M V : Subgroup G) (g : G) :
    NOf (conjSubgroup M g) (conjSubgroup V g) g⁻¹ = NOf M V g := by
  unfold NOf
  rw [UOf_swap, BOf_swap, inf_comm]

theorem LOf_swap (V : Subgroup G) (g : G) :
    LOf (conjSubgroup V g) g⁻¹ = LOf V g := by
  unfold LOf
  rw [conjSubgroup_conjSubgroup_inv, sup_comm]

theorem Z0Of_swap (M V₀ : Subgroup G) (g : G) :
    Z0Of (conjSubgroup M g) (conjSubgroup V₀ g) g⁻¹ = YOf M V₀ g := by
  unfold Z0Of YOf
  rw [conjSubgroup_conjSubgroup_inv]

theorem YOf_swap (M V₀ : Subgroup G) (g : G) :
    YOf (conjSubgroup M g) (conjSubgroup V₀ g) g⁻¹ = Z0Of M V₀ g := by
  unfold YOf Z0Of
  rw [conjSubgroup_conjSubgroup_inv]

theorem L0Of_swap (M V₀ : Subgroup G) (g : G) :
    L0Of (conjSubgroup M g) (conjSubgroup V₀ g) g⁻¹ = L0Of M V₀ g := by
  unfold L0Of
  rw [Z0Of_swap, YOf_swap, sup_comm]

theorem KOf_swap (M V : Subgroup G) (g : G) :
    KOf (conjSubgroup M g) (conjSubgroup V g) g⁻¹ = KOf M V g := by
  unfold KOf
  rw [UOf_swap, BOf_swap, sup_comm]

theorem COf_swap (M V₀ V : Subgroup G) (g : G) :
    COf (conjSubgroup M g) (conjSubgroup V₀ g) (conjSubgroup V g) g⁻¹ = COf M V₀ V g := by
  unfold COf
  rw [LOf_swap, L0Of_swap]

theorem inCalO1_swap {n : ℕ} {M V₀ V : Subgroup G} {g : G} (h : InCalO1 n M V₀ V g) :
    InCalO1 n (conjSubgroup M g) (conjSubgroup V₀ g) (conjSubgroup V g) g⁻¹ := by
  obtain ⟨⟨hF, hD⟩, hOF, hOD⟩ := h
  exact ⟨⟨(oFirst_swap n M V₀ V g).2 hD,
      by simpa only [ODual, OFirst, conjSubgroup_conjSubgroup_inv, ne_eq,
        conjSubgroup_eq_bot_iff] using hF⟩,
    (oneFirst_swap M V₀ V g).2 hOD,
    by simpa only [OneDual, OneFirst, conjSubgroup_conjSubgroup_inv] using hOF⟩

namespace Hyp65

variable {n : ℕ} {M V₀ V : Subgroup G} {g : G}

theorem le_M (h : Hyp65 n M V₀ V g) : V ≤ M := by
  rw [← h.normalizer_eq]
  exact Subgroup.le_normalizer

theorem conjV_le_conjM (h : Hyp65 n M V₀ V g) : conjSubgroup V g ≤ conjSubgroup M g := by
  exact conjSubgroup_mono h.le_M g

theorem not_conjV_le_M (h : Hyp65 n M V₀ V g) : ¬ conjSubgroup V g ≤ M := by
  exact h.inCalO1.1.1.1

theorem not_V_le_conjM (h : Hyp65 n M V₀ V g) : ¬ V ≤ conjSubgroup M g := by
  exact h.inCalO1.1.2.1

theorem mQuot_le (h : Hyp65 n M V₀ V g) : E3.mQuot V (conjSubgroup M g) ≤ n := by
  exact h.inCalO1.1.1.2.1

theorem swap (h : Hyp65 n M V₀ V g) :
    Hyp65 n (conjSubgroup M g) (conjSubgroup V₀ g) (conjSubgroup V g) g⁻¹ := by
  refine ⟨isElemAbelian_conjSubgroup' h.elemAbelian g, conjSubgroup_mono h.le g, ?_,
    ?_, ?_, isTI_conj h.isTI g, inCalO1_swap h.inCalO1⟩
  · rintro h0
    exact h.ne_bot (conjSubgroup_eq_bot_iff.1 h0)
  · rw [← conjSubgroup_normalizer V g, h.normalizer_eq]
  · rw [← conjSubgroup_normalizer V₀ g, h.normalizer₀]

end Hyp65

end CFSG.LocalAnalysis.WeakClosure81

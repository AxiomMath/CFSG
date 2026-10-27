module

public import CFSG.LocalAnalysis.WeakClosure81.FourteenSeven
public import CFSG.LocalAnalysis.WeakClosure81.SixFourSz

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.UC22
open Subgroup

variable {G : Type} [Group G] [Finite G]

theorem barSub_BOf_ne_bot_uncond {n : ℕ} {M V₀ V : Subgroup G} {g : G}
    (h : Hyp64 n M V₀ V g) :
    barSub V₀ V h.elemAbelian (BOf M V g) ≠ ⊥ :=
  barSub_BOf_ne_bot h (genHyp_of_hyp64 h)

theorem fourteen_nine_three_uncond {n : ℕ} {M V₀ V : Subgroup G} {g : G}
    (h : Hyp64 n M V₀ V g) :
    barSub V₀ V h.elemAbelian (BOf M V g) ∈
      calABar (mBar M V₀ V h.elemAbelian - n) M V₀ V h.elemAbelian :=
  fourteen_nine_three h (genHyp_of_hyp64 h)

theorem fourteen_eight_one_uncond {n : ℕ} {M V₀ V : Subgroup G} {g : G}
    (h : Hyp64 n M V₀ V g) (hirr : ConjGenerated M V₀ V) {Y : Subgroup G}
    (hY : IsRegularTorus M V g Y) {X : Subgroup (MulAut (Vtil V₀ V h.elemAbelian))}
    (hX1 : X ≠ ⊥) (hXM : X ≤ Mbar M V₀ V h.elemAbelian)
    (hXnorm : ∀ m ∈ Mbar M V₀ V h.elemAbelian, ∀ x ∈ X, m * x * m⁻¹ ∈ X)
    (hXB : ⁅X, barSub V₀ V h.elemAbelian (BOf M V g)⁆ = ⊥) :
    1 < E3.mQuot V (UOf M V g) ∧ (∀ a ∈ X, ∀ b ∈ X, a * b = b * a) ∧
      ∀ x ∈ X, x ^ (2 ^ E3.mQuot V (UOf M V g) - 1) = 1 :=
  fourteen_eight_one h (genHyp_of_hyp64 h) hirr hY hX1 hXM hXnorm hXB

end CFSG.LocalAnalysis.WeakClosure81

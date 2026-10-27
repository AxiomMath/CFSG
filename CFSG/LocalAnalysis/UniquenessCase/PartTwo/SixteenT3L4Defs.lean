module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven10Case2LnGap
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenDefs3

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

structure S16tL4Setting (D : Data G) (V₀ V L : Subgroup G) (hV : IsElemAbelian 2 V) : Prop where
  counterex : Counterex16 D V₀ V L hV
  shape : Case168_2Shape D V₀ V hV L (Shape168_2Ln V₀ V hV L 4)

structure S16tL4Pack (D : Data G) (V₀ V L : Subgroup G) (hV : IsElemAbelian 2 V) (Y : Subgroup G) :
    Prop where
  le : Y ≤ D.M
  normal : (Y.subgroupOf D.M).Normal
  perfect : ⁅Y, Y⁆ = Y
  bar_eq : barSub V₀ V hV Y = lBar V₀ V hV L
  ker_eq : Y ⊓ F11.CTilde D.M V₀ V = pCoreOf 2 Y

private theorem s16t_l4_sumOfNat_congr_v1 {V : Subgroup G} (hV : IsElemAbelian 2 V)
    (L : Subgroup G) {m : ℕ} {V₀ V₁ : Subgroup G} (h : V₁ = V₀)
    (hsum : SumOfNat (fun H U Z => BinaryNaturalSL H U Z m 1) (barSub V₁ V hV L)
      (⊤ : Subgroup (Vtil V₁ V hV)) ⊥ 2) :
    SumOfNat (fun H U Z => BinaryNaturalSL H U Z m 1) (barSub V₀ V hV L)
      (⊤ : Subgroup (Vtil V₀ V hV)) ⊥ 2 := by
  subst h
  exact hsum

theorem s16t_l4_setting_of_case168_2L4 {D : Data G} {V₀ V L : Subgroup G}
    {hV : IsElemAbelian 2 V} (hc : Counterex16 D V₀ V L hV) (h2 : Case168_2L4 D V₀ V hV L)
    (hV₀ : V₀ ≠ ⊥) : S16tL4Setting D V₀ V L hV := by
  obtain ⟨hK, ⟨L₀, hdir, hL₀, hL, hsum⟩, hσ⟩ := h2
  exact ⟨hc, hK, ⟨L₀, hdir, hL₀, hL,
    s16t_l4_sumOfNat_congr_v1 hV L (v1Sub_of_ne_bot D.M V₀ V hV L hV₀) hsum⟩, hσ⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo

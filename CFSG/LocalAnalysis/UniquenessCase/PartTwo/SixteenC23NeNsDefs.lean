module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC23NeY
public import CFSG.Quasithin.Background.FFC5Coh3

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Quasithin.FFC CFSG.Open Subgroup
  CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

structure C23NeNs (D : Data G) (V₀ V L : Subgroup G) (hV : IsElemAbelian 2 V) (x : G)
    (K₁ K₂ : Subgroup G) : Prop where
  ctx : C23NeCtx D V₀ V L hV x K₁ K₂
  pf : PairFacts D.M V₀ V
  nat : Nonempty (NatQuot3 (barSub V₀ V hV L) (wTil V₀ V hV L) ⊥)
  small : mSub V₀ ≤ 2
  Y_ne_bot : c23neY V K₁ K₂ ≠ ⊥
  Y_ne : c23neY V K₁ K₂ ≠ V₀
  nonsplit : ¬ C23NeSplit V₀ V (c23neY V K₁ K₂) (K₁ ⊔ K₂)

theorem C23NeNs.stab {D : Data G} {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V} {x : G}
    {K₁ K₂ : Subgroup G} (h : C23NeNs D V₀ V L hV x K₁ K₂) : D.M ≤ stabTil V₀ V :=
  le_stabTil h.pf.le_normalizer h.pf.le_normalizer₀

theorem C23NeNs.Y_le {D : Data G} {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V} {x : G}
    {K₁ K₂ : Subgroup G} (h : C23NeNs D V₀ V L hV x K₁ K₂) : c23neY V K₁ K₂ ≤ V₀ :=
  c23ne_Y_le_V₀ h.ctx h.pf.le_normalizer

theorem C23NeNs.Y_norm {D : Data G} {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V} {x : G}
    {K₁ K₂ : Subgroup G} (h : C23NeNs D V₀ V L hV x K₁ K₂) :
    D.M ≤ normalizer ((c23neY V K₁ K₂ : Subgroup G) : Set G) :=
  c23ne_Y_normal h.ctx h.pf.le_normalizer

theorem C23NeNs.stabY {D : Data G} {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V} {x : G}
    {K₁ K₂ : Subgroup G} (h : C23NeNs D V₀ V L hV x K₁ K₂) :
    D.M ≤ stabTil (c23neY V K₁ K₂) V :=
  le_stabTil h.pf.le_normalizer h.Y_norm

end CFSG.LocalAnalysis.UniquenessCase.PartTwo

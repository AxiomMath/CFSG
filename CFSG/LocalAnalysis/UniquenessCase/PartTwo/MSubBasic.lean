module

public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.GroupTheory.ElementaryAbelianTransport
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.DefsModule
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Open Subgroup

variable {G : Type} [Group G] [Finite G]

theorem one_le_mSub_of_ne_bot {V₀ : Subgroup G} (hV₀ : IsElemAbelian 2 V₀) (h : V₀ ≠ ⊥) :
    1 ≤ mSub V₀ := by
  have hP : IsPGroup 2 V₀ := CFSG.Open.IsElemAbelian.isPGroup hV₀
  haveI : Nontrivial ↥V₀ := (Subgroup.nontrivial_iff_ne_bot V₀).2 h
  have h2 : 1 < Nat.card ↥V₀ := Finite.one_lt_card_iff_nontrivial.2 inferInstance
  rw [card_eq_two_pow_mSub hP] at h2
  by_contra hlt
  have h0 : mSub V₀ = 0 := by omega
  rw [h0, pow_zero] at h2
  exact absurd h2 (by norm_num)

theorem ne_bot_of_one_lt_mSub {V₀ : Subgroup G} (h : 1 < mSub V₀) : V₀ ≠ ⊥ := by
  rintro rfl
  simp [mSub, CFSG.Quasithin.rk_bot] at h

end CFSG.LocalAnalysis.UniquenessCase.PartTwo

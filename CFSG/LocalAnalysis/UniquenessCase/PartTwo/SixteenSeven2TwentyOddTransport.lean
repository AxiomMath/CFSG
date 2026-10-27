module

public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.Adapters.RankTwoModelTransports
public import CFSG.Open.StatedDefs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Open

theorem s16c167_isometryCore_quadMinus_equiv {K : Type} [Field K] [Finite K] {b c : K} (n : ℕ)
    (hK : Nat.card K = 2) (hpoly : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    Nonempty (↥(CFSG.MatrixModel.isometryCore (StatedQuadMinus n K b c)) ≃*
      ↥(CFSG.MatrixModel.isometryCore (StatedQuadMinus n (ZMod 2) 1 1))) := by
  classical
  haveI : Fintype K := Fintype.ofFinite K
  have hK' : Fintype.card K = 2 := by rwa [← Nat.card_eq_fintype_card]
  let e : K ≃+* ZMod 2 := (ZMod.ringEquivOfPrime K Nat.prime_two hK').symm
  have hpoly' : ∀ t : ZMod 2, t ^ 2 + e b * t + e c ≠ 0 := by
    intro t h0
    apply hpoly (e.symm t)
    apply e.injective
    simpa using h0
  have hbc : e b = 1 ∧ e c = 1 := by
    have h0 := hpoly' 0
    have h1 := hpoly' 1
    generalize e b = x at h0 h1 ⊢
    generalize e c = y at h0 h1 ⊢
    revert x y
    decide
  obtain ⟨hb, hc⟩ := hbc
  have hmap := CFSG.ClassicalInvolution.Upgrade.map_closure_preserving e
    (CFSG.ClassicalInvolution.Upgrade.statedQuadMinus_comp (n := n) (b := b) (c := c) e hb hc)
  exact ⟨((CFSG.Adapters.RankTwoModelTransports.glCongr e).subgroupMap _).trans
    (MulEquiv.subgroupCongr hmap)⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
